"""Unprivileged sandbox for Lean/Lake processes that elaborate untrusted files.

Submitted proofs can run arbitrary code at elaboration time (tactic
metaprograms, `#eval`-like commands that slip past the static policy), so every
Lean process that sees a candidate proof is started through

    python -m rfvb.sandbox --write DIR [--write DIR ...] -- CMD ARGS...

which applies a Linux Landlock ruleset to itself and then `exec`s CMD:

* file-system writes (create, delete, truncate, write, rename) are allowed only
  beneath the given directories (plus `/dev`, for `/dev/null`); reads are not
  restricted, so the toolchain and the shared Lake packages stay usable but
  cannot be modified;
* TCP bind/connect is denied (Landlock ABI >= 4);
* the environment is reduced to what Lean needs (no API keys).

Landlock needs no privileges (Linux >= 5.13; network rules >= 6.7). Without it
the wrapper refuses to run unless RFVB_ALLOW_UNSANDBOXED=1 is set, in which
case it only scrubs the environment and says so on stderr.
"""
from __future__ import annotations

import ctypes
import os
import sys
from pathlib import Path

SYS_LANDLOCK_CREATE_RULESET = 444
SYS_LANDLOCK_ADD_RULE = 445
SYS_LANDLOCK_RESTRICT_SELF = 446
LANDLOCK_CREATE_RULESET_VERSION = 1
LANDLOCK_RULE_PATH_BENEATH = 1
PR_SET_NO_NEW_PRIVS = 38

# Write-type file-system rights (ABI 1), plus REFER (ABI 2) and TRUNCATE (ABI 3).
FS_WRITE_FILE = 1 << 1
FS_REMOVE_DIR = 1 << 4
FS_REMOVE_FILE = 1 << 5
FS_MAKE_CHAR = 1 << 6
FS_MAKE_DIR = 1 << 7
FS_MAKE_REG = 1 << 8
FS_MAKE_SOCK = 1 << 9
FS_MAKE_FIFO = 1 << 10
FS_MAKE_BLOCK = 1 << 11
FS_MAKE_SYM = 1 << 12
FS_REFER = 1 << 13
FS_TRUNCATE = 1 << 14
NET_BIND_TCP = 1 << 0
NET_CONNECT_TCP = 1 << 1

ENV_KEEP = ("PATH", "HOME", "LANG", "LC_ALL", "TERM", "TMPDIR", "ELAN_HOME", "ELAN_TOOLCHAIN",
            "LEAN_PATH", "LEAN_SRC_PATH", "LAKE_HOME", "LEAN_NUM_THREADS")


class RulesetAttr(ctypes.Structure):
    _fields_ = [("handled_access_fs", ctypes.c_uint64), ("handled_access_net", ctypes.c_uint64)]


class PathBeneathAttr(ctypes.Structure):
    _pack_ = 1
    _fields_ = [("allowed_access", ctypes.c_uint64), ("parent_fd", ctypes.c_int32)]


def landlock_abi() -> int:
    libc = ctypes.CDLL(None, use_errno=True)
    abi = libc.syscall(SYS_LANDLOCK_CREATE_RULESET, None, ctypes.c_size_t(0),
                       ctypes.c_uint32(LANDLOCK_CREATE_RULESET_VERSION))
    return abi if abi > 0 else 0


def fs_write_rights(abi: int) -> int:
    rights = (FS_WRITE_FILE | FS_REMOVE_DIR | FS_REMOVE_FILE | FS_MAKE_CHAR | FS_MAKE_DIR | FS_MAKE_REG
              | FS_MAKE_SOCK | FS_MAKE_FIFO | FS_MAKE_BLOCK | FS_MAKE_SYM)
    if abi >= 2:
        rights |= FS_REFER
    if abi >= 3:
        rights |= FS_TRUNCATE
    return rights


def restrict_self(writable: list[Path]) -> int:
    """Apply the ruleset to the current process; returns the Landlock ABI used."""
    abi = landlock_abi()
    if abi == 0:
        raise OSError("Landlock is not available on this kernel")
    libc = ctypes.CDLL(None, use_errno=True)
    fs = fs_write_rights(abi)
    net = (NET_BIND_TCP | NET_CONNECT_TCP) if abi >= 4 else 0
    attr = RulesetAttr(fs, net)
    size = ctypes.sizeof(RulesetAttr) if abi >= 4 else ctypes.sizeof(ctypes.c_uint64)
    ruleset = libc.syscall(SYS_LANDLOCK_CREATE_RULESET, ctypes.byref(attr), ctypes.c_size_t(size), ctypes.c_uint32(0))
    if ruleset < 0:
        raise OSError(ctypes.get_errno(), "landlock_create_ruleset failed")
    try:
        for path in [*writable, Path("/dev")]:
            fd = os.open(path, os.O_PATH | os.O_CLOEXEC)
            try:
                rule = PathBeneathAttr(fs, fd)
                if libc.syscall(SYS_LANDLOCK_ADD_RULE, ruleset, LANDLOCK_RULE_PATH_BENEATH, ctypes.byref(rule),
                                ctypes.c_uint32(0)) != 0:
                    raise OSError(ctypes.get_errno(), f"landlock_add_rule failed for {path}")
            finally:
                os.close(fd)
        if libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "prctl(PR_SET_NO_NEW_PRIVS) failed")
        if libc.syscall(SYS_LANDLOCK_RESTRICT_SELF, ruleset, ctypes.c_uint32(0)) != 0:
            raise OSError(ctypes.get_errno(), "landlock_restrict_self failed")
    finally:
        os.close(ruleset)
    return abi


def wrap(cmd: list[str], writable: list[Path]) -> list[str]:
    """Command line running `cmd` inside the sandbox."""
    args = [sys.executable, "-I", str(Path(__file__).resolve())]
    for w in writable:
        args += ["--write", str(Path(w).resolve())]
    return [*args, "--", *cmd]


def clean_env() -> dict[str, str]:
    return {k: v for k, v in os.environ.items() if k in ENV_KEEP}


def main(argv: list[str]) -> int:
    writable: list[Path] = []
    i = 0
    while i < len(argv) and argv[i] != "--":
        if argv[i] == "--write" and i + 1 < len(argv):
            writable.append(Path(argv[i + 1]))
            i += 2
        else:
            print(f"rfvb.sandbox: unexpected argument {argv[i]!r}", file=sys.stderr)
            return 2
    cmd = argv[i + 1:]
    if not cmd or not writable:
        print("usage: python -m rfvb.sandbox --write DIR [--write DIR ...] -- CMD ARGS...", file=sys.stderr)
        return 2
    try:
        restrict_self(writable)
    except OSError as exc:
        if os.environ.get("RFVB_ALLOW_UNSANDBOXED") != "1":
            print(f"rfvb.sandbox: cannot sandbox ({exc}); refusing to run untrusted Lean code. "
                  "Set RFVB_ALLOW_UNSANDBOXED=1 to override.", file=sys.stderr)
            return 126
        print(f"rfvb.sandbox: WARNING running unsandboxed ({exc})", file=sys.stderr)
    env = clean_env()
    try:
        os.execvpe(cmd[0], cmd, env)
    except OSError as exc:
        print(f"rfvb.sandbox: cannot execute {cmd[0]}: {exc}", file=sys.stderr)
        return 127


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
