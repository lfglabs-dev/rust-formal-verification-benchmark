"""Minimal OpenAI-compatible chat-completions transport with retries."""
from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass


@dataclass
class ChatConfig:
    base_url: str
    model: str
    api_key: str | None = None
    temperature: float | None = 0.0
    max_tokens: int = 16384
    timeout: int = 600
    retries: int = 6
    backoff: float = 5.0
    extra_body: dict | None = None


class TransportError(RuntimeError):
    pass


def chat(cfg: ChatConfig, messages: list[dict], tools: list[dict] | None = None) -> dict:
    body = {"model": cfg.model, "messages": messages, "max_tokens": cfg.max_tokens}
    if cfg.temperature is not None:
        body["temperature"] = cfg.temperature
    if tools:
        body["tools"] = tools
        body["tool_choice"] = "auto"
    if cfg.extra_body:
        body.update(cfg.extra_body)
    data = json.dumps(body).encode("utf-8")
    headers = {"Content-Type": "application/json", "User-Agent": "rfvb/1.0"}
    if cfg.api_key:
        headers["Authorization"] = f"Bearer {cfg.api_key}"
    url = cfg.base_url.rstrip("/") + "/chat/completions"
    last = None
    for attempt in range(cfg.retries + 1):
        req = urllib.request.Request(url, data=data, headers=headers, method="POST")
        try:
            with urllib.request.urlopen(req, timeout=cfg.timeout) as resp:
                return json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", "replace")[:2000]
            last = f"HTTP {exc.code}: {detail}"
            overflow = any(k in detail.lower() for k in ("context", "maximum", "too long", "too many tokens"))
            if exc.code in (401, 403, 404, 422) or (exc.code == 400 and overflow):
                # context overflow / bad request: not retryable
                raise TransportError(last) from exc
            # other 400s seen from gateways (e.g. an empty upstream reply that the
            # proxy fails to parse) are transient: retry them like 5xx
        except (urllib.error.URLError, TimeoutError, ConnectionError, json.JSONDecodeError) as exc:
            last = f"{type(exc).__name__}: {exc}"
        time.sleep(cfg.backoff * (2 ** attempt))
    raise TransportError(f"request failed after {cfg.retries + 1} attempts: {last}")
