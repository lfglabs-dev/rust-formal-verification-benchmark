import Benchmark.Cases.Etherparse.Net.Specs

open CoreModels Aeneas Aeneas.Std.WP
open Aeneas.Std hiding namespace core alloc
open RustM
open etherparse

namespace Benchmark.Cases.Etherparse.Net

set_option linter.unusedSimpArgs false

theorem ipv4_payload_len (header : net.ipv4_header.Ipv4Header)
    (h_dscp : header.dscp.val ≤ 63)
    (h_frag : header.fragment_offset.val < 2^13)
    (h_options_len : header.options.len.val ≤ 36 ∧ header.options.len.val % 4 = 0)
    (h_total_lo : 20 + header.options.len.val ≤ header.total_len.val)
    (h_total_hi : header.total_len.val < 2^16 - 1) :
    ipv4_payload_len_spec header := by
  have _ := h_dscp
  have _ := h_frag
  have _ := h_options_len.2
  have _ := h_total_hi
  unfold ipv4_payload_len_spec
    net.ipv4_header.Ipv4Header.payload_len
    net.ipv4_header.Ipv4Header.header_len
    net.ipv4_options.Ipv4Options.impl.len
  simp only [net.ipv4_header.Ipv4Header.MIN_LEN,
    core.convert.Into.Blanket.into,
    core.Usize.Insts.CoreConvertFromU8.from,
    core.Usize.Insts.CoreConvertFromU16.from,
    bind_tc_ok, lift]
  have holen : header.options.len.val ≤ 36 := h_options_len.1
  constructor
  · step as ⟨x, hx⟩
    have hx' : x.val = 20 + header.options.len.val := by
      rw [hx, U8.cast_Usize_val_eq]
    have hx16 : (UScalar.cast .U16 x).val = x.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      simp only [UScalarTy.numBits, hx']
      omega
    have hle : UScalar.cast .U16 x ≤ header.total_len := by
      rw [UScalar.le_equiv, hx16, hx']
      exact h_total_lo
    simp only [hle, ↓reduceIte]
    step*
    · congr 1
      apply UScalar.val_eq_imp
      have hc : (UScalar.cast .U16 (UScalar.cast .Usize header.options.len)).val =
          header.options.len.val := by
        rw [UScalar.cast_val_mod_pow_of_inBounds_eq
          (x := UScalar.cast .Usize header.options.len) (tgt_ty := .U16) (by
            rw [U8.cast_Usize_val_eq]
            simp only [UScalarTy.numBits]
            omega)]
        exact U8.cast_Usize_val_eq _
      rw [x_post1, b_post1, a_post1, hx16, hx', hc]
      omega
  · step as ⟨hl, hhl⟩
    intro bad hbad
    step as ⟨x, hx⟩
    have hx' : x.val = 20 + header.options.len.val := by
      rw [hx, U8.cast_Usize_val_eq]
    have hhl' : hl.val = 20 + header.options.len.val := by
      rw [hhl, U8.cast_Usize_val_eq]
    have hx16 : (UScalar.cast .U16 x).val = x.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      simp only [UScalarTy.numBits, hx']
      omega
    have hhl16 : (UScalar.cast .U16 hl).val = hl.val := by
      apply UScalar.cast_val_mod_pow_of_inBounds_eq
      simp only [UScalarTy.numBits, hhl']
      omega
    have hlt : ¬ UScalar.cast .U16 x ≤ bad := by
      rw [UScalar.le_equiv, hx16, hx', ← hhl', ← hhl16]
      omega
    simp only [hlt, ↓reduceIte]
    step*
    have hreq : UScalar.cast .Usize (UScalar.cast .U16 x) = req := by
      apply UScalar.val_eq_imp
      rw [U16.cast_Usize_val_eq, hx16, hx', req_post, U8.cast_Usize_val_eq]
    simp [hreq]

end Benchmark.Cases.Etherparse.Net
