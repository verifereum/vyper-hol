(*
 * Value Range Lattice — Definitions
 *
 * Ports vyper/venom/analysis/variable_range/value_range.py to HOL4.
 * Upstream: vyperlang/vyper@8092fe67f (algebraic representation for range analysis)
 *
 * Interval lattice over signed 256-bit integer bounds.
 * Python uses (lo, hi) with None→TOP and lo>hi→BOTTOM;
 * HOL4 uses explicit constructors for clarity.
 *
 * TOP-LEVEL:
 *   value_range            — interval type: VR_Top | VR_Bottom | VR_Range lo hi
 *   vr_lo, vr_hi           — bound accessors (TOP → INT_MIN/UINT_MAX)
 *   vr_leq                 — lattice order (⊆ of intervals)
 *   vr_union               — join (smallest containing interval)
 *   vr_intersect            — meet (largest contained interval)
 *   vr_clamp               — clamp bounds
 *   vr_widen               — widening operator for convergence
 *   vr_constant, vr_bool_range, vr_bytes_range — constructors
 *   in_range               — soundness predicate: word value in interval
 *
 * Helper:
 *   INT256_MIN, INT256_MAX, UINT256_MAX — 256-bit integer constants
 *)

Theory valueRangeDefs
Ancestors
  integer_word latticeDefs

(* ===== 256-bit Integer Constants ===== *)

(* These match Python's SizeLimits.MIN_INT256 / MAX_INT256 / MAX_UINT256 *)
Definition INT256_MIN_def:
  INT256_MIN : int = INT_MIN (:256)
End

Definition INT256_MAX_def:
  INT256_MAX : int = INT_MAX (:256)
End

Definition UINT256_MAX_def:
  UINT256_MAX_int : int = UINT_MAX (:256)
End

(* Precision threshold: ranges wider than 2^128 are widened to TOP.
   Matches Python RANGE_WIDTH_LIMIT = 1 << 128. *)
Definition RANGE_WIDTH_LIMIT_def:
  RANGE_WIDTH_LIMIT : int = &(2 ** 128)
End

(* ===== Value Range Datatype ===== *)

Datatype:
  value_range =
    VR_Top                      (* unknown — any value *)
  | VR_Bottom                   (* unreachable / empty *)
  | VR_Range int int            (* [lo, hi] inclusive, lo ≤ hi *)
End

(* ===== Bound Accessors ===== *)

(* Matches Python ValueRange.lo / .hi properties *)
Definition vr_lo_def:
  vr_lo VR_Top = INT256_MIN ∧
  vr_lo VR_Bottom = 1 ∧
  vr_lo (VR_Range lo hi) = lo
End

Definition vr_hi_def:
  vr_hi VR_Top = UINT256_MAX_int ∧
  vr_hi VR_Bottom = 0 ∧
  vr_hi (VR_Range lo hi) = hi
End

(* ===== Predicates ===== *)

Definition vr_is_top_def:
  vr_is_top VR_Top = T ∧
  vr_is_top _ = F
End

Definition vr_is_bottom_def:
  vr_is_bottom VR_Bottom = T ∧
  vr_is_bottom _ = F
End

Definition vr_is_constant_def:
  vr_is_constant (VR_Range lo hi) = (lo = hi) ∧
  vr_is_constant _ = F
End

(* ===== Constructors ===== *)

Definition vr_constant_def:
  vr_constant (v : int) = VR_Range v v
End

Definition vr_bool_range_def:
  vr_bool_range = VR_Range 0 1
End

(* bytes_range n = [0, 256^n - 1] = [0, 2^(8*n) - 1] *)
Definition vr_bytes_range_def:
  vr_bytes_range (n : num) = VR_Range 0 (&(2 ** (8 * n)) - 1)
End

(* ===== Lattice Operations ===== *)

(* Join: smallest interval containing both.
   Matches Python ValueRange.union. *)
Definition vr_union_def:
  vr_union VR_Bottom x = x ∧
  vr_union x VR_Bottom = x ∧
  vr_union VR_Top _ = VR_Top ∧
  vr_union _ VR_Top = VR_Top ∧
  vr_union (VR_Range lo1 hi1) (VR_Range lo2 hi2) =
    VR_Range (int_min lo1 lo2) (int_max hi1 hi2)
End

(* Meet: largest interval contained in both.
   Matches Python ValueRange.intersect. *)
Definition vr_intersect_def:
  vr_intersect VR_Top x = x ∧
  vr_intersect x VR_Top = x ∧
  vr_intersect VR_Bottom _ = VR_Bottom ∧
  vr_intersect _ VR_Bottom = VR_Bottom ∧
  vr_intersect (VR_Range lo1 hi1) (VR_Range lo2 hi2) =
    let lo = int_max lo1 lo2 in
    let hi = int_min hi1 hi2 in
    if lo > hi then VR_Bottom else VR_Range lo hi
End

(* Clamp to [lo_bound, hi_bound].
   Matches Python ValueRange.clamp. *)
Definition vr_clamp_def:
  vr_clamp VR_Bottom lo_opt hi_opt = VR_Bottom ∧
  vr_clamp VR_Top lo_opt hi_opt =
    (let lo = case lo_opt of NONE => INT256_MIN | SOME l => int_max INT256_MIN l in
     let hi = case hi_opt of NONE => UINT256_MAX_int | SOME h => int_min UINT256_MAX_int h in
     if lo > hi then VR_Bottom else VR_Range lo hi) ∧
  vr_clamp (VR_Range lo hi) lo_opt hi_opt =
    (let lo' = case lo_opt of NONE => lo | SOME l => int_max lo l in
     let hi' = case hi_opt of NONE => hi | SOME h => int_min hi h in
     if lo' > hi' then VR_Bottom else VR_Range lo' hi')
End

(* ===== Lattice Order ===== *)

(* Containment order: a ≤ b iff a's interval ⊆ b's interval.
   BOTTOM ≤ everything, everything ≤ TOP. *)
Definition vr_leq_def:
  vr_leq VR_Bottom _ = T ∧
  vr_leq _ VR_Top = T ∧
  vr_leq VR_Top VR_Bottom = F ∧
  vr_leq VR_Top (VR_Range _ _) = F ∧
  vr_leq (VR_Range _ _) VR_Bottom = F ∧
  vr_leq (VR_Range lo1 hi1) (VR_Range lo2 hi2) = (lo2 ≤ lo1 ∧ hi1 ≤ hi2)
End

(* ===== Widening ===== *)

(* Widening: if bounds grow, jump to TOP.
   Matches Python VariableRangeAnalysis._widen_range.
   Note: Python jumps straight to TOP (no thresholds). *)
Definition vr_widen_def:
  vr_widen old new =
    case (old, new) of
      (_, VR_Top) => VR_Top
    | (VR_Top, _) => VR_Top
    | (VR_Bottom, _) => new
    | (_, VR_Bottom) => old
    | (VR_Range lo1 hi1, VR_Range lo2 hi2) =>
        if lo2 < lo1 ∨ hi2 > hi1 then VR_Top
        else old
End

(* ===== Soundness Predicate ===== *)

(* A word value w is in the range r if r is TOP, or
   the signed interpretation w2i(w) falls within [lo, hi].
   BOTTOM contains nothing. *)
Definition in_range_def:
  in_range VR_Top (w : 256 word) = T ∧
  in_range VR_Bottom w = F ∧
  in_range (VR_Range lo hi) w = (lo ≤ w2i w ∧ w2i w ≤ hi)
End

(* ===== Check if range spans signed/unsigned boundary ===== *)

(* Python _range_spans_sign_boundary: lo < 0 and hi >= 0.
   Important for unsigned comparison soundness. *)
Definition vr_spans_sign_boundary_def:
  vr_spans_sign_boundary VR_Top = T ∧
  vr_spans_sign_boundary VR_Bottom = F ∧
  vr_spans_sign_boundary (VR_Range lo hi) = (lo < 0 ∧ hi ≥ 0)
End
