(*
 * Memmerging — Interval Arithmetic
 *
 * Ports the _Interval dataclass from memmerging.py.
 * Pure math on integer intervals [start, start + length).
 *
 * TOP-LEVEL:
 *   mm_interval         — record type
 *   interval_end        — start + length
 *   interval_overlaps   — two intervals share a point
 *)

Theory mmInterval

(* ===== Interval type ===== *)

(* Half-open interval [start, start + length).
   Uses num (natural numbers) since all memory addresses are non-negative.
   Python: _Interval(start, length) *)
Datatype:
  mm_interval = <| iv_start : num; iv_length : num |>
End

(* Right endpoint (exclusive).
   Python: _Interval.end *)
Definition interval_end_def:
  interval_end iv = iv.iv_start + iv.iv_length
End

(* Two intervals overlap iff their intersection is non-empty.
   Python: _Interval.overlaps *)
Definition interval_overlaps_def:
  interval_overlaps iv1 iv2 <=>
    MAX iv1.iv_start iv2.iv_start < MIN (interval_end iv1) (interval_end iv2)
End

(* Convenience: make an interval *)
Definition mk_interval_def:
  mk_interval start length = <| iv_start := start; iv_length := length |>
End
