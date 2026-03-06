(*
 * Range Evaluators — Proofs
 *
 * Soundness: each per-opcode evaluator over-approximates the
 * concrete result for all values within the input ranges.
 *
 * Pattern: for each eval_range_X, prove
 *   in_range r1 w1 ∧ in_range r2 w2 ⇒
 *   in_range (eval_range_X r1 r2) (concrete_op w1 w2)
 *)

Theory rangeEvalProofs
Ancestors
  valueRangeDefs rangeEvalDefs valueRangeProofs
Libs
  integerTheory integer_wordTheory

(* ===== ASSIGN soundness ===== *)

Theorem eval_range_assign_sound:
  ∀r w. in_range r w ⇒ in_range (eval_range_assign r) w
Proof
  rw[eval_range_assign_def]
QED

(* ===== ISZERO soundness ===== *)

Theorem eval_range_iszero_sound:
  ∀r w.
    in_range r w ⇒
    in_range (eval_range_iszero r)
             (if w = 0w then 1w else 0w)
Proof
  cheat
QED

(* ===== ADD soundness ===== *)

(* Full ADD soundness requires reasoning about integer overflow and
   word arithmetic. Cheated for now — complex signed/unsigned interaction. *)
Theorem eval_range_add_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_add r1 r2) (w1 + w2)
Proof
  cheat
QED

(* ===== SUB soundness ===== *)

Theorem eval_range_sub_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_sub r1 r2) (w1 - w2)
Proof
  cheat
QED

(* ===== MUL soundness ===== *)

Theorem eval_range_mul_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_mul r1 r2) (w1 * w2)
Proof
  cheat
QED

(* ===== Comparison soundness ===== *)

Theorem eval_range_compare_sound:
  ∀op r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ∧
    (op = LT ∨ op = GT ∨ op = SLT ∨ op = SGT) ⇒
    in_range (eval_range_compare op r1 r2)
             (case op of
                LT => if w2n w1 < w2n w2 then 1w else 0w
              | GT => if w2n w1 > w2n w2 then 1w else 0w
              | SLT => if w2i w1 < w2i w2 then 1w else 0w
              | SGT => if w2i w1 > w2i w2 then 1w else 0w
              | _ => ARB)
Proof
  cheat
QED

(* ===== EQ soundness ===== *)

Theorem eval_range_eq_sound:
  ∀r1 r2 w1 w2.
    in_range r1 w1 ∧ in_range r2 w2 ⇒
    in_range (eval_range_eq r1 r2)
             (if w1 = w2 then 1w else 0w)
Proof
  cheat
QED

(* ===== Top-level dispatch soundness ===== *)
(* This would compose the per-opcode results via eval_range dispatch.
   Deferred until per-opcode proofs are solid. *)
