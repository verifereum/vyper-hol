(*
 * Assert Elimination — Definitions
 *
 * Ports vyper/venom/passes/assert_elimination.py to HOL4.
 * Upstream: vyperlang/vyper@8b4f0a225 (add assert elimination pass)
 *
 * Eliminates ASSERT instructions whose operand is provably nonzero
 * according to the variable range analysis (widening).
 *
 * Framework: analysis_inst_simulates + df_analysis_pass_correct_widen_sound.
 * Soundness: in_range_state (from rangeEvalDefs).
 *
 * TOP-LEVEL:
 *   range_excludes_zero       — predicate: range provably excludes zero
 *   assert_elim_inst          — per-instruction transform
 *   assert_elim_function      — function-level transform
 *)

Theory assertElimDefs
Ancestors
  analysisSimDefs rangeAnalysisDefs valueRangeDefs rangeEvalDefs
  passSharedDefs

(* ===== Range predicate ===== *)

(* Matches Python _range_excludes_zero:
     rng.lo > 0 or rng.hi < 0
   Empty ranges return F (conservative). *)
(* Guard: lo ≤ hi ensures the range is non-empty.
   A pathological VR_Range 5 3 (lo > hi) is treated as empty
   (like VR_Bottom) — conservative. Matches Python's
   `if rng.is_empty: return False` check before the lo/hi test. *)
Definition range_excludes_zero_def:
  range_excludes_zero VR_Top = F /\
  range_excludes_zero VR_Bottom = F /\
  range_excludes_zero (VR_Range lo hi) = (lo <= hi /\ (lo > 0 \/ hi < 0))
End

(* ===== Per-instruction transform ===== *)

(* Transform given pre-instruction range state.
   ASSERT with range excluding zero → NOP.
   Signature: ('a -> instruction -> instruction) for analysis_inst_simulates. *)
Definition assert_elim_inst_def:
  assert_elim_inst (rs_opt : (string, value_range) fmap option) inst =
    if inst.inst_opcode <> ASSERT then inst
    else case rs_opt of
      NONE => inst  (* bottom = unreachable, keep as-is *)
    | SOME rs =>
        (case inst.inst_operands of
           [Var v] =>
             if range_excludes_zero (rs_lookup rs v)
             then mk_nop_inst inst
             else inst
         | [Lit w] =>
             if w <> 0w then mk_nop_inst inst else inst
         | _ => inst)
End

(* ===== Function-level transform ===== *)

Definition assert_elim_function_def:
  assert_elim_function fn =
    let ra = range_analyze fn in
    clear_nops_function
      (analysis_function_transform_widen NONE ra
        (\v inst. [assert_elim_inst v inst]) fn)
End
