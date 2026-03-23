(*
 * Base Pointer Analysis — Proofs
 *
 * TOP-LEVEL:
 *   bp_handle_inst_other_var_proof       — transfer function frame property
 *   bp_handle_inst_no_output_unchanged_proof — no-output identity
 *)

Theory basePtrProofs
Ancestors
  basePtrDefs
Libs
  finite_mapTheory

(* Transfer function only modifies the output variable's pointer set. *)
Theorem bp_handle_inst_other_var_proof:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[LET_THM] >>
  rename1 `SOME out` >>
  Cases_on `inst.inst_opcode` >> gvs[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

(* No-output instructions don't modify the pointer map at all. *)
Theorem bp_handle_inst_no_output_unchanged_proof:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[]
QED
