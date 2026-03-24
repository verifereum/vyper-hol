(*
 * Base Pointer Analysis — Properties
 *
 * Frame and lookup properties for the transfer function.
 *
 * TOP-LEVEL:
 *   bp_get_ptrs_update_same, bp_get_ptrs_update_diff, bp_get_ptrs_fempty,
 *   bp_handle_inst_other_var, bp_handle_inst_no_output_unchanged
 *)

Theory basePtrProps
Ancestors
  basePtrDefs basePtrProofs
Libs
  finite_mapTheory

(* ===== bp_get_ptrs lookup lemmas ===== *)

Theorem bp_get_ptrs_update_same:
  ∀result k v. bp_get_ptrs (result |+ (k, v)) k = v
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_update_diff:
  ∀result k1 k2 v. k1 ≠ k2 ⇒
    bp_get_ptrs (result |+ (k1, v)) k2 = bp_get_ptrs result k2
Proof
  rw[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Theorem bp_get_ptrs_fempty:
  ∀v. bp_get_ptrs FEMPTY v = {}
Proof
  rw[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* ===== bp_handle_inst frame ===== *)

(* Transfer function only modifies the output variable's pointer set.
 * Needed for any analysis that reasons about variables not defined by inst. *)
Theorem bp_handle_inst_other_var:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_other_var_proof
QED

(* No-output instructions don't modify the pointer map at all. *)
Theorem bp_handle_inst_no_output_unchanged:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  ACCEPT_TAC basePtrProofsTheory.bp_handle_inst_no_output_unchanged_proof
QED

