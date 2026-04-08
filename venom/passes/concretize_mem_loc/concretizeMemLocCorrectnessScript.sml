(*
 * Concretize Memory Locations — Correctness Statement
 *
 * Two properties:
 * 1. compute_alloc_map produces non-overlapping regions for
 *    simultaneously live allocations.
 * 2. Given a sound allocation map, concretize_function preserves
 *    semantics under a memory remapping relation.
 *)

Theory concretizeMemLocCorrectness
Ancestors
  concretizeMemLocProofs venomExecSemantics

Theorem concretize_function_correct:
  !amap fn fuel ctx s1 s2.
    venom_wf ctx /\ ssa_form fn /\
    concretize_pointer_confined fn amap /\
    mem_remap_equiv amap fn s1 s2 ==>
    lift_result
      (mem_remap_equiv amap fn)
      (mem_remap_equiv amap fn)
      (mem_remap_equiv amap fn)
      (run_blocks fuel ctx fn s1)
      (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  ACCEPT_TAC concretize_function_correct_proof
QED

(* ===== Obligations ===== *)

Theorem concretize_preserves_ssa_form:
  ∀amap fn. ssa_form fn ⇒ ssa_form (concretize_function amap fn)
Proof
  cheat
QED

Theorem concretize_preserves_wf_function:
  ∀amap fn. wf_function fn ⇒ wf_function (concretize_function amap fn)
Proof
  cheat
QED
