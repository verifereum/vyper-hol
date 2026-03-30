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
  concretizeMemLocProofs

Theorem concretize_function_correct:
  !amap fn fuel ctx s1 s2.
    venom_wf ctx /\ ssa_form fn /\
    pointer_confined fn amap /\
    mem_remap_equiv amap fn s1 s2 ==>
    lift_result
      (mem_remap_equiv amap fn)
      (mem_remap_equiv amap fn)
      (run_function fuel ctx fn s1)
      (run_function fuel ctx (concretize_function amap fn) s2)
Proof
  ACCEPT_TAC concretize_function_correct_proof
QED

(* pointer_confined is strictly stronger than alloca_safe_fn:
 * pointer-derived vars can only appear in memory ops or ADD,
 * which excludes all observable operand positions.
 * Precondition: amap covers all alloca outputs in fn. *)
Theorem pointer_confined_implies_alloca_safe:
  ∀fn amap.
    pointer_confined fn amap ∧
    (∀inst. MEM inst (fn_insts fn) ∧ inst.inst_opcode = ALLOCA ⇒
       ∀out. inst_output inst = SOME out ⇒ out ∈ FDOM amap) ⇒
    alloca_safe_fn fn
Proof
  ACCEPT_TAC pointer_confined_implies_alloca_safe
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
