(* Resource boundaries for the shared raise/assert reason encoder. *)
Theory reasonResourcesPtr
Ancestors
  representationCleanPtr bodyPtrDefs exprSimProps valueEncoding vfmConstants
  words list loweringPosts venomState

Theorem reason_string_head_clean:
  !cx ty str op G tn s tv w.
    ptr_mem_ok cx ty (StringV str) op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w ==>
    !i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv (StringV str) (w2n w) mem` by
    metis_tac[ptr_mem_ok_def] >>
  drule robust_val_in_memory_string_clean >> simp[]
QED

Theorem reason_string_source_covers:
  !cx ty str op G tn s n w.
    ptr_mem_ok cx ty (StringV str) op G tn s /\
    op_taint tn op = {} /\
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (StringT n)) /\
    eval_operand op s = SOME w ==>
    ?p. op = Var p /\
        ptr_covers G tn p s (32 + 32 * word_size (LENGTH str))
Proof
  rpt gen_tac >> strip_tac >>
  fs[ptr_mem_ok_def, val_footprint_def, val_store_size_def] >>
  gvs[] >> simp[ptr_covers_def] >>
  qexists_tac `w` >> gvs[eval_operand_def]
QED

(* The rounded copy always reads the head, including for an empty reason. *)
Theorem reason_string_copy_boundary_tests:
  MAP (\n. 32 + 32 * word_size n) [0;31;32;33] = [32;64;64;96]
Proof
  EVAL_TAC
QED
