(* Dynamic concat sources include their header and payload below the frontier. *)
Theory bodyMemBiConcatBounds
Ancestors
  exprSimMemDefs valueCopyBytes valueTypingMemoryProps bodyMemAggregateBounds

Theorem concat_bytestring_source_bound_mem:
  expr_store_bound cx ty v op t /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_operand op t = SOME sw ==>
  w2n sw + 32 + LENGTH (case v of BytesV bs => bs
    | StringV str => MAP (n2w o ORD) str | _ => []) <= t.vs_alloca_next
Proof
  strip_tac >>
  `~is_word_type ty` by metis_tac[is_bytestring_word_type] >>
  drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, expr_store_bound_def,
      exprSimPropsTheory.val_store_size_def] >>
  qmatch_goalsub_rename_tac `LENGTH payload` >>
  qspec_then `LENGTH payload` mp_tac word_size_capacity >> decide_tac
QED
