(* The word Append needs no scratch stage: its direct store is the
   word specialization of the common memory suffix. *)
Theory bodyAppendMemoryWordInputMods
Ancestors
  bodySimStmtFacts bodyPtrDefs context compileEnv exprLowering exprWordOperand
  exprSimSource exprSimPrecompiles exprBodyPreProps entryDecodeStaticProps
  typedMemoryCopy valueEncodingTyping vyperTypeEvalCaseProofs
  vyperTypeExprSoundness vyperTypeSystem exprSimHypsDefs

Theorem append_memory_word_uses_store[local]:
  is_word_type elem ==>
  compile_dynarray_append cenv bop op 32 stride elem sty cap T LocMemory =
  compile_dynarray_append cenv bop op 32 stride elem elem cap F LocMemory
Proof
  strip_tac >> rw[FUN_EQ_THM, compile_dynarray_append_def, LET_THM,
    contextTheory.compile_ptr_store_def, contextTheory.compile_store_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem append_memory_word_input_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,fin) /\
  expr_post H ctx func cenv cx e mid sp sm s fin v op u /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
  is_word_type elem /\ type_widens_to env.type_defs (expr_type e) elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\
  compile_dynarray_append cenv (Var p) op (word_scale LocMemory)
    (elem_size_in_location cenv LocMemory elem) elem (lowered_value_type cenv e)
    cap T LocMemory sm = ((),sf) ==>
  compile_dynarray_append cenv (Var p) op 32 (type_memory_size tv)
    elem elem cap F LocMemory sm = ((),sf) /\
  type_memory_size tv = 32 /\ value_has_type tv v /\ val_wf tv v /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) /\
  op_taint tn op = {} /\ (!x. op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  drule_all_then assume_tac compileEnvTheory.type_widens_to_word >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `value_has_type tv v` by
    (drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] expr_body_pre_eval_mods) >>
     gvs[value_runtime_typed_def]) >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type (get_tenv cx) t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all env_consistent_var_type_evaluates >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    (drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
     simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `elem_size_in_location cenv LocMemory elem = type_memory_size tv` by
    (simp[elem_size_in_location_def, is_slot_addressed_def] >>
     irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `compile_dynarray_append cenv (Var p) op _ _ elem _ cap T LocMemory sm = _`
        mp_tac >>
      simp[word_scale_def, append_memory_word_uses_store]) >>
  metis_tac[word_type_memory_size, valueEncodingTypingTheory.value_has_type_val_wf,
    expr_post_typed_stack_operand, ptr_val_ok_def]
QED
