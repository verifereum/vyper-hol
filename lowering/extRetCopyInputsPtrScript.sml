Theory extRetCopyInputsPtr
Ancestors
  extRetCopySuffixPtr representationCleanPtr bodyPtrDefs loweringPosts
  stmtLowering compileEnv venomState venomInst fragExec fragGasPathPtr
  words

Theorem compile_external_return_static_copy_gas_path_ptr:
  !cx ctx fn PG G tn s op m n nkey ut iv st x st' cenv es ty sa sb v tv w.
    compile_external_return (SOME op) F F (AbiCopy m) n F nkey ut iv st = (x,st') /\
    (!p. op = Var p ==> not_fresh_at st p) /\
    fn_has_code st st' fn /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    stmt_state_rel ctx fn cenv cx es s /\
    expr_val_at cenv cx ty sa sb es v op s /\
    ptr_val_ok cx ty v op G tn s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    ~is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\ value_has_type tv v /\
    m = type_memory_size tv /\ m <= n /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s /\ ~ctx_has_dalloca ctx ==>
    ?G' tn' t. gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 G' tn' (Halt t)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `m = 0`
  >- (gvs[] >> drule_all compile_external_return_copy_zero_suffix_gas_path_ptr >>
      simp[]) >>
  drule_all static_val_footprint >> strip_tac >>
  `val_footprint tv v <> 0 /\ m <= val_footprint tv v` by simp[] >>
  `!j. w2n w <= j /\ j < w2n w + type_memory_size tv ==> j NOTIN tn.t_mem` by
    (rpt strip_tac >> metis_tac[ptr_val_ok_static_clean]) >>
  drule_all ptr_val_ok_read_covers >> strip_tac >> gvs[] >>
  `type_memory_size tv <= val_footprint tv v` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [arithmeticTheory.ADD_COMM]
    compile_external_return_copy_suffix_gas_path_ptr) >> simp[]
QED
