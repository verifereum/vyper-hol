Theory bodyExtStaticRestoredStoreMods
Ancestors
  abiEncodeValuesStaticPrefix abiEncodeValuesStatic abiEncodeValuesSource
  abiEncodeValuesPhases abiCallerTupleLayout exprSimAbiEncodePlanMetadata
  entryDecodeStaticProps exprBopSimProps allocaSiteResource
  abiEncoderWindowPhase abiEncoderOpenInput abiDecodeRanges exprSimAbiEncodeExecFrame
  loweringPosts loweringStateRelDefs bodyPtrDefs ptrDiscipline fragGasOriginPtr
  contractABI vyperABI vyperValue vyperTyping venomState venomInst
  words finite_map pred_set list arithmetic

(* The interval starts after unwrap. The aggregate source can be either an
   original snapshot or a fresh materialization; both carry their actual
   ownership interval at this state. *)
Theorem ext_static_restored_store_mods:
  abi_encode_values_prefix_at ats avs hl d cursor loc slot i ready s G tn /\
  i < LENGTH ats /\ LENGTH ats = LENGTH avs /\
  at = EL i ats /\ av = EL i avs /\ at = vyper_to_abi_type (get_tenv cx) ty /\
  ~is_dynamic at /\ abi_encoder_layout_valid at av /\
  LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs) /\
  h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
  off = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs))) /\
  hs = abi_member_head_size at /\ h + hs <= hl /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,capacity) /\
  inst.inst_id <> loc /\ b <= d /\ d + off <= b + capacity /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\ type_memory_bytes ce ty = type_memory_size tv /\
  expr_val_rel cx ty v src s /\
  (is_word_type ty ==> op_taint tn src = {}) /\
  (~is_word_type ty ==>
    ptr_val_ok cx ty v src G tn s /\ expr_store_bound cx ty v src s /\
    stmt_state_rel H ctx func ce cx ee s /\
    expr_val_at ce cx ty first last ee v src s /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [root] /\
    not_local_ptr ce ee.scopes root /\
    (inst.inst_id < first.cs_next_id \/ last.cs_next_id <= inst.inst_id)) /\
  eval_operand (Var head) s = SOME (n2w (d+h)) /\ ptr_covers G tn head s hs /\
  not_fresh_at ready head /\ (!x. src = Var x ==> not_fresh_at ready x) /\
  compile_store_memory ce src (Var head) ty ty ready = ((),en) /\
  fn_has_code ready en func /\ ci_mono ready en /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = ready.cs_current_bb /\
  s.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?t G' tn'.
    abi_encode_values_prefix_at ats avs hl d cursor loc slot (SUC i) en t G' tn' /\
    mem_bytes_at (d+h) hs t.vs_memory = enc at av /\
    window_phase ctx func ready en {} [(d+h,hs)] s t /\ abi_encode_exec_frame func s t /\
    (!j. d+h <= j /\ j < d+h+hs ==> j NOTIN tn'.t_mem) /\
    (!j. (j < d+h \/ d+h+hs <= j) ==> (j IN tn'.t_mem <=> j IN tn.t_mem)) /\
    (!x. not_fresh_at ready x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `b + capacity <= s.vs_alloca_next` by drule_all_then ACCEPT_TAC alloca_site_registered_below >>
  `d+h+hs <= b+capacity /\ d+h+hs <= s.vs_alloca_next` by decide_tac >>
  `~is_dynamic (vyper_to_abi_type (get_tenv cx) ty)` by metis_tac[] >>
  `type_memory_size tv = static_length (vyper_to_abi_type (get_tenv cx) ty)` by
    metis_tac[abi_caller_static_memory] >>
  `LENGTH (enc at av) = hs` by fs[abi_encoder_layout_valid_def,abi_member_head_size_def] >>
  `?t G' tn'. mem_bytes_at (d+h) hs t.vs_memory = enc at av /\
    window_phase ctx func ready en {} [(d+h,hs)] s t /\ abi_encode_exec_frame func s t /\
    (!j. d+h <= j /\ j < d+h+hs ==> j NOTIN tn'.t_mem) /\
    (!j. (j < d+h \/ d+h+hs <= j) ==> (j IN tn'.t_mem <=> j IN tn.t_mem)) /\
    (!x. not_fresh_at ready x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')` by
    (Cases_on `is_word_type ty` >- suspend "word" >> suspend "aggregate") >>
  qexistsl [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  irule abi_encode_values_static_prefix >>
  qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `abi_encode_values_prefix_at _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas _ = _` (irule_at Any) >>
  qpat_assum `mem_bytes_at _ _ _ = _` (irule_at Any) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Resume ext_static_restored_store_mods[word]:
  `hs = 32` by
    (drule_then (qspecl_then [`ce.ce_struct_fields`,`ce`] strip_assume_tac)
       entryDecodeStaticPropsTheory.word_type_dec_sizes >>
     drule_all abi_encode_translated_head >> metis_tac[]) >>
  qpat_x_assum `hs = 32` SUBST_ALL_TAC >>
  `eval_operand src s = SOME (typed_val_to_w256 tv v)` by
    drule_all_then ACCEPT_TAC expr_val_rel_typed >>
  `op_taint tn src = {} /\ ptr_covers G tn head s 32 /\ d+h+32 <= s.vs_alloca_next` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  drule_all abi_encode_values_word_head >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`tn'`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `at = vyper_to_abi_type _ _` SUBST_ALL_TAC >>
  qexistsl [`t`,`G`,`tn'`] >>
  simp[op_taint_def,IN_DIFF] >> decide_tac
QED

Resume ext_static_restored_store_mods[aggregate]:
  qpat_assum `~is_word_type ty ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `~is_abi_dynamic ce.ce_struct_fields ty` by
    drule_all_then (fn th => simp[th]) abi_encode_translated_dynamic >>
  `val_footprint tv v = hs` by
    (drule_all abi_encode_values_static_footprint >> fs[abi_member_head_size_def]) >>
  `b <= d+h` by decide_tac >>
  drule_all (Q.INST [`d` |-> `d+h`,`len` |-> `hs`] abi_encode_values_memory_source) >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand src s = SOME (n2w (w2n w))` by simp[] >>
  `op_taint tn (Var head) = {}` by fs[ptr_covers_def] >>
  `!x. src = Var x \/ Var head = Var x ==> not_fresh_at ready x` by metis_tac[operand_11] >>
  `0 < LENGTH (enc at av) ==> w2n w + LENGTH (enc at av) <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n w,LENGTH (enc at av)) (d+h,LENGTH (enc at av)) /\
    (?p. src = Var p /\ ptr_covers G tn p s (LENGTH (enc at av))) /\
    (?p. Var head = Var p /\ ptr_covers G tn p s (LENGTH (enc at av)))` by
    (qpat_assum `LENGTH (enc at av) = hs` (fn th => pure_rewrite_tac [th]) >>
     qpat_assum `val_footprint tv v = hs` (fn th =>
       qpat_assum `0 < val_footprint tv v ==> _` (assume_tac o REWRITE_RULE [th])) >>
     disch_tac >> qpat_assum `0 < hs ==> _` (drule_then strip_assume_tac) >>
     asm_rewrite_tac[] >> conj_tac >> metis_tac[]) >>
  `d+h+LENGTH (enc at av) <= s.vs_alloca_next` by
    (qpat_assum `LENGTH (enc at av) = hs` (fn th => pure_rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `at = vyper_to_abi_type _ _` SUBST_ALL_TAC >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bs` |-> `enc (vyper_to_abi_type env ty) av`] abi_encode_values_static_store)) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`G'`,`tn'`] (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `LENGTH (enc _ _) = hs` (fn th =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  qexistsl [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Finalise ext_static_restored_store_mods
