(* Physical setup after the output allocation.  No execution is selected per horizon. *)
Theory bodyFullAbiEncodeSetupTail
Ancestors
  bodyFullAbiEncodeOffset bodyFullAbiEncodeStore bodyFullPathHistory
  bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission abiBuiltinEncodeCode typedMemoryCopy exprSimProps
  wordArgsPtr bodyFullUnwrapRun exprLoweringProps localPtrsProps bodyPtrMakeArrayWordStore exprSimPtrTopLevelImmutableCopy
  fragExec fragGasOriginPtr wordLoadStorePtr robustCopyTransportPtr
  emitHelper emitHelperProps compileEnv venomState venomExecSemantics
  instMemFrontier memSafeRun unitTransformDefs contextCodegenRel codegenRel
  words arithmetic finite_map pred_set ptrDiscipline venomInst bodyPtrDefs

Theorem setup_literal_store_origin[local]:
  emit_void MSTORE [Var dst;Lit w] a = ((),b) /\ fn_has_code a b func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var dst s = SOME (n2w p) /\ p < dimword(:256) /\
  ptr_covers G tn dst s 32 /\ allocas_from lo s /\
  p+32 <= s.vs_alloca_next ==>
  ?t tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)) /\
    t = (mstore p w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    tf = (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> mem_word_at p mem = w) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      lo <= p /\ (!name base sz. local_region ce es.scopes s name base sz ==>
        regions_disjoint p 32 base sz) ==>
      ghost_inv_at D lo d ce cx es G tf t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G tf)
Proof
  strip_tac >> drule_all emit_void_fetch_boundary >> strip_tac >>
  qexistsl_tac [`mstore p w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}`] >>
  simp[] >> conj_tac >- suspend "path" >>
  conj_tac >- simp[mstore_def] >>
  conj_tac >- suspend "robust" >>
  conj_tac >- suspend "inv" >>
  rpt strip_tac >> irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[op_taint_def, SUBSET_DEF]
QED

Resume setup_literal_store_origin[path]:
  gen_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst a.cs_next_id MSTORE [Var dst;Lit w] [])` by simp[] >>
  drule_at (Pat `get_instruction _ _ = _`) abi_encode_mstore_origin_path >>
  simp[eval_operand_def, op_taint_def, w2n_n2w,
    SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame] >>
  disch_then irule >> simp[] >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def, mk_inst_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    sized_source_write_range_def, fixed_source_write_range_def,
    eval_operand_def, w2n_n2w, ADD_COMM]
QED

Resume setup_literal_store_origin[robust]:
  rpt strip_tac >>
  `step_taint (mk_inst a.cs_next_id MSTORE [Var dst;Lit w] []) s (mstore p w s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32})` by
    (drule (Q.INST [`value` |-> `Lit w`] toplevel_immutable_mstore_ghost_frame) >>
     simp[eval_operand_def, op_taint_def, w2n_n2w] >> metis_tac[]) >>
  drule_at (Pat `lookup_var _ _ = _`) mstore_raw_robust_word >>
  simp[w2n_n2w] >> disch_then irule >>
  qexistsl_tac [`a.cs_next_id`, `tn`, `Lit w`] >>
  simp[eval_operand_def, op_taint_def]
QED

Resume setup_literal_store_origin[inv]:
  rpt strip_tac >>
  `ghost_kept_at lo ce es a G tn s G tn` by simp[ghost_kept_at_refl] >>
  drule_at (Pat `lookup_var _ _ = _`) (cj 1 abi_encode_mstore_frame_at) >>
  simp[eval_operand_def, op_taint_def, w2n_n2w,
    SRULE [eval_operand_def, op_taint_def] toplevel_immutable_mstore_ghost_frame] >>
  disch_then irule >>
  simp[] >> conj_tac
  >- gvs[] >>
  simp[] >> conj_tac
  >- (qexists_tac `Lit w` >> simp[eval_operand_def]) >>
  metis_tac[]
QED

Finalise setup_literal_store_origin

(* The selector occupies a full MSTORE word, even though only four bytes are
   included in the encoded payload.  Allocation is deliberately a caller step. *)
Theorem abi_encode_setup_tail_origin:
  k = (case mid of NONE => 0 | SOME w => 4) /\
  N = 32 + 32 * word_size (maxlen+k) /\
  write_len = (case mid of NONE => 0 | SOME w => 32) /\
  emit_op ADD [Var root;Lit (n2w (32+k))] a = (data,address_st) /\
  abi_builtin_encode_method_id mid (Var root) address_st = ((),ready) /\
  fn_has_code a ready func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ alloca_inv s /\
  lookup_var root s = SOME (n2w p) /\ not_fresh_at a root /\
  ptr_covers G tn root s N /\ lo <= p /\
  p+N <= s.vs_alloca_next /\ p+N < dimword(:256) ==>
  ?dp t G' tn'.
    data = Var dp /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    ~t.vs_halted /\ t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\
    eval_operand data t = SOME (n2w (p+32+k)) /\
    ptr_covers G' tn' dp t maxlen /\
    ptr_covers G' tn' root t N /\
    eval_operand (Var root) t = SOME (n2w p) /\ not_fresh_at ready dp /\
    (case mid of NONE => T | SOME w =>
      !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
        mem_word_at (p+32) mem = w << 224) /\
    typed_copy_state_frame a (p+32) write_len s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    alloca_inv t /\ allocas_from lo t /\
    tn'.t_mem = tn.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!op. (!x. op = Var x ==> not_fresh_at a x) ==>
      eval_operand op t = eval_operand op s /\
      op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op) /\
    (!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==>
      ptr_covers G' tn' x t n) /\
    (!code. abi_alloca_history code s ==> abi_alloca_history code t) /\
    (fn_inst_ids_distinct func /\ alloca_history func s ==> alloca_history func t) /\
    (!ce es.
      local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      local_ptrs_rel func ce es.scopes t) /\
    (!D d ce cx es.
      ghost_inv_at D lo d ce cx es G tn s /\ local_ptrs_rel func ce es.scopes s /\
      (!name x sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) sz) ==>
        not_fresh_at a x) /\
      (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
      (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> not_fresh_at a x) /\
      (!name b sz. local_region ce es.scopes s name b sz ==>
        regions_disjoint (p+32) write_len b sz) ==>
      ghost_inv_at D lo d ce cx es G' tn' t) /\
    (!ce es origin G0 tn0 s0.
      ghost_kept_at lo ce es origin G0 tn0 s0 G tn /\
      (!x. not_fresh_at origin x ==> not_fresh_at a x) ==>
      ghost_kept_at lo ce es origin G0 tn0 s0 G' tn')
Proof
  strip_tac >> Cases_on `mid`
  >- suspend "none" >> suspend "some"
QED

Resume abi_encode_setup_tail_origin[none]:
  gvs[abi_builtin_encode_method_id_def, comp_return_def] >>
  `32+maxlen <= 32+32*word_size maxlen` by
    (mp_tac (Q.SPEC `maxlen` le_word_size_mul) >> decide_tac) >>
  `w2n (n2w p : bytes32)+32 < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_at (Pat `emit_op _ _ _ = _`)
    (Q.INST [`off` |-> `32`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  simp[] >> disch_then (qspecl_then [`maxlen`, `explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `data = Var dp` >>
  `!x. not_fresh_at a x ==> x <> dp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `lookup_var dp t = _` >>
  `!x n. not_fresh_at a x /\ ptr_covers G tn x s n ==>
    ptr_covers G' tn' x t n` by
    (rpt strip_tac >> `x <> dp` by metis_tac[] >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `alloca_inv t` by
    (irule alloca_inv_fields >> qexists_tac `s` >>
     simp[Abbr `t`, update_var_def]) >>
  `allocas_from lo t` by
    (gvs[Abbr `t`, update_var_def, allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`dp`, `t`, `G'`, `tn'`] >>
  asm_rewrite_tac[] >>
  simp[Abbr `t`, update_var_def, eval_operand_def] >>
  conj_tac >- suspend "none_frame" >>
  conj_tac >- suspend "none_history" >>
  conj_tac >- suspend "none_locals" >>
  conj_tac >- suspend "none_inv" >>
  suspend "none_kept"
QED

Resume abi_encode_setup_tail_origin[none_frame]:
  simp[typed_copy_state_frame_def, typed_copy_frame_def, lookup_var_def,
    FLOOKUP_UPDATE, venom_state_component_equality] >> rpt strip_tac >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[none_history]:
  rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[body_full_path_alloca_history]
QED

Resume abi_encode_setup_tail_origin[none_locals]:
  rpt strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> `p' <> dp` by metis_tac[] >> simp[]
QED

Resume abi_encode_setup_tail_origin[none_inv]:
  rpt strip_tac >> gvs[update_var_def] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[none_kept]:
  rpt strip_tac >> gvs[update_var_def] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some]:
  gvs[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> rename1 `emit_op ADD [Var root;Lit 32w] address_st = (midop,store_st)` >>
  `cs_extends a address_st /\ cs_extends address_st store_st /\ cs_extends store_st ready` by
    (gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
     simp[cs_extends_def] >> rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code a address_st func /\ fn_has_code address_st store_st func /\
    fn_has_code store_st ready func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `36+maxlen <= 32+32*word_size (maxlen+4)` by
    (mp_tac (Q.SPEC `maxlen+4` le_word_size_mul) >> decide_tac) >>
  `w2n (n2w p : bytes32)+36 < dimword(:256)` by
    (simp[w2n_n2w] >> decide_tac) >>
  drule_at (Pat `emit_op ADD [Var root;Lit 36w] a = _`)
    (Q.INST [`off` |-> `36`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ root s _`)) >>
  disch_then (drule_at (Pat `fn_has_code a address_st _`)) >>
  disch_then (drule_at (Pat `allocas_from _ s`)) >>
  simp[] >> disch_then (qspecl_then [`maxlen`, `explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `data = Var dp` >>
  qmatch_asmsub_abbrev_tac `lookup_var dp s1 = _` >>
  `!v. not_fresh_at a v ==> v <> dp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  `lookup_var root s1 = SOME (n2w p)` by metis_tac[] >>
  `ptr_covers G' tn' root s1 (32 * word_size (maxlen+4)+32)` by
    (`root <> dp` by metis_tac[] >>
     gvs[ptr_covers_def, Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `~s1.vs_halted /\ s1.vs_current_bb = address_st.cs_current_bb /\
    s1.vs_inst_idx = LENGTH address_st.cs_current_insts /\ allocas_from lo s1` by
    (gvs[Abbr `s1`, update_var_def, allocas_from_def] >> metis_tac[]) >>
  `32+32 <= 32 * word_size (maxlen+4)+32` by
    simp[vfmConstantsTheory.word_size_def, X_LT_DIV] >>
  drule_at (Pat `emit_op ADD [Var root;Lit 32w] address_st = _`)
    (Q.INST [`off` |-> `32`] (SPEC_ALL abi_encode_owned_offset_origin)) >>
  disch_then (drule_at (Pat `ptr_covers G' tn' root s1 _`)) >>
  disch_then (drule_at (Pat `fn_has_code address_st store_st _`)) >>
  disch_then (drule_at (Pat `allocas_from _ s1`)) >>
  simp[w2n_n2w] >>
  disch_then (qspecl_then [`32`, `explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `midop = Var mp` >>
  qmatch_asmsub_abbrev_tac `lookup_var mp s2 = _` >>
  `~s2.vs_halted /\ s2.vs_current_bb = store_st.cs_current_bb /\
    s2.vs_inst_idx = LENGTH store_st.cs_current_insts /\ allocas_from lo s2 /\
    ptr_covers G'' tn'' mp s2 32 /\
    p+32+32 <= s2.vs_alloca_next /\ p+32 < dimword(:256)` by
    (gvs[Abbr `s2`, Abbr `s1`, update_var_def, allocas_from_def] >>
     conj_tac >- metis_tac[] >>
     mp_tac (Q.SPEC `maxlen+4` le_word_size_mul) >>
     Cases_on `word_size (maxlen+4)` >> simp[] >> decide_tac) >>
  qpat_x_assum `midop = Var mp` SUBST_ALL_TAC >>
  drule_at (Pat `emit_void MSTORE _ _ = _`) setup_literal_store_origin >>
  disch_then (drule_at (Pat `fn_has_code store_st ready _`)) >>
  disch_then (drule_at (Pat `lookup_var mp s2 = _`)) >>
  disch_then (drule_at (Pat `ptr_covers G'' tn'' mp s2 _`)) >>
  disch_then (drule_at (Pat `allocas_from _ s2`)) >>
  simp[] >> disch_then (qspecl_then [`explicit`, `ctx`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (s2,G'',tn'') [] (OK t,_,tf)` >>
  `!v. not_fresh_at a v ==> not_fresh_at address_st v` by
    (qpat_x_assum `emit_op ADD _ a = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
     disch_tac >> gvs[] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]) >>
  `!v. not_fresh_at address_st v ==> v <> mp` by
    (drule_all emit_op_fetch_boundary >> strip_tac >> gvs[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G'',tf)` by
    metis_tac[gas_origin_ptr_path_append, listTheory.APPEND] >>
  qexistsl_tac [`t`, `G''`, `tf`] >> asm_rewrite_tac[] >>
  suspend "some_posts"
QED

Resume abi_encode_setup_tail_origin[some_posts]:
  `dp <> mp` by metis_tac[] >>
  `!v. not_fresh_at a v ==> v <> mp` by metis_tac[] >>
  conj_tac >- simp[Abbr `t`, mstore_def] >>
  conj_tac >- simp[Abbr `t`] >>
  conj_tac >- simp[Abbr `t`] >>
  conj_tac >- suspend "some_data" >>
  conj_tac >- suspend "some_dp_cover" >>
  conj_tac >- suspend "some_root_cover" >>
  conj_tac >- suspend "some_root_value" >>
  conj_tac >- suspend "some_fresh" >>
  conj_tac >- simp[Abbr `tf`, Abbr `t`] >>
  conj_tac >- suspend "some_frame" >>
  conj_tac >- simp[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def] >>
  conj_tac >- simp[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def] >>
  conj_tac >- suspend "some_alloca_inv" >>
  conj_tac >- (gvs[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def, allocas_from_def] >> metis_tac[]) >>
  simp[Abbr `tf`] >>
  conj_tac >- suspend "some_operands" >>
  conj_tac >- suspend "some_old_cover" >>
  conj_tac >- (rpt strip_tac >> irule abiAllocationHistoryTheory.abi_alloca_history_frame >>
    qexists_tac `s` >> simp[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def]) >>
  conj_tac >- metis_tac[body_full_path_alloca_history] >>
  conj_tac >- suspend "some_locals" >>
  conj_tac >- suspend "some_inv" >>
  suspend "some_kept"
QED

Resume abi_encode_setup_tail_origin[some_data]:
  gvs[Abbr `t`, Abbr `s2`, mstore_def, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE]
QED

Resume abi_encode_setup_tail_origin[some_dp_cover]:
  gvs[ptr_covers_def, Abbr `tf`, Abbr `t`, Abbr `s2`, Abbr `s1`,
    mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_root_cover]:
  `root <> dp /\ root <> mp` by metis_tac[] >>
  `p < dimword(:256)` by decide_tac >>
  gvs[ptr_covers_def, Abbr `tf`, Abbr `t`, Abbr `s2`, Abbr `s1`,
    mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def, w2n_n2w] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_root_value]:
  `root <> dp /\ root <> mp` by metis_tac[] >>
  gvs[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_fresh]:
  qpat_x_assum `emit_op ADD _ address_st = _` mp_tac >>
  qpat_x_assum `emit_void MSTORE _ store_st = _` mp_tac >>
  simp[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]
QED

Resume abi_encode_setup_tail_origin[some_frame]:
  irule typed_copy_state_frame_trans >> qexists_tac `s2` >>
  reverse conj_tac >- simp[Abbr `t`, typed_copy_mstore_state_frame] >>
  simp[Abbr `s2`, Abbr `s1`, typed_copy_state_frame_def, typed_copy_frame_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE, venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_alloca_inv]:
  irule alloca_inv_fields >> qexists_tac `s` >>
  simp[Abbr `t`, Abbr `s2`, Abbr `s1`, mstore_def, update_var_def]
QED

Resume abi_encode_setup_tail_origin[some_operands]:
  Cases >> simp[eval_operand_def, op_taint_def, Abbr `t`, Abbr `s2`, Abbr `s1`,
    mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> `s' <> dp /\ s' <> mp` by metis_tac[] >>
  gvs[op_taint_def] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_old_cover]:
  rpt strip_tac >> `x' <> dp /\ x' <> mp` by metis_tac[] >>
  gvs[ptr_covers_def, Abbr `t`, Abbr `s2`, Abbr `s1`,
    mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_locals]:
  rpt strip_tac >> simp[Abbr `t`, local_ptrs_rel_inst_idx] >>
  irule local_ptrs_rel_mstore >> reverse conj_tac
  >- (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
      simp[Abbr `s2`, Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[] >>
      `p' <> dp /\ p' <> mp` by metis_tac[] >> simp[]) >>
  rpt strip_tac >>
  `local_region ce es.scopes s name b sz` by
    (qpat_x_assum `local_region _ _ s2 _ _ _` mp_tac >>
     simp[loweringStateRelDefsTheory.local_region_def, Abbr `s2`, Abbr `s1`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> `p' <> dp /\ p' <> mp` by metis_tac[] >>
     gvs[] >> metis_tac[]) >>
  gvs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED

Resume abi_encode_setup_tail_origin[some_inv]:
  rpt strip_tac >>
  `ghost_inv_at D lo d ce cx es G' tn' s1` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  `ghost_inv_at D lo d ce cx es G'' tn'' s2` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> rename1 `local_region ce es.scopes s2 name lb sz` >>
      `local_region ce es.scopes s name lb sz` by
        (qpat_x_assum `local_region _ _ s2 _ _ _` mp_tac >>
         simp[loweringStateRelDefsTheory.local_region_def, Abbr `s2`, Abbr `s1`,
           update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
         rpt strip_tac >> `p' <> dp /\ p' <> mp` by metis_tac[] >>
         gvs[] >> metis_tac[]) >> metis_tac[]) >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  simp[Abbr `s2`, Abbr `s1`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  `p' <> dp /\ p' <> mp` by metis_tac[] >> simp[]
QED

Resume abi_encode_setup_tail_origin[some_kept]:
  rpt strip_tac >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G' tn'` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo ce es origin G0 tn0 s0 G'' tn''` by
    (first_assum irule >> simp[] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Finalise abi_encode_setup_tail_origin
