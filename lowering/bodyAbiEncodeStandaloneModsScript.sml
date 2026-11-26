(* Physical payload execution after the standalone saved operand is unwrapped. *)
Theory bodyAbiEncodeStandaloneMods
Ancestors
  abiEncoderWindowJoint abiEncoderWindowPhase abiEncoderWindowContract
  exprLowering compileEnv fragExec bodyPtrDefs fragGasSeqPtr
  freshWrites ptrDiscipline venomMemDefs venomState words list finite_map
  contractABI vyperAST
  bodyAbiEncodeStandaloneRestoreMods bodyAbiEncodeRegisteredFrameMods
  bodyAbiEncodeRestoredInputMods bodyAbiEncodeStandaloneSourceMods
  bodyAbiEncodePackedPostMods bodyFullExtCallDirectPhase abiEncodeValuesPhases
  externalReturnEncoderSites bodyFullPostsMods bodyFullShadowBodyInv
  exprLoweringProps loweringHalt exprSimUnwrap exprSimWordArgs exprSimProps wordArgsPtr
  loweringPosts loweringStateRelDefs bodyMemoryDefs stateRelProj
  bodyFullHashKeccakFixed allocaSiteResource vyperStorageFootprint
  vyperInterpreter vyperState vyperContext vyperTyping vyperABI vyperTypeSystem
  abiEncoderSourceInvoke exprSimAbiEncodePlanTranslation abiBuiltinAllocation
  memoryReadProps exprSimHypsDefs abiDecodeStaticProps pred_set option arithmetic

Theorem abi_encode_nonword_window_mods:
  compile_abi_encode_payload ce T [saved] [ty] dst ready = (out,en) /\
  ~is_word_type ty /\ unwrap_value ce saved ready = (src,st) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce ty /\
  abi_encoder_admissible ei /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    abi_encoder_window_input ei at av sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH (enc at av)) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH (enc at av) <= s.vs_alloca_next /\
  (0 < LENGTH (enc at av) ==> ?p. dst = Var p /\
    ptr_covers G tn p s (LENGTH (enc at av))) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc at av))] s t /\
    abi_encode_exec_frame func s t /\
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH (enc at av) ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH (enc at av) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  `compile_abi_encode_to_buf dst src ei st = (out,en)` by
    (qpat_x_assum `compile_abi_encode_payload _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_abi_encode_payload_def, comp_bind_def]) >>
  drule_all compile_abi_encode_to_buf_window_joint >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  drule_then assume_tac window_phase_strong_result >>
  drule_then (strip_assume_tac o MATCH_MP abi_encoder_window_result_output)
    window_strong_result_public >>
  qexistsl [`t`,`G'`,`tn'`] >> asm_rewrite_tac[]
QED

Theorem abi_encode_nonword_payload_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiEncode F mid) target [e]) es /\
  eval_exprs cx [e] (es with gas_obs := gs) = (INL [v],ee) /\
  ~is_word_type (lowered_value_type ce e) /\ assignable_type (get_tenv cx) (lowered_value_type ce e) /\
  get_tenv cx SUBMAP E0 /\ sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t tv. evaluate_type E0 t = SOME tv ==> type_memory_bytes ce t = type_memory_size tv) /\
  compile_abi_encode_payload ce T [saved] [lowered_value_type ce e] (Var dst) ready = (len,body_end) /\
  fn_has_code ready body_end func /\ fn_inst_ids_distinct func /\
  k = LENGTH (abi_encode_method_id_bytes mid) /\
  cap = 32 + 32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) + k) /\
  MEM (mk_inst aid ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
  not_local_ptr ce ee.scopes root /\
  front.cs_next_id <= aid /\ ss.cs_next_id <= aid /\ aid < ready.cs_next_id /\
  front.cs_next_var <= ready.cs_next_var /\ local_ptrs_reserved ce front /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at front x) /\
  (!x. vv_operand saved = Var x ==> not_fresh_at ready x) /\
  not_fresh_at ready root /\ not_fresh_at ready dst /\
  eval_operand (Var root) s = SOME (n2w p) /\ ptr_covers G tn root s cap /\
  eval_operand (Var dst) s = SOME (n2w (p+32+k)) /\ ptr_covers G tn dst s (cap-(32+k)) /\
  FLOOKUP s.vs_allocas aid = SOME (p,cap) /\ lo <= p /\
  read_memory (p+32) k s = abi_encode_method_id_bytes mid /\
  (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tn.t_mem) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\
    stmt_state_rel H ctx func ce cx ee s /\ immutable_frame_mods func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  return_buf_frame d ce ready s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = ready.cs_current_bb /\ s.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?bytes limit q Gq tq.
    ann = BaseT (BytesT (Dynamic limit)) /\
    evaluate_type_builtin cx (AbiEncode F mid) target [expr_type e] [v] =
      INL (BytesV (abi_encode_method_id_bytes mid ++ bytes)) /\
    LENGTH (abi_encode_method_id_bytes mid ++ bytes) <= limit /\
    32+k+LENGTH bytes <= cap /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tq)) /\
    ~q.vs_halted /\ q.vs_current_bb = body_end.cs_current_bb /\
    q.vs_inst_idx = LENGTH body_end.cs_current_insts /\ alloca_history func q /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\ s.vs_alloca_next <= q.vs_alloca_next /\
    alloca_inv q /\ allocas_from lo q /\ q.vs_alloca_next < dimword (:256) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee q /\ immutable_frame_mods func ce cx ee q /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gq tq q) /\
    return_buf_frame d ce body_end q /\ pure_frame ce func ee front s q /\
    wb_frame ce ee ee front s q /\ ghost_kept_at lo ce ee front G tn s Gq tq /\
    front.cs_next_var <= body_end.cs_next_var /\ aid < body_end.cs_next_id /\
    not_fresh_at body_end root /\
    eval_operand (Var root) q = SOME (n2w p) /\ ptr_covers Gq tq root q cap /\
    FLOOKUP q.vs_allocas aid = SOME (p,cap) /\
    eval_operand len q = SOME (n2w (LENGTH bytes)) /\ op_taint tq len = {} /\
    (!x. len = Var x ==> not_fresh_at body_end x) /\
    mem_bytes_at (p+32) k q.vs_memory = abi_encode_method_id_bytes mid /\
    mem_bytes_at (p+32+k) (LENGTH bytes) q.vs_memory = bytes /\
    (!i. p+32 <= i /\ i < p+32+k+LENGTH bytes ==> i NOTIN tq.t_mem)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_nonword_source_mods >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choosel_then [`rt`,`av`,`limit`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `ty = lowered_value_type ce e` >>
  qabbrev_tac `bytes = enc (vyper_to_abi_type (get_tenv cx) ty) av` >>
  `32+k+LENGTH bytes <= cap` by
    (qspec_then `abi_size_bound ce.ce_struct_fields ty + k` assume_tac abi_builtin_word_size_capacity >> decide_tac) >>
  Cases_on `unwrap_value ce saved ready` >> rename1 `unwrap_value ce saved ready = (src,st)` >>
  `compile_abi_encode_to_buf (Var dst) src (type_to_abi_enc_info ce.ce_struct_fields ce ty) st = (len,body_end)` by
    (qpat_assum `compile_abi_encode_payload _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [compile_abi_encode_payload_def,comp_bind_def,HD] >>
     asm_rewrite_tac[] >> simp[pairTheory.UNCURRY,LET_THM]) >>
  `ci_mono ready st /\ ci_mono ready body_end` by
    (conj_tac
     >- (qspecl_then [`ce`,`saved`,`ready`] mp_tac ci_mono_unwrap_value >> simp[]) >>
     `ci_mono ready (SND (compile_abi_encode_payload ce T [saved] [ty] (Var dst) ready))` by
       irule ci_mono_compile_abi_encode_payload >>
     pop_assum mp_tac >> asm_rewrite_tac[pairTheory.SND]) >>
  `cs_extends st body_end` by (irule compile_abi_encode_to_buf_extends >> metis_tac[]) >>
  qpat_x_assum `ci_mono ready st` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  qpat_x_assum `ci_mono ready body_end` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `32+k <= cap` by decide_tac >>
  qpat_x_assum `cap = 32 + _` kall_tac >>
  (* Restore the saved row, retaining its source allocation interval. *)
  (Q.SUBGOAL_THEN `?z Gz tz first last.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    ~z.vs_halted /\ z.vs_current_bb = st.cs_current_bb /\
    z.vs_inst_idx = LENGTH st.cs_current_insts /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    expr_val_rel cx ty v src z /\ expr_val_at ce cx ty first last ee v src z /\
    ptr_val_ok cx ty v src Gz tz z /\ expr_store_bound cx ty v src z /\
    (!x. src = Var x ==> not_fresh_at st x) /\
    (aid < first.cs_next_id \/ last.cs_next_id <= aid) /\ last.cs_next_id <= st.cs_next_id /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z) /\
    return_buf_frame d ce st z /\ pure_frame ce func ee ready s z /\
    wb_frame ce ee ee ready s z /\ ghost_kept_at lo ce ee ready G tn s Gz tz /\
    (!x. not_fresh_at ready x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x cap. not_fresh_at ready x /\ ptr_covers G tn x s cap ==> ptr_covers Gz tz x z cap) /\
    (!id row. FLOOKUP s.vs_allocas id = SOME row ==> FLOOKUP z.vs_allocas id = SOME row) /\
    read_memory (p+32) k z = abi_encode_method_id_bytes mid /\
    (!i. p+32 <= i /\ i < p+32+k ==> i NOTIN tz.t_mem)`
    (qx_choosel_then [`z`,`Gz`,`tz`,`first`,`last`] (MAP_EVERY assume_tac o CONJUNCTS))
   >- (qunabbrev_tac `ty` >> irule abi_encode_standalone_restore_mods >>
     asm_rewrite_tac[] >> conj_tac >- (qexists_tac `cap` >> asm_rewrite_tac[] >> decide_tac) >>
     conj_tac >- (qexistsl_tac [`copy`,`sa`,`saved`,`si`,`sm`,`ss`,`vv`] >> asm_rewrite_tac[]) >>
     qexists_tac `rt` >> asm_rewrite_tac[])) >>
  qpat_x_assum `k = LENGTH _` (assume_tac o SYM) >>
  qpat_assum `storage_trace_domain _ _ _` (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `local_ptrs_reserved ce st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `front` >> asm_rewrite_tac[] >> decide_tac) >>
  `front.cs_next_var <= st.cs_next_var /\ aid < st.cs_next_id` by decide_tac >>
  `FLOOKUP z.vs_allocas aid = SOME (p,cap)` by
    (qpat_assum `!id row. FLOOKUP s.vs_allocas id = SOME row ==> _` (drule_then ACCEPT_TAC)) >>
  `p <= p+32+k /\ p+32+k+LENGTH bytes <= p+cap` by decide_tac >>
  qabbrev_tac `owner = mk_inst aid ALLOCA [Lit (n2w cap)] [root]` >>
  `MEM owner (fn_insts func) /\ owner.inst_id = aid /\ owner.inst_opcode = ALLOCA /\
   owner.inst_outputs = [root]` by simp[Abbr `owner`, venomInstTheory.mk_inst_def] >>
  (Q.SUBGOAL_THEN `owner.inst_id < st.cs_next_id /\
   (owner.inst_id < first.cs_next_id \/ last.cs_next_id <= owner.inst_id) /\
   FLOOKUP z.vs_allocas owner.inst_id = SOME (p,cap)` (MAP_EVERY assume_tac o CONJUNCTS)
   >- asm_rewrite_tac[]) >>
  `bytes = enc (vyper_to_abi_type (get_tenv cx) ty) av` by simp[Abbr `bytes`] >>
  `?w at rv.
    eval_operand src z = SOME w /\ op_taint tz src = {} /\ enc at rv = bytes /\
    (!mem. mem_agree_outside tz.t_mem z.vs_memory mem ==>
      abi_encoder_window_input
        (type_to_abi_enc_info ce.ce_struct_fields ce ty)
        at rv (w2n w) (val_footprint rt v) mem) /\
    (0 < val_footprint rt v ==>
      w2n w + val_footprint rt v <= z.vs_alloca_next /\
      venomMemDefs$regions_disjoint (w2n w,val_footprint rt v) (p+32+k,LENGTH bytes) /\
      ?pp. src = Var pp /\ ptr_covers Gz tz pp z (val_footprint rt v)) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st body_end /\
      FLOOKUP z.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      (0 < val_footprint rt v ==>
        regions_disjoint (w2n w,val_footprint rt v) (b,sz)) /\
      regions_disjoint (p+32+k,LENGTH bytes) (b,sz))` by
    (irule (Q.INST [`tv` |-> `rt`, `en` |-> `body_end`, `d` |-> `p+32+k`]
       (INST_TYPE [``:'a`` |-> ``:256``] abi_encode_restored_window_input_mods)) >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (qexistsl_tac [`Var dst`,`len`,`ready`,`saved`] >>
         conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (qexistsl_tac [`E0`,`storage_trace_horizon ee.storage_trace`,`av`,`p`,`ctx`,`cx`,`ee`,`first`,`last`,`owner`,`cap`,`root`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  `abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info ce.ce_struct_fields ce ty)` by
    (irule abi_encode_translated_plan >>
     conj_tac >- (qexists_tac `rt` >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `E0` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  drule_then assume_tac (cj 1 abi_enc_plan_admissible) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ z` (fn th =>
    MAP_EVERY (fn rule => mp_tac (MATCH_MP rule th) >> strip_tac)
      [stmt_state_rel_local_ptrs_alloca,stmt_state_rel_alloca_room,
       stmt_state_rel_fmp_room,stmt_state_rel_allocas_below_fmp]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z /\
     z.vs_alloca_next + pending_alloca_size func z <= w2n z.vs_initial_fmp` by
    (strip_tac >> conj_tac
     >- (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp z`
           (drule_then ACCEPT_TAC))
     >- (qpat_assum `fmp_room ctx func z` (mp_tac o REWRITE_RULE[fmp_room_def]) >>
         (impl_tac >- (disj1_tac >> first_assum ACCEPT_TAC)) >>
         strip_tac >> decide_tac)) >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ lo d ce cx ee Gz tz z`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all_then assume_tac alloca_site_registered_below >>
  `p+32+k+LENGTH bytes <= z.vs_alloca_next` by decide_tac >>
  `!x. not_fresh_at ready x ==> not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  `!x. src = Var x \/ Var dst = Var x ==> not_fresh_at st x` by
    (gen_tac >> strip_tac
     >- (qpat_assum `!x. src = Var x ==> _` (drule_then ACCEPT_TAC)) >>
     qpat_x_assum `Var dst = Var x` mp_tac >> rewrite_tac[operand_11] >>
     disch_then (SUBST1_TAC o SYM) >>
     qpat_assum `!x. not_fresh_at ready x ==> not_fresh_at st x`
       (drule_then ACCEPT_TAC)) >>
  `ptr_covers Gz tz dst z (cap-(32+k))` by
    (qpat_assum `!x n. not_fresh_at ready x /\ ptr_covers G tn x s n ==> _` (drule_all_then ACCEPT_TAC)) >>
  `ptr_covers Gz tz dst z (LENGTH bytes)` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `cap-(32+k)` >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tz (Var dst) = {}` by
    (qpat_assum `ptr_covers Gz tz dst z (LENGTH bytes)`
       (strip_assume_tac o REWRITE_RULE[ptr_covers_def]) >> first_assum ACCEPT_TAC) >>
  `eval_operand (Var dst) z = SOME (n2w (p+32+k))` by
    (qpat_assum `!x. not_fresh_at ready x ==> lookup_var x z = _ /\ _`
       (drule_then strip_assume_tac) >>
     PURE_REWRITE_TAC[eval_operand_def] >>
     qpat_assum `lookup_var dst z = lookup_var dst s` (PURE_REWRITE_TAC o single) >>
     qpat_assum `eval_operand (Var dst) s = _`
       (ACCEPT_TAC o REWRITE_RULE[eval_operand_def])) >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids st body_end)` >>
  qabbrev_tac `addr = p+32+k` >>
  (* Run the physical encoder at the restored state and ghost frame. *)
  `?q Gq tq.
    window_phase ctx func st body_end ids [(addr,LENGTH bytes)] z q /\
    abi_encode_exec_frame func z q /\
    mem_bytes_at addr (LENGTH bytes) q.vs_memory = bytes /\
    eval_operand len q = SOME (n2w (LENGTH bytes)) /\
    op_taint tq len = {} /\ (!x. len = Var x ==> not_fresh_at body_end x) /\
    (!i. addr <= i /\ i < addr + LENGTH bytes ==> i NOTIN tq.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP Gq x = FLOOKUP Gz x /\ op_taint tq (Var x) = op_taint tz (Var x)) /\
    (!i. (i < addr \/ addr + LENGTH bytes <= i) /\
      (!id b sz. id IN ids /\ FLOOKUP q.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i) ==>
      (i IN tq.t_mem <=> i IN tz.t_mem)) /\
    tq.t_stor = tz.t_stor /\ tq.t_trans = tz.t_trans /\ tq.t_imm = tz.t_imm /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (z,Gz,tz) [] (OK q,Gq,tq)` by
    (qunabbrev_tac `ids` >>
     qpat_assum `enc at rv = bytes` (PURE_REWRITE_TAC o single o SYM) >>
     irule abi_encode_nonword_window_mods >>
     qpat_assum `enc at rv = bytes` (PURE_REWRITE_TAC o single) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`val_footprint rt v`,`ce`,`Var dst`,
       `type_to_abi_enc_info ce.ce_struct_fields ce ty`,`ready`,`saved`,`w2n w`,`src`,`ty`] >>
     PURE_REWRITE_TAC[n2w_w2n] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- REFL_TAC >>
     disch_tac >> qexists_tac `dst` >> conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
  `!i. i IN ids ==> front.cs_next_id <= i` by
    (qunabbrev_tac `ids` >> simp_tac bool_ss
      [window_alloca_sites_def,IN_GSPEC_IFF,abiEncoderPropsTheory.frag_ids_def] >>
     rpt strip_tac >> decide_tac) >>
  `!i. i IN aid INSERT ids ==>
     ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_id = i /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x` by
    (simp_tac bool_ss [IN_INSERT] >> gen_tac >> strip_tac
     >- (qexistsl_tac [`owner`,`root`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
         qpat_assum `i = aid` (PURE_REWRITE_TAC o single) >> first_assum ACCEPT_TAC) >>
     qpat_assum `i IN ids` mp_tac >>
     simp_tac bool_ss [Abbr `ids`,window_alloca_sites_def,IN_GSPEC_IFF] >>
     strip_tac >> rename1 `inst.inst_id = i` >>
     `inst.inst_id IN frag_ids st body_end` by
       (qpat_assum `inst.inst_id = i` (PURE_REWRITE_TAC o single) >> first_assum ACCEPT_TAC) >>
     drule_all encoder_function_alloca_nonlocal >>
     disch_then (qspec_then `ee.scopes`
       (CONJUNCTS_THEN2 kall_tac (qx_choose_then `x` strip_assume_tac))) >>
     qexistsl_tac [`inst`,`x`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (Q.SUBGOAL_THEN `?H. valid_horizon cx st0 H ee.storage_trace` assume_tac
   >- (qexists_tac `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (\(b,n). p <= b /\ b+n <= p+cap) [(addr,LENGTH bytes)]` by
    (simp_tac bool_ss [EVERY_DEF,pairTheory.UNCURRY,pairTheory.FST,pairTheory.SND] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!i. EVERY (\(b,n). i < b \/ b+n <= i) [(addr,LENGTH bytes)] /\
     (!a b n. a IN ids /\ FLOOKUP q.vs_allocas a = SOME (b,n) ==> i < b \/ b+n <= i) /\
     i IN tq.t_mem ==> i IN tz.t_mem` by
    (simp_tac bool_ss [EVERY_DEF,pairTheory.UNCURRY,pairTheory.FST,pairTheory.SND] >> gen_tac >> strip_tac >>
     qpat_assum `!i. _ ==> (i IN tq.t_mem <=> i IN tz.t_mem)`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- (conj_tac
       >- ((disj1_tac >> first_assum ACCEPT_TAC) ORELSE (disj2_tac >> first_assum ACCEPT_TAC)) >>
       rpt gen_tac >> strip_tac >>
       qpat_assum `!a b n. a IN ids /\ _ ==> _` (drule_all_then ACCEPT_TAC))) >>
     disch_then (PURE_REWRITE_TAC o single o SYM) >> first_assum ACCEPT_TAC) >>
  drule_all_then (MAP_EVERY assume_tac o CONJUNCTS) abi_encode_registered_phase_frame_mods >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ q /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ q`
    (fn th => MAP_EVERY (fn rule => mp_tac (MATCH_MP rule th) >> strip_tac)
      [stmt_state_rel_local_ptrs_alloca,stmt_state_rel_allocas_below_fmp,
       stmt_state_rel_alloca_room]) >>
  `allocas_from lo q` by
    (qpat_assum `ghost_inv_at_mods _ lo d ce cx ee Gq tq q`
       (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  `q.vs_alloca_next < dimword (:256)` by (irule alloca_room_next_lt >> metis_tac[]) >>
  `st.cs_next_var <= body_end.cs_next_var` by
    (qspecl_then [`Var dst`,`src`,`type_to_abi_enc_info ce.ce_struct_fields ce ty`,`st`] mp_tac
       (cj 2 ci_mono_compile_abi_encode) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ st = _`
       (fn th => simp_tac bool_ss [th,ci_mono_def,pairTheory.SND])) >>
  `front.cs_next_id <= ready.cs_next_id /\ aid < body_end.cs_next_id /\
   front.cs_next_var <= body_end.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var /\
   s.vs_alloca_next <= q.vs_alloca_next` by decide_tac >>
  `not_fresh_at st root /\ not_fresh_at body_end root` by metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d ce body_end q` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`z`,`st`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> TRY (REFL_TAC >> NO_TAC) >>
     rpt gen_tac >> strip_tac >>
     drule_all_then ACCEPT_TAC window_phase_vars) >>
  `FLOOKUP q.vs_allocas aid = SOME (p,cap)` by
    (qpat_assum `!id row. FLOOKUP z.vs_allocas id = SOME row ==> _`
       (drule_then ACCEPT_TAC)) >>
  `lookup_var root z = SOME (n2w p)` by
    (qpat_assum `!x. not_fresh_at ready x ==> lookup_var x z = _ /\ _`
       (qspec_then `root` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `lookup_var root z = lookup_var root s` (PURE_REWRITE_TAC o single) >>
     qpat_assum `eval_operand (Var root) s = _`
       (ACCEPT_TAC o REWRITE_RULE[eval_operand_def])) >>
  `lookup_var root q = SOME (n2w p)` by (drule_all_then ACCEPT_TAC window_phase_vars) >>
  `ptr_covers Gq tq root q cap` by
    (`ptr_covers Gz tz root z cap` by
       (qpat_assum `!x n. not_fresh_at ready x /\ ptr_covers G tn x s n ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP Gq x = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `ptr_covers Gz tz root z cap` mp_tac >>
     PURE_REWRITE_TAC[ptr_covers_def] >>
     qpat_assum `lookup_var root z = SOME _` (PURE_REWRITE_TAC o single) >>
     qpat_assum `lookup_var root q = SOME _` (PURE_REWRITE_TAC o single) >>
     qpat_assum `FLOOKUP Gq root = FLOOKUP Gz root` (PURE_REWRITE_TAC o single) >>
     qpat_assum `op_taint tq (Var root) = op_taint tz (Var root)` (PURE_REWRITE_TAC o single) >>
     disch_then ACCEPT_TAC) >>
  (* Restrict the unwrap frame to the caller front, then compose. *)
  `!x. not_fresh_at front x ==> not_fresh_at ready x` by metis_tac[not_fresh_at_mono] >>
  `pure_frame ce func ee front s z` by
    (qpat_assum `pure_frame ce func ee ready s z`
       (strip_assume_tac o REWRITE_RULE[pure_frame_def]) >>
     PURE_REWRITE_TAC[pure_frame_def] >> conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!off len. _ ==> mem_bytes_at off len z.vs_memory = _` irule >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ _ _` irule >>
     qexists_tac `inst` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac) >>
  `wb_frame ce ee ee front s z` by
    (qpat_assum `wb_frame ce ee ee ready s z`
       (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >>
     PURE_REWRITE_TAC[wb_frame_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (rpt gen_tac >> strip_tac >>
         qpat_assum `!x. not_fresh_at front x ==> _` (drule_then assume_tac) >>
         qpat_assum `!x w. not_fresh_at ready x /\ _ ==> _` (drule_all_then ACCEPT_TAC)) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id off sz. _ ==> mem_bytes_at off sz z.vs_memory = _` irule >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid'` >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce ee front G tn s Gz tz` by
    (qpat_assum `ghost_kept_at lo ce ee ready G tn s Gz tz`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     PURE_REWRITE_TAC[ghost_kept_at_def] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (gen_tac >> disch_tac >>
         qpat_assum `!x. not_fresh_at front x ==> _` (drule_then assume_tac) >>
         qpat_assum `!x. not_fresh_at ready x ==> FLOOKUP Gz x = _ /\ _` (drule_then ACCEPT_TAC)) >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!id off sz i. FLOOKUP s.vs_allocas id = SOME (off,sz) /\ _ ==> i IN tn.t_mem`
       (qspecl_then [`aid'`,`off`,`sz`,`i`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac)) >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
    abi_encode_saved_row_mods lo ce cx sa ready e saved v si sm ss vv copy H ee G tn s /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `pure_frame ce func ee front s q /\ wb_frame ce ee ee front s q` by
    (irule abi_encode_saved_frames_trans >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qexistsl_tac [`front`,`z`] >> rpt conj_tac >>
         TRY (first_assum ACCEPT_TAC >> NO_TAC) >> decide_tac) >>
     qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`ctx`,`cx`] >> first_assum ACCEPT_TAC) >>
  `wb_frame ce ee ee front s q /\ ghost_kept_at lo ce ee front G tn s Gq tq /\
   (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tq))` by
    (match_mp_tac (Q.INST [`u` |-> `z`, `st` |-> `front`, `Gu` |-> `Gz`, `tu` |-> `tz`,
       `H` |-> `storage_trace_horizon ee.storage_trace`] extcall_direct_row_frame_trans) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp_tac bool_ss [LESS_EQ_REFL]) >>
  (* The selector prefix is in the registered result, outside the
     encoder's payload window and every registered scratch allocation. *)
  `!i. p+32 <= i /\ i < addr ==> !a b n. a IN ids /\
    FLOOKUP q.vs_allocas a = SOME (b,n) ==> i < b \/ b+n <= i` by
    (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
     `st.cs_next_id <= a` by
       (qpat_assum `a IN ids` mp_tac >>
        simp_tac bool_ss [Abbr `ids`, window_alloca_sites_def,
          abiEncoderPropsTheory.frag_ids_def, IN_GSPEC_IFF] >>
        disch_then strip_assume_tac >> first_assum ACCEPT_TAC) >>
     `a <> aid` by decide_tac >>
     qpat_assum `alloca_inv q` (strip_assume_tac o REWRITE_RULE[alloca_inv_def]) >>
     qpat_assum `allocas_non_overlapping q`
       (mp_tac o Q.SPECL [`a`,`aid`,`b`,`n`,`p`,`cap`] o REWRITE_RULE[allocas_non_overlapping_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >> qpat_x_assum `Abbrev (addr = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     decide_tac) >>
  `mem_bytes_at (p+32) k q.vs_memory = abi_encode_method_id_bytes mid` by
    (`mem_bytes_at (p+32) k q.vs_memory = mem_bytes_at (p+32) k z.vs_memory` by
       (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> gen_tac >> strip_tac >>
        `i < addr` by (simp_tac bool_ss [Abbr `addr`] >> first_assum ACCEPT_TAC) >>
        qpat_assum `window_phase ctx func st body_end ids _ z q`
          (MAP_EVERY assume_tac o CONJUNCTS o
            REWRITE_RULE[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def] o
           MATCH_MP window_phase_effect) >>
        qpat_assum `!a. EVERY _ _ /\ _ ==> mem_bytes_at a 1 q.vs_memory = _`
          (qspec_then `i` mp_tac) >>
        (impl_tac >- (conj_tac
         >- (simp_tac list_ss [] >> disj1_tac >> first_assum ACCEPT_TAC) >>
         qpat_assum `!i. p+32 <= i /\ i < addr ==> !a b n. _` (qspec_then `i` mp_tac) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `read_memory (p+32) k z = _`
       (assume_tac o REWRITE_RULE[read_memory_eq_mem_bytes_at]) >>
     qpat_assum `mem_bytes_at (p+32) k q.vs_memory = mem_bytes_at _ _ _`
       (PURE_REWRITE_TAC o single) >> first_assum ACCEPT_TAC) >>
  `!i. p+32 <= i /\ i < addr + LENGTH bytes ==> i NOTIN tq.t_mem` by
    (gen_tac >> strip_tac >> Cases_on `i < addr`
     >- (strip_tac >>
         qpat_assum `!i. p+32 <= i /\ i < addr ==> i NOTIN tz.t_mem`
           (drule_all_then mp_tac) >>
         qpat_assum `!i. EVERY _ _ /\ _ ==> i IN tz.t_mem` (qspec_then `i` mp_tac) >>
         (impl_tac >- (rpt conj_tac
          >- (simp_tac list_ss [] >> disj1_tac >> first_assum ACCEPT_TAC)
          >- (qpat_assum `!i. p+32 <= i /\ i < addr ==> !a b n. _` (qspec_then `i` mp_tac) >>
              (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC)
          >> first_assum ACCEPT_TAC)) >>
         simp_tac bool_ss []) >>
     `addr <= i` by (simp_tac bool_ss [GSYM NOT_LESS] >> first_assum ACCEPT_TAC) >>
     qpat_assum `!i. addr <= i /\ _ ==> i NOTIN tq.t_mem` (drule_all_then ACCEPT_TAC)) >>
  `eval_operand (Var root) q = SOME (n2w p)` by
    (PURE_REWRITE_TAC[eval_operand_def] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bytes`,`limit`,`q`,`Gq`,`tq`] >>
  qpat_x_assum `Abbrev (addr = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee q /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
