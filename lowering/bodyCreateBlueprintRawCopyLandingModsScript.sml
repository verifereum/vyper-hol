(* Materialized raw blueprint argument: one linked landing and retained window. *)
Theory bodyCreateBlueprintRawCopyLandingMods
Ancestors
  bodyCreateBlueprintRawTypeMods bodyCreateBlueprintRawCopyEntryMods
  bodyCreateBlueprintRawCopyStoreMods bodyCreateBlueprintRawHeaderMods
  bodyCreateBlueprintRawOwnedMods bodyFullIfExpReach bodyFullPostsMods
  fragGasOriginPtrLoop wordArgsPtr exprSimWordArgs exprOperandVar
  stmtLoweringMono loweringHalt fragExec exprLowering exprLoweringProps typeLayoutProps
  exprSimHyps exprSimHypsDefs allocLimits bodyMemoryDefs bodyPtrDefs
  bodyFullShadowBodyInv loweringPosts loweringStateRelDefs vyperStorageFootprint
  vyperInterpreter vyperState vyperTyping valueEncoding context compileEnv finite_map words

Theorem blueprint_raw_copy_landing_mods:
  expr_body_pre_mods mods ce cx env e es /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce T vv sm = (saved,sd) /\
  unwrap_value ce saved sd = (op,su) /\
  emit_op MLOAD [op] su = (cnt,sn) /\
  emit_op ADD [op;Lit 32w] sn = (data,sb) /\
  fn_has_code sm sd func /\ fn_has_code su sn func /\ fn_has_code sn sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo ce es sa Gi ti s0 G tn /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bs h Gh th.
    v = BytesV bs /\ LENGTH bs < 2 ** 64 /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK h,Gh,th) /\
      stmt_state_rel H ctx func ce cx ee h /\ immutable_frame_mods func ce cx ee h /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gh th h) /\
    wb_frame ce es ee sa s0 h /\ ghost_kept_at lo ce es sa Gi ti s0 Gh th /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ s0.vs_alloca_next <= h.vs_alloca_next /\
    alloca_history func h /\ return_buf_frame d ce sb h /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp h) /\
    (!fn i z. frag_reachable ctx func h fn i z ==> dalloca_fmp_headroom i z) /\
    ~h.vs_halted /\ h.vs_current_bb = sb.cs_current_bb /\ h.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x) /\
    (!ef Gf tf f.
      wb_frame ce ee ef sb h f /\ ghost_kept_at lo ce ee sb Gh th h Gf tf /\
      h.vs_alloca_next <= f.vs_alloca_next ==>
      eval_operand cnt f = SOME (n2w (LENGTH bs)) /\ op_taint tf cnt = {} /\ op_prov Gf cnt = NONE /\
      (cnt <> Lit 0w ==> ?q a. data = Var q /\ lookup_var q f = SOME a /\
        ptr_covers Gf tf q f (LENGTH bs) /\ (bs = [] \/ w2n a + LENGTH bs <= f.vs_alloca_next) /\
        (!i. w2n a <= i /\ i < w2n a + LENGTH bs ==> i NOTIN tf.t_mem) /\
        read_memory (w2n a) (LENGTH bs) f = bs))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[Once bind_def] >>
  drule_all blueprint_raw_read_tag_mods >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (qx_choosel_then [`bs`,`lk`,`dk`] (map_every assume_tac o CONJUNCTS)))))) >>
  qpat_x_assum `v = BytesV bs` SUBST_ALL_TAC >>
  `?buf si src sc.
     compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) sm = (buf,si) /\
     unwrap_value ce vv si = (src,sc) /\
     compile_store_memory ce src buf.buf_operand (vv_type vv) (vv_type vv) sc = ((),sd) /\
     saved = LocatedValue (vv_type vv) (mk_ptr buf.buf_operand LocMemory) /\
     op = buf.buf_operand /\ su = sd` by suspend "placement" >>
  qpat_x_assum `su = sd` SUBST_ALL_TAC >>
  qpat_x_assum `op = buf.buf_operand` SUBST_ALL_TAC >>
  `ci_mono sa sm /\ ci_mono sm si /\ ci_mono si sc /\ ci_mono sc sd /\
   ci_mono sd sn /\ ci_mono sn sb` by suspend "ranges" >>
  `fn_has_code sm si func /\ fn_has_code si sc func /\ fn_has_code sc sd func` by suspend "code" >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[Abbr `H0`,storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func ce cx es s0` by simp[] >>
  qpat_assum `!H. _ ==> vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes /\ allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[vv_post_mods_def,locals_kept_def,ghost_inv_at_mods_def] >>
  suspend "entry"
QED

Resume blueprint_raw_copy_landing_mods[placement]:
  Cases_on `compile_alloc_buffer (type_memory_bytes ce (vv_type vv)) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,si)` >>
  Cases_on `unwrap_value ce vv si` >>
  rename1 `unwrap_value ce vv si = (src,sc)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand (vv_type vv) (vv_type vv) sc` >>
  rename1 `compile_store_memory _ src _ _ _ sc = (u,sd')` >>
  Cases_on `u` >>
  qpat_x_assum `compile_snapshot_vv ce T vv sm = _` mp_tac >>
  simp[compile_snapshot_vv_def,compile_materialize_vv_def,comp_bind_def,comp_return_def,
       comp_ignore_bind_def] >>
  strip_tac >> gvs[unwrap_value_def,mk_ptr_def,comp_return_def] >>
  qexistsl [`buf`,`si`,`src`,`sc`] >> simp[]
QED

Resume blueprint_raw_copy_landing_mods[ranges]:
  mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`,`sa`] (cj 1 ci_mono_compile_expr_sa)) >>
  mp_tac (Q.SPECL [`type_memory_bytes ce (vv_type vv)`,`sm`] ci_mono_compile_alloc_buffer) >>
  mp_tac (Q.SPECL [`ce`,`vv`,`si`] ci_mono_unwrap_value) >>
  mp_tac (Q.SPECL [`ce`,`src`,`buf.buf_operand`,`vv_type vv`,`vv_type vv`,`sc`] ci_mono_compile_store_memory) >>
  mp_tac (Q.SPECL [`MLOAD`,`[buf.buf_operand]`,`sd`] ci_mono_emit_op) >>
  mp_tac (Q.SPECL [`ADD`,`[buf.buf_operand;Lit 32w]`,`sn`] ci_mono_emit_op) >>
  asm_rewrite_tac[pairTheory.SND] >> rpt strip_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_raw_copy_landing_mods[code]:
  `ci_mono si sd` by metis_tac[ci_mono_trans] >>
  qspecl_then [`sm`,`si`,`sd`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- fs[ci_mono_def]) >> strip_tac >>
  qspecl_then [`si`,`sc`,`sd`,`func`] mp_tac fn_has_code_split >>
  (impl_tac >- fs[ci_mono_def]) >> simp[]
QED

Resume blueprint_raw_copy_landing_mods[entry]:
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w` by
    (qpat_assum `vv_post_mods H0 ctx func ce cx e es sa sm s0 ee tv vv s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d ce sm s` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  `~is_word_type (post_value_type ce e) /\
   is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)` by
    simp[is_word_type_def,is_bytestring_type_def] >>
  `!t op0. vv = StackValue t op0 ==> ptr_buf_ok ce e op0 G s` by simp[] >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size (BaseTV (BytesT (Dynamic cap)))` by
    (fs[] >> metis_tac[type_memory_bytes_base_evaluated]) >>
  `type_memory_size (BaseTV (BytesT (Dynamic cap))) < 2**64` by
    (`alloc_limits_expr ce e` by fs[expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def,is_word_type_def] >>
     metis_tac[]) >>
  `0 < type_memory_size (BaseTV (BytesT (Dynamic lk)))` by decide_tac >>
  `type_memory_bytes ce (vv_type vv) < dimword (:256)` by fs[dimword_def] >>
  qpat_assum `compile_expr ce _ e sa = _`
    (mp_then Any mp_tac blueprint_raw_copy_entry_mods) >>
  disch_then (fn th => qpat_assum `compile_alloc_buffer _ sm = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `unwrap_value ce vv si = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `read_result cx tv ee = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo ce es sa Gi ti s0 G tn`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (post_value_type ce e) = _`
    (mp_then (Pat `evaluate_type _ (post_value_type _ _) = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (lowered_value_type ce e) = _`
    (mp_then (Pat `evaluate_type _ (lowered_value_type _ _) = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H0 ctx func ce cx es s0`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `return_buf_frame d ce sm s`
    (mp_then Any mp_tac th)) >>
  disch_then (qspecl_then [`st0`,`explicit`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`dst`,`dw`,`z`,`Gz`,`tz`,`srcvar`,`sw`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "store"
QED

Resume blueprint_raw_copy_landing_mods[store]:
  qpat_x_assum `src = Var srcvar` SUBST_ALL_TAC >>
  qpat_assum `buf.buf_operand = Var dst` (fn eq =>
    rule_assum_tac (REWRITE_RULE [eq]) >> assume_tac eq) >>
  `ci_mono sa sc /\ ci_mono sa sd /\ ci_mono sd sb` by metis_tac[ci_mono_trans] >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_var <= sd.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ si.cs_next_id <= sc.cs_next_id` by fs[ci_mono_def] >>
  `sm.cs_next_id < sc.cs_next_id` by
    (drule compile_alloc_buffer_parts >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved ce sc /\ local_ptrs_reserved ce sd` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee z /\ immutable_frame_mods func ce cx ee z /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def])) >>
     asm_rewrite_tac[]) >>
  `wb_frame ce es ee sa s0 z` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
       (drule_then (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
     drule_then ACCEPT_TAC expr_post_frame) >>
  suspend "write"
QED

Resume blueprint_raw_copy_landing_mods[write]:
  qpat_assum `compile_store_memory ce _ (Var dst) _ _ sc = _`
    (mp_then Any mp_tac
      (Q.INST [`sty` |-> `lowered_value_type ce e`, `cap` |-> `dk`,
               `aid` |-> `sm.cs_next_id`] blueprint_raw_copy_store_mods)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (vv_type vv) = _`
    (mp_then (Pat `evaluate_type _ (vv_type vv) = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `evaluate_type _ (lowered_value_type ce e) = _`
    (mp_then (Pat `evaluate_type _ (lowered_value_type _ _) = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var dst z = SOME dw`
    (mp_then (Pat `lookup_var dst _ = _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `lookup_var srcvar z = SOME sw`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `return_buf_frame d ce sc z`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_kept_at lo ce es sa Gi ti s0 Gz tz`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `fn_has_code sc sd func`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `storage_trace_domain cx st0 ee.storage_trace`
    (mp_then Any mp_tac th)) >>
  disch_then (qspec_then `sm` (qspecl_then [`explicit`,`dk`,`ctx`] mp_tac)) >>
  disch_then (qspecl_then [`bs`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (
    qpat_assum `type_memory_bytes ce (vv_type vv) = _`
      (fn eq => rule_assum_tac (REWRITE_RULE [eq]) >> rewrite_tac[eq]) >>
    rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "header"
QED

Resume blueprint_raw_copy_landing_mods[header]:
  `gas_origin_ptr_path (DF H0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by
    (qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `gas_origin_ptr_path (DF H0,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)` by
    (irule gas_origin_ptr_path_trans >> qexistsl [`Gz`,`z`,`tz`] >> simp[]) >>
  `!fn i r. frag_reachable ctx func u fn i r ==> dalloca_fmp_headroom i r` by
    (rpt gen_tac >> disch_tac >>
     irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path (DF H0,_,_,_,_,_) (s,G,tn) [] (OK u,Gu,tu)`
       (irule_at Any) >> goal_assum (drule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `emit_op MLOAD _ _ = _`)
    (PURE_REWRITE_RULE [n2w_w2n]
       (Q.INST [`b` |-> `w2n (dw:bytes32)`] blueprint_raw_header_frame_mods)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `mload (w2n dw) u = _`)) >>
  disch_then (drule_at (Pat `ptr_covers Gu tu dst u (32 + LENGTH bs)`)) >>
  disch_then (drule_at (Pat `fn_has_code sd sn func`)) >>
  disch_then (drule_at (Pat `return_buf_frame d ce sd u`)) >>
  disch_then (drule_at (Pat `storage_trace_domain cx st0 ee.storage_trace`)) >>
  disch_then (qspecl_then [`lo`,`ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`l`,`q`,`h`,`Gh`,`th`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "finish"
QED

Resume blueprint_raw_copy_landing_mods[finish]:
  `sa.cs_next_id <= sd.cs_next_id` by fs[ci_mono_def] >>
  `wb_frame ce es ee sa s0 h` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     qpat_assum `wb_frame ce ee ee sd u h` (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s0` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo ce es sa Gi ti s0 Gh th` by
    (irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo ce ee sd Gu tu u Gh th` (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s0` (irule_at Any) >>
     qexists `ee` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s0.vs_alloca_next <= h.vs_alloca_next` by simp[] >>
  `!x. data = Var x \/ cnt = Var x ==> not_fresh_at sb x` by
    (gen_tac >> simp[] >> disch_then (DISJ_CASES_THEN (SUBST1_TAC o SYM)) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK h,Gh,th) /\
    stmt_state_rel H ctx func ce cx ee h /\ immutable_frame_mods func ce cx ee h /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gh th h` by
    suspend "path" >>
  qexistsl [`bs`,`h`,`Gh`,`th`] >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  suspend "window"
QED

Resume blueprint_raw_copy_landing_mods[path]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func ce cx ee h /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >>
      reverse conj_tac >- simp[] >>
      irule gas_origin_ptr_path_trans >> qexistsl [`Gz`,`z`,`tz`] >> simp[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_raw_copy_landing_mods[window]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func ce cx ee u /\ _`
       (drule_then strip_assume_tac) >> fs[Abbr `H0`]) >>
  `32 + LENGTH bs <= type_memory_size (BaseTV (BytesT (Dynamic dk)))` by
    (mp_tac (Q.SPEC `dk` abiBuiltinAllocationTheory.abi_builtin_word_size_capacity) >>
     simp[type_memory_size_def] >> decide_tac) >>
  `w2n dw + type_memory_size (BaseTV (BytesT (Dynamic dk))) <= u.vs_alloca_next /\
   u.vs_alloca_next <= h.vs_alloca_next` by simp[] >>
  `compile_snapshot_vv ce T vv sm = (LocatedValue (vv_type vv) (mk_ptr (Var dst) LocMemory),sd)` by
    metis_tac[] >>
  qpat_assum `cnt = Var l` (fn eq =>
    map_every (fn pat => qpat_assum pat (assume_tac o REWRITE_RULE [eq]))
      [`eval_operand cnt h = _`, `op_taint th cnt = _`, `op_prov Gh cnt = _`]) >>
  qpat_assum `data = Var q` (fn eq =>
    qpat_assum `eval_operand data h = _` (assume_tac o REWRITE_RULE [eq])) >>
  drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`) blueprint_raw_owned_window_mods >>
  disch_then (drule_at (Pat `ptr_val_ok cx _ (BytesV bs) (Var dst) Gu tu u`)) >>
  disch_then (drule_at (Pat `ghost_kept_at lo ce ee sd Gu tu u Gh th`)) >>
  disch_then (drule_at (Pat `ghost_kept_at lo ce ee sb Gh th h Gf tf`)) >>
  disch_then (drule_at (Pat `ptr_covers Gh th q h (LENGTH bs)`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (vv_type vv) = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP u.vs_allocas sm.cs_next_id = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ ctx func ce cx ee u`)) >>
  disch_then (drule_at (Pat `wb_frame ce ee ef sb h f`)) >>
  disch_then (qspecl_then [`l`,`data`,`cnt`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED

Finalise blueprint_raw_copy_landing_mods
