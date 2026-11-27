(* Select the original byte string and the allocation endpoint before copying. *)
Theory bodyCreateRawSnapshotSelectMods
Ancestors
  bodyCreateRawReachedMods bodyCreateRawAllocMods bodyCopyReadPhysicalTypeMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyMemoryDefs bodyPtrDefs
  exprSimHypsDefs exprLowering exprLoweringProps exprSimCopy abiValueEncoding
  loweringPosts loweringStateRelDefs stateRelProj compileEnv emitHelper context
  fragGasOriginPtr ptrDiscipline vyperStorageFootprint vyperState vyperValue
  gasExplicitSites venomInst venomState venomExecSemantics finite_map words
Libs monadsyntax

Theorem snapshot_bytes_type_evals[local]:
  expr_body_pre_mods mods cenv cx env code es /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  lowered_value_type cenv code = BaseT (BytesT (Dynamic k)) /\
  bind (eval_expr cx code) (read_result cx) (es with gas_obs := obs) = (INL v,ee) ==>
  post_value_type cenv code = expr_type code /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic bound))) =
    SOME (BaseTV (BytesT (Dynamic bound))) /\
  evaluate_type (get_tenv cx) (post_value_type cenv code) =
    SOME (BaseTV (BytesT (Dynamic bound))) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv code) =
    SOME (BaseTV (BytesT (Dynamic k)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type cenv code = expr_type code` by
    simp[post_value_type_bytestring,is_bytestring_type_def] >>
  `~is_word_type (expr_type code)` by simp[is_word_type_def] >>
  drule_all_then (qx_choosel_then [`pt`,`rt`] (map_every assume_tac o CONJUNCTS) o
                  CONJUNCT2 o CONJUNCT2) copy_read_physical_type_gas_obs_mods >>
  qpat_x_assum `evaluate_type _ (post_value_type _ _) = SOME pt` mp_tac >>
  qpat_x_assum `evaluate_type _ (lowered_value_type _ _) = SOME rt` mp_tac >>
  asm_rewrite_tac[] >> rpt disch_tac >>
  qpat_assum `evaluate_type _ _ = SOME pt`
    (mp_then Any SUBST_ALL_TAC evaluate_type_base_result) >>
  qpat_assum `evaluate_type _ _ = SOME rt`
    (mp_then Any SUBST_ALL_TAC evaluate_type_base_result) >> asm_rewrite_tac[]
QED

Theorem snapshot_old_operand[local]:
  j.vs_labels = t.vs_labels /\
  (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)) ==>
  !op. copy_old_operand a op ==>
    copy_old_operand m op /\ eval_operand op j = eval_operand op t /\
    op_taint tj op = op_taint tn1 op /\ op_prov Gj op = op_prov G1 op
Proof
  strip_tac >> Cases >> simp[copy_old_operand_def,eval_operand_def,op_taint_def,op_prov_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

val reached = ``!H. valid_horizon cx st0 H ee.storage_trace ==>
  vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
  vv_store_bound cx (post_value_type cenv code) (lowered_value_type cenv code) ee raw vv t /\
  t.vs_current_bb = a.cs_current_bb /\ t.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
  gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1)``;

Theorem raw_create_snapshot_select_mods:
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env code es /\
  expr_type code = BaseT (BytesT (Dynamic bound)) /\
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  compile_create_snapshot cenv vv (lowered_value_type cenv code) a = (snap,b) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  return_buf_frame d cenv sa s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ee.gas_obs = [] /\ ~t.vs_halted /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. eval_expr cx code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL raw,ee with gas_obs := tail)) /\
  read_result cx raw ee = (INL v,ee) /\
  (!tail. bind (eval_expr cx code) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  (^reached) ==>
  ?bs k cap buf m site owner pbase j Gj tj.
    v = BytesV bs /\ lowered_value_type cenv code = BaseT (BytesT (Dynamic k)) /\
    LENGTH bs <= k /\ k <= bound /\
    cap = type_memory_bytes cenv (lowered_value_type cenv code) /\
    32 + LENGTH bs <= cap /\ cap = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    cap < 2 ** 64 /\ cap < dimword (:256) /\
    post_value_type cenv code = expr_type code /\
    evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic bound))) =
      SOME (BaseTV (BytesT (Dynamic bound))) /\
    evaluate_type (get_tenv cx) (post_value_type cenv code) =
      SOME (BaseTV (BytesT (Dynamic bound))) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv code) =
      SOME (BaseTV (BytesT (Dynamic k))) /\
    vv_location vv <> SOME LocCalldata /\
    (!loc. vv_location vv = SOME loc /\ loc <> LocMemory ==>
      vv_type vv = lowered_value_type cenv code /\
      32 * ((type_memory_bytes cenv (vv_type vv) + 31) DIV 32) = cap) /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> valid_horizon cx st0 H es.storage_trace) /\
    ci_mono sa a /\ local_ptrs_reserved cenv a /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\ (!l. vv_operand vv <> Label l) /\
    wb_frame cenv es ee sa s t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    return_buf_frame d cenv a t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) /\
    read_result cx raw ee = (INL (BytesV bs),ee) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (BytesV bs),ee with gas_obs := tail)) /\
    (^reached) /\
    valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace /\
    vv_post_mods (storage_trace_horizon ee.storage_trace) ctx func cenv cx code es sa a s ee raw vv t /\
    vv_store_bound cx (post_value_type cenv code) (lowered_value_type cenv code) ee raw vv t /\
    ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx raw ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    ghost_inv_at_mods (DF (storage_trace_horizon ee.storage_trace)) lo d cenv cx ee G1 tn1 t /\
    compile_alloc_buffer cap a = (buf,m) /\ snap = buf.buf_operand /\
    buf.buf_operand = Var owner /\ ci_mono a m /\ ci_mono m b /\
    fn_has_code a m func /\ fn_has_code m b func /\
    ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
      ?len l size c.
        emit_op MLOAD [vv_operand vv] m = (len,l) /\
        emit_op ADD [len;Lit 32w] l = (size,c) /\
        compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) size c = ((),b) /\
        ci_mono m l /\ ci_mono l c /\ ci_mono c b /\
        fn_has_code m l func /\ fn_has_code l c func /\ fn_has_code c b func) /\
    (!loc. vv_location vv = SOME loc /\ (loc = LocStorage \/ loc = LocTransient) ==>
      ?lab. compile_slot_to_memory (vv_operand vv) buf.buf_operand
        ((cap+31) DIV 32) loc m = (lab,b)) /\
    (vv_location vv = SOME LocCode ==>
      compile_imm_copy_to_memory cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
        buf.buf_operand ((type_memory_bytes cenv (vv_type vv)+31) DIV 32) 0 m = ((),b)) /\
    site = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [owner] /\
    MEM site (fn_insts func) /\ site.inst_id = a.cs_next_id /\
    site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
    not_local_ptr cenv ee.scopes owner /\ not_fresh_at m owner /\ not_fresh_at b owner /\
    ((FLOOKUP t.vs_allocas a.cs_next_id = NONE /\ pbase = t.vs_alloca_next) \/
      FLOOKUP t.vs_allocas a.cs_next_id = SOME (pbase,cap)) /\
    FLOOKUP j.vs_allocas a.cs_next_id = SOME (pbase,cap) /\
    lookup_var owner j = SOME (n2w pbase) /\ eval_operand snap j = SOME (n2w pbase) /\
    FLOOKUP Gj owner = SOME (pbase,cap) /\ op_taint tj (Var owner) = {} /\
    ptr_covers Gj tj owner j cap /\ lo <= pbase /\ pbase+cap < dimword (:256) /\
    pbase+cap <= j.vs_alloca_next /\ t.vs_alloca_next <= j.vs_alloca_next /\
    allocas_from lo j /\ lo <= j.vs_alloca_next /\ alloca_history func j /\ alloca_inv j /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\ return_buf_frame d cenv m j /\
    ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\ j.vs_inst_idx = LENGTH m.cs_current_insts /\
    j with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
            vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
    j.vs_memory = t.vs_memory /\ j.vs_data_section = t.vs_data_section /\
    j.vs_call_ctx = t.vs_call_ctx /\ j.vs_accounts = t.vs_accounts /\
    j.vs_transient = t.vs_transient /\ j.vs_immutables = t.vs_immutables /\
    j.vs_initial_fmp = t.vs_initial_fmp /\ j.vs_fmp = t.vs_fmp /\ j.vs_labels = t.vs_labels /\
    (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
         FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)) /\
    (!op. copy_old_operand a op ==> copy_old_operand m op /\ eval_operand op j = eval_operand op t /\
      op_taint tj op = op_taint tn1 op /\ op_prov Gj op = op_prov G1 op) /\
    (!aid ent. FLOOKUP t.vs_allocas aid = SOME ent ==> FLOOKUP j.vs_allocas aid = SOME ent) /\
    (!aid off sz. FLOOKUP j.vs_allocas aid = SOME (off,sz) ==>
         FLOOKUP t.vs_allocas aid = SOME (off,sz) \/ t.vs_alloca_next <= off) /\
    (!name off sz. local_region cenv ee.scopes j name off sz <=> local_region cenv ee.scopes t name off sz) /\
    (!name off sz. local_region cenv ee.scopes j name off sz ==> regions_disjoint pbase cap off sz) /\
    (!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
         regions_disjoint pbase cap off sz) /\
    tj.t_stor = tn1.t_stor /\ tj.t_trans = tn1.t_trans /\ tj.t_imm = tn1.t_imm /\
    (!i. i IN tj.t_mem <=> i IN tn1.t_mem \/ (t.vs_alloca_next <= i /\ i < pbase+cap)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee j /\ immutable_frame_mods func cenv cx ee j /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gj tj j /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK j,Gj,tj))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\ s.vs_alloca_next <= t.vs_alloca_next` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ vv_store_bound _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> asm_rewrite_tac[]) >>
  drule_all_then (qx_choosel_then [`bs`,`k`] (map_every assume_tac o CONJUNCTS))
    raw_create_reached_bytes_mods >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) snapshot_bytes_type_evals >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ vv_store_bound _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `cap = type_memory_bytes cenv (lowered_value_type cenv code)` >>
  `cap = type_memory_bytes cenv (lowered_value_type cenv code)` by
    simp[NoAsms, Abbr `cap`] >>
  `compile_create_snapshot cenv vv (BaseT (BytesT (Dynamic k))) a = (snap,b)` by
    (qpat_assum `lowered_value_type cenv code = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `cap = type_memory_bytes cenv (BaseT (BytesT (Dynamic k)))` by
    (qpat_assum `lowered_value_type cenv code = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  drule_all (CONV_RULE (DEPTH_CONV BETA_CONV) raw_create_snapshot_alloc_mods) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`buf`,`m`,`site`,`owner`,`pbase`,`j`,`Gj`,`tj`]
      (map_every assume_tac o CONJUNCTS))) >>
  `alloca_inv j` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ j /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     drule_then (assume_tac o CONJUNCT2) stmt_state_rel_local_ptrs_alloca >>
     first_assum ACCEPT_TAC) >>
  `j.vs_labels = t.vs_labels` by
    (qpat_assum `j with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = t`
       (mp_tac o AP_TERM ``\z. z.vs_labels``) >> simp[]) >>
  qexistsl_tac [`bs`,`k`,`cap`,`buf`,`m`,`site`,`owner`,`pbase`,`j`,`Gj`,`tj`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE REFL_TAC ORELSE conj_tac)
  >- (qpat_assum `v = BytesV bs` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `v = BytesV bs` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  irule snapshot_old_operand >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists `a` >> conj_tac >> first_assum ACCEPT_TAC
QED
