(* Word snapshots reuse the original compiled value's unwrap path. *)
Theory bodyFullExtCallRequestSnapshotWord
Ancestors
  bodyFullExtCallRequestSnapshot exprSimHypsDefs exprSimHyps
  aggregateEvaluatedLayout loweringPosts exprLowering context compileEnv
  exprSimUnwrap valueEncodingProofs valueEncodingDefs valueCopyBytes
  exprPtrUnwrapFacts abiStaticAggregateProps

Theorem extcall_request_word_snapshot_unwrap:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  vv_holds ce cx (post_value_type ce e) tv vv ee s /\
  is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) ==>
  compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) =
    comp_bind (unwrap_value ce vv)
      (\op. comp_return
        (StackValue (vv_type (ext_call_arg_value (lowered_value_type ce e) vv)) op))
Proof
  strip_tac >> Cases_on `vv`
  >- gvs[ext_call_arg_value_def, compile_snapshot_vv_def] >>
  rename1 `LocatedValue tag p` >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `is_word_type (expr_type e)` by
    (gvs[ext_call_arg_value_def, vv_type_def] >>
     metis_tac[arg_type_fits_word_type]) >>
  gvs[vv_holds_def, ext_call_arg_value_def, vv_type_def,
      compile_snapshot_vv_def, unwrap_value_def,
      is_bytestring_type_def, is_word_type_def] >>
  Cases_on `expr_type e` >> gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  rename1 `BytesT bs` >> Cases_on `bs` >>
  gvs[is_bytestring_type_def, is_word_type_def]
QED

Theorem extcall_request_word_snapshot_marked_horizons:
  !ctx func cenv cx e es sa sm sb s0 ee tv vv snap s st0 tr H0.
    post_value_type cenv e = expr_type e /\
    compile_snapshot_vv cenv F
      (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (snap, sb) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
           ~is_word_type (expr_type e) ==>
           type_memory_bytes cenv (expr_type e) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
    (!H. valid_horizon cx st0 H tr ==>
       vv_post H ctx func cenv cx e es sa sm s0 ee tv vv s) /\
    valid_horizon cx st0 H0 tr /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) ==>
    ?op v u.
      snap = StackValue
        (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv)) op /\
      gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
        [] (INL v) ee (OK u) /\
      (!H. valid_horizon cx st0 H tr ==>
         expr_post H ctx func cenv cx e es sa sb s0 ee v op u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee s` by
    metis_tac[vv_post_def] >>
  drule_all extcall_request_word_snapshot_unwrap >> disch_then (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qpat_x_assum `comp_bind _ _ sm = _` mp_tac >>
  simp[comp_bind_def, comp_return_def] >>
  Cases_on `unwrap_value cenv vv sm` >>
  rename1 `unwrap_value cenv vv sm = (op, su)` >>
  strip_tac >> gvs[] >>
  irule unwrap_value_marked_read_horizons >>
  simp[] >> conj_tac
  >- (qexistsl_tac [`sm`, `vv`] >> simp[]) >>
  metis_tac[]
QED

Theorem extcall_capture_memory_bytes_frame:
  !ce cx ty sa sb es raw tag p s v tv w func cut ee u.
    vv_at ce cx ty sa sb es raw (LocatedValue tag p) s /\
    p.ptr_location = LocMemory /\
    read_result cx raw es = (INL v,es) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand p.ptr_operand s = SOME w /\
    wb_frame ce es ee sb s u /\
    pure_frame ce func es cut s u ==>
    mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[pure_frame_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        metis_tac[] >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem extcall_capture_expr_val_bytes_frame:
  !ce cx src sa sb ee v op s sv w ef func cut u.
    expr_val_at ce cx src sa sb ee v op s /\
    evaluate_type (get_tenv cx) src = SOME sv /\
    ~is_word_type src /\ eval_operand op s = SOME w /\
    wb_frame ce ee ef sb s u /\ pure_frame ce func ee cut s u ==>
    mem_bytes_at (w2n w) (val_footprint sv v) u.vs_memory =
    mem_bytes_at (w2n w) (val_footprint sv v) s.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[pure_frame_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        metis_tac[] >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem extcall_capture_located_at_frame:
  !ce cx ty sa sb sc es ee raw tag p s u.
    vv_at ce cx ty sa sb es raw (LocatedValue tag p) s /\
    FST (read_result cx raw ee) = FST (read_result cx raw es) /\
    (!w. eval_operand p.ptr_operand s = SOME w ==>
         eval_operand p.ptr_operand u = SOME w) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
               FLOOKUP u.vs_allocas aid = SOME row) /\
    (!n b sz. local_region ce ee.scopes u n b sz <=>
               local_region ce es.scopes s n b sz) /\
    sb.cs_next_id <= sc.cs_next_id ==>
    vv_at ce cx ty sa sc ee raw (LocatedValue tag p) u
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `p.ptr_location = LocMemory`
  >- (gvs[vv_at_def] >> rpt strip_tac >>
      `read_result cx raw es = (INL v,es)` by
        (Cases_on `read_result cx raw es` >>
         imp_res_tac vyperStateTheory.read_result_state >> gvs[]) >>
      first_x_assum drule >> disch_then drule >> strip_tac >>
      qexists_tac `w` >> simp[]
      >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
          simp[] >> metis_tac[]) >>
      disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  gvs[vv_at_def]
QED

Theorem extcall_capture_located_memory_transport:
  !ce cx src sa sb sc ee ef raw tag p s u v sv dv w func cut.
    vv_at ce cx src sa sb ee raw (LocatedValue tag p) s /\
    p.ptr_location = LocMemory /\
    read_result cx raw ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) src = SOME sv /\
    eval_operand p.ptr_operand s = SOME w /\
    val_in_memory dv v (w2n w) s.vs_memory /\ val_wf dv v /\
    val_footprint sv v = val_footprint dv v /\
    wb_frame ce ee ef sb s u /\ pure_frame ce func ee cut s u /\
    FST (read_result cx raw ef) = FST (read_result cx raw ee) /\
    (!z. eval_operand p.ptr_operand s = SOME z ==>
         eval_operand p.ptr_operand u = SOME z) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
               FLOOKUP u.vs_allocas aid = SOME row) /\
    (!n b sz. local_region ce ef.scopes u n b sz <=>
               local_region ce ee.scopes s n b sz) /\
    sb.cs_next_id <= sc.cs_next_id ==>
    val_in_memory dv v (w2n w) u.vs_memory /\
    vv_at ce cx src sa sc ef raw (LocatedValue tag p) u
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (drule_all extcall_capture_memory_bytes_frame >> strip_tac >>
      irule exprSimPropsTheory.val_in_memory_footprint_agree >>
      simp[] >> qexists_tac `s.vs_memory` >> gvs[]) >>
  irule extcall_capture_located_at_frame >>
  qexistsl_tac [`ee`, `s`, `sb`] >> simp[]
QED

Theorem extcall_capture_stack_memory_transport:
  !ce cx src sa sb sc ee ef raw tag op s u v sv dv w func cut.
    vv_at ce cx src sa sb ee raw (StackValue tag op) s /\
    read_result cx raw ee = (INL v,ee) /\
    evaluate_type (get_tenv cx) src = SOME sv /\ ~is_word_type src /\
    eval_operand op s = SOME w /\
    val_in_memory dv v (w2n w) s.vs_memory /\ val_wf dv v /\
    val_footprint sv v = val_footprint dv v /\
    wb_frame ce ee ef sb s u /\ pure_frame ce func ee cut s u /\
    FST (read_result cx raw ef) = FST (read_result cx raw ee) /\
    eval_operand op u = SOME w /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
               FLOOKUP u.vs_allocas aid = SOME row) /\
    ef.scopes = ee.scopes /\
    (!n b sz. local_region ce ee.scopes s n b sz <=>
               local_region ce ee.scopes u n b sz) /\
    sb.cs_next_id <= sc.cs_next_id ==>
    val_in_memory dv v (w2n w) u.vs_memory /\
    vv_at ce cx src sa sc ef raw (StackValue tag op) u
Proof
  rpt gen_tac >> strip_tac >>
  `expr_val_at ce cx src sa sb ee v op s` by gvs[vv_at_def] >>
  conj_tac
  >- (drule_all extcall_capture_expr_val_bytes_frame >> strip_tac >>
      irule exprSimPropsTheory.val_in_memory_footprint_agree >>
      simp[] >> qexists_tac `s.vs_memory` >> gvs[]) >>
  `vv_at ce cx src sa sc ee raw (StackValue tag op) u` by
    (irule abiEncodeMaterializeTheory.materialize_vv_at_alloc_frame >>
     qexistsl_tac [`s`, `sb`] >> simp[vv_operand_def]) >>
  `read_result cx raw ef = (INL v,ef)` by
    (Cases_on `read_result cx raw ef` >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[]) >>
  `expr_val_at ce cx src sa sc ef v op u <=>
   expr_val_at ce cx src sa sc ee v op u` by simp[expr_val_at_def] >>
  gvs[vv_at_def]
QED

(* No-copy composites retain their ownership type even when a memory
   bytestring's value interpretation changes capacity. *)
Theorem extcall_request_nonword_snapshot_capture:
  ~is_word_type dst /\
  (src = dst \/
   p.ptr_location = LocMemory /\
   is_bytestring_type src /\ is_bytestring_type dst) /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\
  value_has_type sv v /\ value_has_type dv v /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx src raw (LocatedValue tag p) ee s /\
  vv_at ce cx src sa sm ee raw (LocatedValue tag p) s /\
  compile_snapshot_vv ce F
    (ext_call_arg_value dst (LocatedValue tag p)) sm = (snap,sb)
  ==>
  sb = sm /\ snap = LocatedValue dst p /\
  vv_holds ce cx dst raw snap ee s /\
  vv_at ce cx src sa sm ee raw snap s /\
  val_footprint sv v = val_footprint dv v
Proof
  strip_tac
  >- (gvs[ext_call_arg_value_def, compile_snapshot_vv_def, vv_type_def,
          comp_return_def] >> conj_tac
      >- (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
          simp[vv_holds_def]) >>
      qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_at_def]) >>
  gvs[ext_call_arg_value_def, compile_snapshot_vv_def, vv_type_def,
      comp_return_def] >>
  conj_tac
  >- (irule vv_holds_bytestring_memory_retag >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[vv_at_def]) >>
  metis_tac[bytestring_val_footprint_eq]
QED

Theorem extcall_capture_nonmemory_transport:
  !H ctx func ce cx ty sa sb sc ee ef raw tag p s u.
    p.ptr_location <> LocMemory /\
    vv_holds ce cx ty raw (LocatedValue tag p) ee s /\
    vv_at ce cx ty sa sb ee raw (LocatedValue tag p) s /\
    vv_storage_live H cx (LocatedValue tag p) ee s /\
    stmt_state_rel H ctx func ce cx ef u /\
    (ef with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
      (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
    FST (read_result cx raw ef) = FST (read_result cx raw ee) /\
    (!w. eval_operand p.ptr_operand s = SOME w ==>
         eval_operand p.ptr_operand u = SOME w) ==>
    vv_holds ce cx ty raw (LocatedValue tag p) ef u /\
    vv_at ce cx ty sa sc ef raw (LocatedValue tag p) u /\
    vv_storage_live H cx (LocatedValue tag p) ef u
Proof
  rpt gen_tac >> strip_tac >>
  `ef.accounts = ee.accounts /\ ef.tStorage = ee.tStorage /\
   ef.immutables = ee.immutables` by
    (qpat_x_assum `_ with <|gas_obs := []; outcomes := NONE; storage_trace := []|> = _`
       (fn th => map_every (mp_tac o (fn f => AP_TERM f th))
          [``\x:evaluation_state. x.accounts``,
           ``\x:evaluation_state. x.tStorage``,
           ``\x:evaluation_state. x.immutables``]) >> simp[]) >>
  `!tr. get_storage cx ef tr = get_storage cx ee tr` by
    (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `SND (read_result cx raw ef) = ef` by
    (Cases_on `read_result cx raw ef` >>
     drule vyperStateTheory.read_result_state >> simp[]) >>
  Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, vv_at_def, vv_storage_live_def]
  >~ [`immutable_holds ce cx tag raw w ef u`]
  >- (gvs[immutable_holds_def] >>
      qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`, `v`] >>
      simp[] >> metis_tac[pairTheory.PAIR, pairTheory.FST, pairTheory.SND]) >>
  (gvs[storage_holds_def] >>
  `w2n w + type_slot_size tvt <= dimword (:256)` by
    gvs[accountsRelPropsTheory.storage_range_agree_def] >>
  `storage_read_live H (p.ptr_location = LocTransient)
     (get_storage cx ef (p.ptr_location = LocTransient)) w tvt` by simp[] >>
  qexists_tac `v` >> conj_tac
  >- (qpat_x_assum `read_storage_slot _ _ _ _ ee = _` mp_tac >>
      simp[vyperStateTheory.read_storage_slot_def,
           vyperStorageBackendTheory.get_storage_backend_eq,
           vyperStateTheory.bind_def, vyperStateTheory.lift_option_def,
           vyperStateTheory.return_def] >>
      Cases_on `decode_value (get_storage cx ee
        (p.ptr_location = LocTransient)) (w2n w) tvt` >>
      gvs[vyperStateTheory.return_def,
                            vyperStateTheory.raise_def]) >>
  conj_tac
  >- metis_tac[pairTheory.PAIR, pairTheory.FST, pairTheory.SND] >>
  irule accountsRelPropsTheory.storage_range_agree_of_live >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`H`, `p.ptr_location = LocTransient`] >>
  simp[] >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def,
      loweringStateRelDefsTheory.state_rel_def,
      loweringStateRelDefsTheory.storage_rel_def,
      loweringStateRelDefsTheory.transient_rel_def,
      vyperStorageBackendTheory.get_storage_def,
      vfmStateTheory.lookup_account_def])
QED

Theorem extcall_capture_read_result_frame:
  (ef with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
  (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) ==>
  FST (read_result cx raw ef) = FST (read_result cx raw ee)
Proof
  strip_tac >>
  `ef.scopes = ee.scopes /\ ef.accounts = ee.accounts /\
   ef.tStorage = ee.tStorage /\ ef.immutables = ee.immutables` by
    (qpat_x_assum `_ with <|gas_obs := []; outcomes := NONE; storage_trace := []|> = _`
       (fn th => map_every (mp_tac o (fn f => AP_TERM f th))
          [``\z:evaluation_state. z.scopes``, ``\z:evaluation_state. z.accounts``,
           ``\z:evaluation_state. z.tStorage``, ``\z:evaluation_state. z.immutables``]) >> simp[]) >>
  qpat_x_assum `_ with <|gas_obs := []; outcomes := NONE; storage_trace := []|> = _` kall_tac >>
  Cases_on `raw` >> simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rename1 `read_place cx place` >> Cases_on `place`
  >- (rename1 `StoragePlace tr slot vt` >> Cases_on `tr` >>
      simp[vyperStateTheory.read_place_def, vyperStateTheory.read_storage_slot_def,
           vyperStateTheory.get_storage_backend_def, vyperStateTheory.get_accounts_def,
           vyperStateTheory.get_transient_storage_def, vyperStateTheory.bind_def,
           vyperStateTheory.return_def, vyperStateTheory.lift_option_def] >>
      rpt (BasicProvers.TOP_CASE_TAC >> simp[vyperStateTheory.bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def]))
  >- (rename1 `MemoryPlace id path` >>
      simp[vyperStateTheory.read_place_def, vyperStateTheory.get_scopes_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
      Cases_on `lookup_scopes id ee.scopes` >>
      simp[vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_option_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      Cases_on `read_memory_path x path` >>
      simp[vyperStateTheory.lift_sum_def, vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
  rename1 `ImmutablePlace src id path` >>
  simp[vyperStateTheory.read_place_def, vyperStateTheory.get_immutables_def,
       vyperStateTheory.get_address_immutables_def, vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  simp[vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `FLOOKUP (get_source_immutables src x) id` >>
  simp[vyperStateTheory.lift_option_type_def, vyperStateTheory.lift_option_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `evaluate_subscripts (FST x') (SND x') path` >>
  simp[vyperStateTheory.lift_sum_def, vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem extcall_capture_value_transport:
  vv_holds ce cx dst raw snap ee s /\
  vv_at ce cx src ca cb ee raw snap s /\ vv_storage_live H cx snap ee s /\
  read_result cx raw ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) src = SOME sv /\
  evaluate_type (get_tenv cx) dst = SOME dv /\ val_wf dv v /\
  val_footprint sv v = val_footprint dv v /\
  (is_word_type src <=> is_word_type dst) /\
  (is_word_type src ==> src = dst) /\
  wb_frame ce ee ef cb s u /\ pure_frame ce func ee cut s u /\
  (ef with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) =
  (ee with <|gas_obs := []; outcomes := NONE; storage_trace := []|>) /\
  stmt_state_rel H ctx func ce cx ef u /\
  (!w. eval_operand (vv_operand snap) s = SOME w ==>
       eval_operand (vv_operand snap) u = SOME w) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
             FLOOKUP u.vs_allocas aid = SOME row) /\
  (!n b sz. local_region ce ef.scopes u n b sz <=>
             local_region ce ee.scopes s n b sz) /\
  cb.cs_next_id <= cc.cs_next_id ==>
  vv_holds ce cx dst raw snap ef u /\
  vv_at ce cx src ca cc ef raw snap u /\ vv_storage_live H cx snap ef u
Proof
  strip_tac >>
  `FST (read_result cx raw ef) = FST (read_result cx raw ee)` by
    (irule extcall_capture_read_result_frame >> simp[]) >>
  `read_result cx raw ef = (INL v,ef)` by
    (Cases_on `read_result cx raw ef` >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[]) >>
  `ef.scopes = ee.scopes` by
    (qpat_assum `_ with <|gas_obs := []; outcomes := NONE; storage_trace := []|> = _`
      (mp_tac o AP_TERM ``\z:evaluation_state. z.scopes``) >> simp[]) >>
  Cases_on `snap`
  >- (rename1 `StackValue tag op` >>
      Cases_on `is_word_type src`
      >- (gvs[vv_holds_def, vv_at_def, expr_val_at_def, expr_val_rel_def,
              vv_operand_def] >> metis_tac[]) >>
      `?w. eval_operand op s = SOME w /\
           val_in_memory dv v (w2n w) s.vs_memory` by
        gvs[vv_holds_def, expr_val_rel_def] >>
      `val_in_memory dv v (w2n w) u.vs_memory /\
       vv_at ce cx src ca cc ef raw (StackValue tag op) u` by
        (irule extcall_capture_stack_memory_transport >>
         simp[vv_operand_def] >>
         conj_tac >- gvs[vv_operand_def] >>
         qexistsl_tac [`cut`, `ee`, `func`, `s`, `cb`] >> simp[] >> metis_tac[]) >>
      gvs[vv_operand_def] >>
      simp[vv_holds_def, expr_val_rel_def] >>
      qexists_tac `w` >> simp[]) >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (`?w. eval_operand p.ptr_operand s = SOME w /\
            val_in_memory dv v (w2n w) s.vs_memory /\
            (is_word_type dst ==> mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 dv v)` by
        gvs[vv_holds_def] >>
      `val_in_memory dv v (w2n w) u.vs_memory /\
       vv_at ce cx src ca cc ef raw (LocatedValue tag p) u` by
        (irule extcall_capture_located_memory_transport >> simp[] >>
         qexistsl_tac [`cut`, `ee`, `func`, `s`, `cb`] >>
         gvs[vv_operand_def]) >>
      `is_word_type dst ==> mem_word_at (w2n w) u.vs_memory = typed_val_to_w256 dv v` by
        (strip_tac >>
         `val_footprint sv v = 32` by metis_tac[word_value_memory_extent] >>
         `mem_bytes_at (w2n w) 32 u.vs_memory = mem_bytes_at (w2n w) 32 s.vs_memory` by
           (drule_all extcall_capture_memory_bytes_frame >> simp[]) >>
         gvs[mem_word_at_bytes]) >>
      gvs[vv_operand_def, vv_holds_def] >>
      qexists_tac `w` >> simp[]) >>
  `vv_at ce cx dst ca cb ee raw (LocatedValue tag p) s` by
    gvs[vv_at_def] >>
  `vv_holds ce cx dst raw (LocatedValue tag p) ef u /\
   vv_at ce cx dst ca cc ef raw (LocatedValue tag p) u /\
   vv_storage_live H cx (LocatedValue tag p) ef u` by
    (irule extcall_capture_nonmemory_transport >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`ee`, `s`, `cb`] >> gvs[vv_operand_def]) >>
  gvs[vv_at_def]
QED
