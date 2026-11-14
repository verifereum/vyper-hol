(* Word snapshots reuse the original compiled value's unwrap path. *)
Theory bodyFullExtCallRequestSnapshotWord
Ancestors
  bodyFullExtCallRequestSnapshot exprSimHypsDefs exprSimHyps
  aggregateEvaluatedLayout loweringPosts exprLowering context compileEnv
  exprSimUnwrap valueEncodingProofs valueEncodingDefs

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
