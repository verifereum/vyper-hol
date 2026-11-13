(* Counted execution is kept separate from the representation restrictions. *)
Theory bodyPtrSubscriptSeamTupleSummary
Ancestors
  bodyPtrSubscriptSeamTupleSelection bodyPtrSubscriptSeamTupleSource
  bodyPtrAttributeCase bodyPtrAttributeAdd bodyPtrAttributeSource
  bodyPtrSubscriptTupleDispatch exprSimDefs exprSimProps exprSimAttributeProps
  exprSimTuple exprSimVVFrame exprLowering exprLoweringProps loweringPosts
  compileEnv context venomState bodyPtrDefs ptrDiscipline
  emitHelper emitHelperProps freshWrites ASCIInumbers finite_map list
  gasSummaryComposePtr fragGasPathPtr gasSummary gasCount fragGasPath fragGasMode
  exprSimSource exprSimHyps exprSimUnwrap fragExec gasExemptCert vyperAST vyperState

Theorem tuple_normal_endpoint_ptr:
  expr_body_pre cenv cx env (Subscript ann obj idx) (es with gas_obs := gs) /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  idx = Literal ity (IntL (&k)) /\
  eval_expr cx obj (es with gas_obs := gs) = (INL btv,ee) /\
  compile_expr cenv ty obj sa = (bvv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  vv_post ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  ptr_vv_ok cx (TupleT tys) btv bvv ee G tn s /\
  (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv obj (vv_operand bvv) G s) /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?tv' G' tn' t.
    select_result cx (TupleT tys) btv (ValueSubscript (IntV (&k))) ee = (INL tv',ee) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func cenv cx (Subscript ann obj idx) es sa sn s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
    ghost_inv d cenv cx ee G' tn' t /\
    ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee G' tn' t /\
    (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Subscript ann obj idx) dst G' t) /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `op_taint tn (vv_operand bvv) = {}` by
    (Cases_on `bvv` >> gvs[ptr_vv_ok_def, ptr_val_ok_def, vv_operand_def]) >>
  `?v w. read_result cx btv ee = (INL v,ee) /\ eval_operand (vv_operand bvv) s = SOME w` by
    (irule attribute_vv_holds_read_operand >> fs[vv_post_def] >> metis_tac[]) >>
  drule_all attribute_add_path_post_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule_all tuple_selected_vv_post >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   LENGTH sn.cs_current_insts = SUC (LENGTH sm.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all attribute_fresh_ghost_update >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ (OK t)` >>
  `t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient` by
    simp[Abbr `t`, update_var_def] >>
  `!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
    ?y. Var (STRING #"%" (toString sm.cs_next_var)) = Var y /\ FLOOKUP G' y = SOME (b,sz)` by
    (rpt strip_tac >> simp[] >> gvs[op_prov_def]) >>
  `vv_loc bvv = LocCode ==>
    op_prov G' (Var (STRING #"%" (toString sm.cs_next_var))) = NONE` by
    (Cases_on `bvv` >>
     gvs[vv_loc_def, vv_location_def, vv_operand_def, op_prov_def, ptr_vv_ok_def]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) t =
    SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k))` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
  qpat_x_assum `sn.cs_current_insts = _` kall_tac >>
  drule_all (tuple_selected_ptr |>
    Q.INST [`idx` |-> `Literal ity (IntL (&k))`] |> SRULE []) >>
  strip_tac >> gvs[sumTheory.INL_11] >>
  goal_assum (drule_at Any) >> qexists_tac `tn'` >> simp[] >>
  simp[Abbr `t`, update_var_def]
QED

Theorem tuple_summary_ok_ptr:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  idx = Literal ity (IntL (&k)) /\
  compile_expr cenv ty obj sa = (bvv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx obj) (es,s0,G0,tn0)
    marks (INL btv) fe G tn (OK s) /\
  vv_post ctx func cenv cx obj es sa sm s0 (fe with gas_obs := []) btv bvv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx (fe with gas_obs := []) G tn s /\
  ptr_vv_ok cx (TupleT tys) btv bvv (fe with gas_obs := []) G tn s /\
  (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv obj (vv_operand bvv) G s) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at D (ctx,func) PG marks (eval_expr cx (Subscript ann obj idx))
    (es,s0,G0,tn0)
    (\res ee H tt t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sn s0 ee tv
        (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
      t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      ghost_inv d cenv cx ee H tt t /\
      ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee H tt t /\
      (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Subscript ann obj idx) dst H t) /\
      ghost_kept cenv es sa G0 tn0 s0 H tt) R
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL btv,fe with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~s.vs_halted` by
    (drule gas_marked_exec_ptr_exec >>
     metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal]) >>
  gvs[] >> drule_all (tuple_normal_endpoint_ptr |>
    Q.INST [`idx` |-> `Literal ity (IntL (&k))`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexists_tac `INL tv'` >> qexists_tac `fe` >>
  qexistsl_tac [`G'`, `tn'`, `OK t`] >> simp[] >>
  `eval_expr cx (Subscript ann obj (Literal ity (IntL (&k)))) = bind (eval_expr cx obj)
    (\r. select_result cx (TupleT tys) r (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, tuple_subscript_source] >> asm_rewrite_tac[] >>
  irule (gas_marked_exec_ptr_bind_normal |> Q.INST [`right` |-> `[]`] |>
    REWRITE_RULE [APPEND_NIL]) >>
  goal_assum (drule_at Any) >>
  simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
  drule tuple_selection_gas_obs >> simp[]
QED

Theorem tuple_vv_sim_ptr_compose:
  !d ctx PG func cenv cx env ty ann obj idx es tys.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
    post_value_type cenv obj = expr_type obj /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty obj es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >> drule_all tuple_subscript_pre >> strip_tac >> gvs[] >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all tuple_subscript_compile >> strip_tac >> gvs[] >>
  rename1 `compile_expr cenv ty obj sa = (bvv,sm)` >>
  `cs_extends sm sb` by
    (drule emit_op_extends >> simp[same_blocks_def, cs_extends_def] >>
     strip_tac >> qexists_tac `[]` >> simp[]) >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >> suspend "exempt"
QED

Resume tuple_vv_sim_ptr_compose[normal]:
  `vv_loc bvv = LocMemory ==> ptr_buf_ok cenv obj (vv_operand bvv) G t` by
    (Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def]) >>
  gvs[literal_int_index_def] >>
  drule_all (tuple_summary_ok_ptr |>
    Q.INST [`idx` |-> `Literal ity (IntL (&k))`] |>
    SRULE [expr_type_def, mk_ptr_def, tuple_offset_def, literal_int_index_def]) >>
  simp[expr_type_def, mk_ptr_def]
QED
Resume tuple_vv_sim_ptr_compose[exception]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >> simp[] >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) = bind (eval_expr cx obj)
    (\v. select_result cx (TupleT tys) v (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, tuple_subscript_source] >> asm_rewrite_tac[] >>
  irule gas_marked_exec_ptr_bind_exception >> simp[]
QED
Resume tuple_vv_sim_ptr_compose[exempt]:
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  `eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) = bind (eval_expr cx obj)
    (\v. select_result cx (TupleT tys) v (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, tuple_subscript_source] >>
  asm_rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED
Finalise tuple_vv_sim_ptr_compose
