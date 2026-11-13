Theory bodyPtrAttributeSummary
Ancestors
  bodyPtrAttributeSelection bodyPtrAttributeSource bodyPtrAttributeStorage bodyPtrAttributeObservation
  gasSummaryComposePtr exprSimAttributeFields vyperPlaceResultTyping
  bodyPtrAttributeCase bodyPtrAttributeFields exprSimFieldLayout
  exprSimDefs exprSimAttributeProps compileEnv loweringPosts exprLowering context exprSimAttribute exprSimSource
  emitHelper emitHelperProps freshWrites ASCIInumbers venomState bodyPtrDefs ptrDiscipline
  gasSummary gasCount fragGasPath fragGasMode fragGasPathPtr list

Theorem attribute_normal_endpoint_ptr:
  expr_body_pre cenv cx env (Attribute ann obj fld) es0 /\
  eval_expr cx obj es0 = (INL btv,ee) /\
  compile_expr cenv ty obj sa = (bvv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv;
    Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  vv_post H ctx func cenv cx obj es sa sm s0 ee btv bvv s /\
  ptr_vv_ok cx (expr_type obj) btv bvv ee G tn s /\
  ghost_inv H d cenv cx ee G tn s /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  ?tv' G' tn' t.
    select_result cx (expr_type obj) btv (AttrSubscript fld) ee = (INL tv',ee) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post H ctx func cenv cx (Attribute ann obj fld) es sa sn s0 ee tv'
      (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
    ghost_inv H d cenv cx ee G' tn' t /\
    ptr_vv_ok cx ann tv' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee G' tn' t /\
    (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Attribute ann obj fld) dst G' t) /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  `op_taint tn (vv_operand bvv) = {}` by
    (Cases_on `bvv` >> gvs[bodyPtrDefsTheory.ptr_vv_ok_def,
       bodyPtrDefsTheory.ptr_val_ok_def, vv_operand_def]) >>
  `?v w. read_result cx btv ee = (INL v,ee) /\
    eval_operand (vv_operand bvv) s = SOME w` by
    (`vv_holds cenv cx (post_value_type cenv obj) btv bvv ee s` by fs[vv_post_def] >>
     drule attribute_vv_holds_read_operand >> simp[]) >>
  drule_all attribute_add_path_post_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  drule_all attribute_selected_vv_post >> strip_tac >>
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
     ?y. Var (STRING #"%" (toString sm.cs_next_var)) = Var y /\
         FLOOKUP G' y = SOME (b,sz)` by
    (rpt strip_tac >> simp[] >> gvs[op_prov_def]) >>
  `vv_loc bvv = LocCode ==>
     op_prov G' (Var (STRING #"%" (toString sm.cs_next_var))) = NONE` by
    (Cases_on `bvv` >>
     gvs[vv_loc_def, vv_location_def, vv_operand_def, op_prov_def,
         bodyPtrDefsTheory.ptr_vv_ok_def]) >>
  `eval_operand (Var (STRING #"%" (toString sm.cs_next_var))) t =
    SOME (w + n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
  qpat_x_assum `sn.cs_current_insts = _` kall_tac >>
  drule_all attribute_selected_ptr >> strip_tac >>
  gvs[sumTheory.INL_11] >>
  goal_assum (drule_at Any) >> qexists_tac `tn'` >> simp[] >>
  simp[Abbr `t`] >> simp[update_var_def]
QED

Theorem attribute_summary_ok_ptr:
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  compile_expr cenv ty obj sa = (bvv,sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv;
    Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))] sm = (dst,sn) /\
  fn_has_code sm sn func /\ ~ctx_has_dalloca ctx /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_expr cx obj) (es,s0,G0,tn0)
    marks (INL btv) fe G tn (OK s) /\
  vv_post H ctx func cenv cx obj es sa sm s0 (fe with gas_obs := []) btv bvv s /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv H d cenv cx (fe with gas_obs := []) G tn s /\
  ptr_vv_ok cx (expr_type obj) btv bvv (fe with gas_obs := []) G tn s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at D (ctx,func) PG marks (eval_expr cx (Attribute ann obj fld))
    (es,s0,G0,tn0)
    (\res ee HG tt t. ?tv. res = INL tv /\
      vv_post H ctx func cenv cx (Attribute ann obj fld) es sa sn s0 ee tv
        (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
      t.vs_current_bb = sn.cs_current_bb /\ t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      ghost_inv H d cenv cx ee HG tt t /\
      ptr_vv_ok cx ann tv (LocatedValue ann (mk_ptr dst (vv_loc bvv))) ee HG tt t /\
      (vv_loc bvv = LocMemory ==> ptr_buf_ok cenv (Attribute ann obj fld) dst HG t) /\
      ghost_kept cenv es sa G0 tn0 s0 HG tt) R
Proof
  strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL btv,fe with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `~s.vs_halted` by
    (drule gas_marked_exec_ptr_exec >>
     metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal]) >>
  `expr_body_pre cenv cx env (Attribute ann obj fld)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all attribute_normal_endpoint_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexists_tac `INL tv'` >> qexists_tac `fe` >>
  qexistsl_tac [`G'`, `tn'`, `OK t`] >> simp[] >>
  `eval_expr cx (Attribute ann obj fld) = bind (eval_expr cx obj)
    (\r. select_result cx (expr_type obj) r (AttrSubscript fld))` by
    simp[FUN_EQ_THM, eval_expr_attribute] >> asm_rewrite_tac[] >>
  irule (gas_marked_exec_ptr_bind_normal |> Q.INST [`right` |-> `[]`] |>
    REWRITE_RULE [APPEND_NIL]) >>
  goal_assum (drule_at Any) >>
  simp[gas_marked_exec_ptr_def, gas_explicit_def, select_attr_gas_update] >>
  qpat_x_assum `select_result _ _ _ _ _ = _` mp_tac >>
  simp[select_attr_gas_update] >> strip_tac >>
  gvs[vyperStateTheory.evaluation_state_component_equality]
QED
