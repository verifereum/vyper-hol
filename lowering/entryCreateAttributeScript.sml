Theory entryCreateAttribute
Ancestors
  bodyFullAttribute bodyPtrAttributeObservation entryCreateFocusSpec
  entryCreateAdminSequence entryCreateScopedBind entryCreatePathScope
  entryCreateCompletedCut entryCreateOperandReplay entryCreateNativeFirstExit
  createSizeCutCode createSizeCutRegion exprSimAbiGasBridge
  abiEncoderProps gasSummary gasExemptCert fragGasOriginPtrExec fragExec
  vyperState vyperAST vyperStorageTrace vyperStorageFootprint
  gasOutcomeFullCompose exprLoweringProps venomInst venomExecSemantics list

Theorem field_vv_scoped_post[local]:
  field_vv_post (DF,lo,d,ctx,f) ce cx e (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t <=>
  create_operand_vv_post (DF,lo,d,ctx,f) ce cx e (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\
  create_operand_at sb t
Proof
  simp[field_vv_post_def, create_operand_vv_post_def, create_operand_at_def] >>
  iff_tac
  >- (strip_tac >> simp[] >> qexists_tac `tv` >> simp[]) >>
  strip_tac >> qexists_tac `tv` >> simp[]
QED

Theorem attribute_add_layout[local]:
  emit_op ADD [x; Lit off] sm = (p,sb) /\ fn_has_code sm sb f ==>
  sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  emitted_insts sm sb = [mk_inst sm.cs_next_id ADD [x; Lit off]
    [STRING #"%" (toString sm.cs_next_var)]] /\
  sb.cs_next_id = SUC sm.cs_next_id
Proof
  strip_tac >> drule_all attribute_add_code >> strip_tac >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem attribute_add_scoped[local]:
  expr_body_pre cenv cx env (Attribute ann obj fld) es /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (attr_offset cenv (expr_type obj) (vv_loc bvv) fld))]
    sm = (p,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\ mid.gas_obs = [] /\
  create_operand_at sm s /\
  eval_expr cx obj (es with gas_obs := obs) = (INL tv,mid) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    field_vv_post (DF,lo,d,ctx,func) cenv cx obj (es,sa,sm,s0,bvv,G0,tn0)
      H (INL tv : eval_result + exception) mid G1 tn1 s) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sm sb
    (select_result cx (expr_type obj) tv (AttrSubscript fld)) (mid,s,G1,tn1)
    (field_vv_post (DF,lo,d,ctx,func) cenv cx (Attribute ann obj fld)
        (es,sa,sb,s0,LocatedValue ann (mk_ptr p (vv_loc bvv)),G0,tn0)) R /\
  create_operand_cut sm sb E ctx func tops cx st0
    (select_result cx (expr_type obj) tv (AttrSubscript fld)) (mid,s)
Proof
  strip_tac >> drule_all attribute_add_layout >> strip_tac >>
  conj_tac
  >- (drule_all attribute_vv_selection >>
      disch_then (qspecl_then [`E`, `PG`] strip_assume_tac) >>
      `step_inst_base i s = OK u` by
        (qpat_x_assum `!k. step_inst _ _ i s = _` (qspec_then `0` mp_tac) >>
         simp[step_inst_non_invoke, mk_inst_def]) >>
      `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by
        fs[create_operand_at_def, arithmeticTheory.ADD1] >>
      `create_operand_full_scope sm sb E ctx func s []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
        (qpat_x_assum `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx`
           (ONCE_REWRITE_TAC o single o SYM) >>
         irule create_admin_sequence_scope >>
         qpat_x_assum `i = _` SUBST_ALL_TAC >>
         fs[run_inst_seq_def, frag_ids_def, mk_inst_def, is_terminator_def]) >>
      `mid with gas_obs := [] = mid` by
        (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
      simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`INL tv'`, `mid`, `OK (u with vs_inst_idx := SUC s.vs_inst_idx)`, `G2`, `tn2`] >>
      simp[gas_explicit_def, select_attr_gas_update, fragExecTheory.exit_result_def] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  irule create_admin_sequence_cut >> simp[mk_inst_def, is_terminator_def]
QED

Theorem attribute_base_pre[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty (Attribute ann obj fld) es
    (st0,a,b,sha,shb,vv,s,G,tn) ==>
  ?base m shm p.
    compile_expr ce ty obj a = (base,m) /\
    emit_op ADD [vv_operand base;
      Lit (n2w (attr_offset ce (expr_type obj) (vv_loc base) fld))] m = (p,b) /\
    vv = LocatedValue ann (mk_ptr p (vv_loc base)) /\
    cs_extends a m /\ cs_extends m b /\ fn_has_code m b f /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty obj es
      (st0,a,m,sha,shm,base,s,G,tn)
Proof
  strip_tac >> drule exprSimAttributeTheory.attr_pre_base >> strip_tac >>
  fs[s1PrefixDefsTheory.expr_vv_sim_full_pre_def] >>
  drule_all attribute_compiled_base >> strip_tac >>
  drule exprSimHypsTheory.expr_body_pre_vv_gas_admissible >> strip_tac >>
  qexistsl_tac [`bvv`,`sm`,`shadow_sm`,`p`] >> fs[] >> metis_tac[]
QED

(* The successful base supplies the exact tail-independent input of the ADD. *)
Theorem attribute_selected_suffix[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  compile_expr ce ty obj a = (bvv,m) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld))]
    m = (p,b) /\
  fn_has_code m b f /\ local_ptrs_reserved ce a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at m t /\
  mid.gas_obs = [] /\
  (!tail. eval_expr cx obj (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,mid with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn)
      H res mid G1 tn1 t /\
    gas_origin_ptr_path (DF H,lo,E,ctx,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
  ?v. res = INL v /\ scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 m b
    (select_result cx (expr_type obj) v (AttrSubscript fld))
    (mid,t,G1,tn1)
    (field_vv_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld)
      (es,a,b,s,LocatedValue ann (mk_ptr p (vv_loc bvv)),G,tn)) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> field_vv_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `?v. res = INL v` by fs[field_vv_post_def] >>
  pop_assum strip_assume_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE bool_ss [APPEND_NIL])) >>
  qpat_assum `mid with gas_obs := [] = mid`
    (fn th => rule_assum_tac (ONCE_REWRITE_RULE [th])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn)
      H (INL v : eval_result + exception) mid G1 tn1 t` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  drule_all attribute_add_scoped >> simp[]
QED

Theorem attribute_bind_scoped[local]:
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  compile_expr ce ty obj a = (bvv,m) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld))]
    m = (p,b) /\
  fn_has_code m b f /\ local_ptrs_reserved ce a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m (eval_expr cx obj) (es,s,G,tn)
    (field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn))
    (create_operand_exit_post ctx cx) /\
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
           create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
             create_operand_full_scope a b E ctx f s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx f s left (OK t) /\
        create_operand_focus_scope m b E ctx f t right ==>
        create_operand_focus_scope a b E ctx f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx f s left (OK t) /\
        create_operand_full_scope m b E ctx f t right r ==>
        create_operand_full_scope a b E ctx f s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (eval_expr cx (Attribute ann obj fld)) (es,s,G,tn)
    (field_vv_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld)
      (es,a,b,s,LocatedValue ann (mk_ptr p (vv_loc bvv)),G,tn))
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  `eval_expr cx (Attribute ann obj fld) =
   bind (eval_expr cx obj) (\v. select_result cx (expr_type obj) v (AttrSubscript fld))` by
    simp[FUN_EQ_THM, exprSimAttributeTheory.eval_expr_attribute] >>
  asm_rewrite_tac[] >> irule scoped_operand_bind_all >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_select, ignore_bind_def, bind_assoc] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[ignore_bind_def]) >>
  qexistsl_tac [`\H res ee G1 tn1 t.
    field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn) H res ee G1 tn1 t /\
    ee.gas_obs = []`, `m`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule attribute_selected_suffix >>
      simp[] >> conj_tac
      >- (qexists_tac `marks` >> metis_tac[]) >>
      fs[storage_trace_domain_def] >> metis_tac[]) >>
  rpt conj_tac >> TRY (rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC) >> NO_TAC) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >>
  qexists_tac `marks` >> simp[]
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> Cases_on `r` >> gvs[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED
