Theory entryCreateAttribute
Ancestors
  bodyFullAttribute bodyPtrAttributeObservation entryCreateFocusSpec
  entryCreateAdminSequence entryCreateScopedBind entryCreatePathScope
  entryCreateCompletedCut abiEncoderProps gasSummary
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
