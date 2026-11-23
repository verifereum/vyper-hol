Theory entryCreateAttribute
Ancestors
  bodyFullAttribute bodyPtrAttributeObservation entryCreateFocusSpec
  entryCreateAdminSequence entryCreateScopedBind entryCreatePathScope entryCreateBodyCut
  entryCreateCompletedCut entryCreateOperandReplay entryCreateNativeFirstExit
  entryCreatePendingScope createSizePrefixReplay
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

Theorem attribute_add_cut_code[local]:
  emit_op ADD [x; Lit off] m = (p,b) ==> create_cut_code {} m b
Proof
  strip_tac >>
  `create_cut_code {} m (SND (emit_op ADD [x; Lit off] m))` by
    (irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
  pop_assum mp_tac >> asm_simp_tac bool_ss [pairTheory.SND]
QED

(* The right visit has no CREATE of its own or in a pending callee. Its
   administrative cut is independent of the source computation. *)
Theorem attribute_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\ fn_has_code m b f /\
  emit_op ADD [x; Lit off] m = (p,b) /\
  create_operand_cut a m E ctx f tops cx st0 (eval_expr cx obj) (es,s) ==>
  create_operand_cut a b E ctx f tops cx st0
    (eval_expr cx (Attribute ann obj fld)) (es,s)
Proof
  strip_tac >>
  drule attribute_add_cut_code >> disch_tac >>
  drule_all attribute_add_layout >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (`eval_expr cx (Attribute ann obj fld) =
        bind (eval_expr cx obj) (\v. select_result cx (expr_type obj) v (AttrSubscript fld))` by
        simp[FUN_EQ_THM,exprSimAttributeTheory.eval_expr_attribute] >>
      asm_rewrite_tac[] >> irule create_cut_bind_left >> simp[storage_trace_frame_select] >>
      fs[create_operand_cut_def] >> metis_tac[]) >>
  simp[create_body_cut_def] >> rpt strip_tac >>
  `create_operand_cut m b E ctx f tops cx st0 (\_. (res,ee)) (es,t)` by
    (irule create_admin_sequence_cut >> simp[mk_inst_def,is_terminator_def]) >>
  qpat_x_assum `create_operand_cut m b _ _ _ _ _ _ _ _` mp_tac >>
  simp[create_operand_cut_def,create_body_cut_def] >>
  disch_then (drule_then mp_tac) >> simp[] >> metis_tac[]
QED

(* The suffix and the whole expression have the same exit. Widening the
   suffix therefore only changes the lower end of its instruction-ID band. *)
Theorem attribute_suffix_step_widen[local]:
  a.cs_next_id <= m.cs_next_id /\ create_prefix_step m b E ctx f s left t ==>
  create_prefix_step a b E ctx f s left t
Proof
  simp[create_prefix_step_def, frag_ids_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem attribute_full_scope_join[local]:
  a.cs_next_id <= m.cs_next_id /\
  create_expr_prefix a b E ctx f s left t /\
  create_operand_full_scope m b E ctx f t right r ==>
  create_operand_full_scope a b E ctx f s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_mono,attribute_suffix_step_widen,
            create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem attribute_focus_scope_join[local]:
  a.cs_next_id <= m.cs_next_id /\
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} m b /\ fn_has_code m b f /\ create_operand_at m t /\
  create_expr_prefix a b E ctx f s left t /\
  create_operand_focus_scope m b E ctx f t right ==>
  create_operand_focus_scope a b E ctx f s (left ++ right)
Proof
  strip_tac >> irule entryCreatePendingScopeTheory.create_operand_focus_scope_prepend >>
  first_assum (irule_at Any) >> irule entryCreatePendingScopeTheory.create_operand_focus_scope_lift >>
  first_assum (irule_at Any) >> first_assum (irule_at Any) >> simp[] >>
  `create_cut_region m b t` by
    (drule_all create_cut_region_rules >> fs[create_operand_at_def]) >>
  metis_tac[attribute_suffix_step_widen]
QED

Theorem attribute_vv_at_split[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  compile_expr ce ty obj a = (bvv,m) /\
  emit_op ADD [vv_operand bvv;
    Lit (n2w (attr_offset ce (expr_type obj) (vv_loc bvv) fld))] m = (p,b) /\
  vv = LocatedValue ann (mk_ptr p (vv_loc bvv)) /\
  create_cut_code {} a m /\ fn_has_code a m f /\ fn_has_code m b f /\
  a.cs_next_id <= m.cs_next_id /\ local_ptrs_reserved ce a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a m (eval_expr cx obj) (es,s,G,tn)
    (field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a m E ctx f tops cx st0 (eval_expr cx obj) (es,s) /\
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
           create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
             create_operand_full_scope a b E ctx f s marks r) /\
  (!left t. create_expr_prefix a m E ctx f s left t ==>
            create_expr_prefix a b E ctx f s left t) ==>
  scoped_operand_outcome (DF,lo,E,ctx,f,PG) tops cx st0 a b
    (eval_expr cx (Attribute ann obj fld)) (es,s,G,tn)
    (field_vv_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld) (es,a,b,s,vv,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a b E ctx f tops cx st0 (eval_expr cx (Attribute ann obj fld)) (es,s)
Proof
  strip_tac >> drule attribute_add_cut_code >> disch_tac >>
  reverse conj_tac >- (irule attribute_cut >> first_assum (irule_at Any) >> metis_tac[]) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  irule attribute_bind_scoped >> first_assum (irule_at Any) >> simp[] >>
  qexistsl_tac [`ty`,`env`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule attribute_full_scope_join >>
      first_assum (irule_at Any) >> fs[create_operand_full_scope_def] >> metis_tac[]) >>
  rpt strip_tac >> irule attribute_focus_scope_join >>
  first_assum (irule_at Any) >> fs[create_operand_full_scope_def,create_operand_at_def] >>
  metis_tac[]
QED

Theorem attribute_vv_from_base[local]:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Attribute ann obj fld) es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty (Attribute ann obj fld) es
    (st0,a,b,sha,shb,vv,s,G,tn) /\
  L a b /\
  (!m shm bvv. expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty obj es
      (st0,a,m,sha,shm,bvv,s,G,tn) /\ L a m ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG) tops cx st0 a m
      (eval_expr cx obj) (es,s,G,tn)
      (field_vv_post (DF,lo,d,ctx,f) ce cx obj (es,a,m,s,bvv,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f tops cx st0
      (eval_expr cx obj) (es,s)) /\
  (!a m b. cs_extends a m /\ cs_extends m b /\ L a b ==> L a m) /\
  (!a m b u. cs_extends a m /\ cs_extends m b /\ L a b /\
       create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) /\
  (!a m b s. create_cut_code {} a m /\ fn_has_code a m f /\ create_cut_region a m s /\
       m.cs_next_id <= b.cs_next_id /\
       (!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) ==>
       (!marks. create_operand_focus_scope a m (gas_explicit_sites ctx shctx) ctx f s marks ==>
                create_operand_focus_scope a b (gas_explicit_sites ctx shctx) ctx f s marks) /\
       (!marks r. exit_result r /\ create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx f s marks r ==>
                create_operand_full_scope a b (gas_explicit_sites ctx shctx) ctx f s marks r) /\
       (!left t. create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx f s left t ==>
                create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx f s left t)) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG) tops cx st0 a b
    (eval_expr cx (Attribute ann obj fld)) (es,s,G,tn)
    (field_vv_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld) (es,a,b,s,vv,G,tn))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f tops cx st0
    (eval_expr cx (Attribute ann obj fld)) (es,s)
Proof
  strip_tac >> drule_all attribute_base_pre >> strip_tac >>
  rename1 `compile_expr ce ty obj a = (bvv,m)` >>
  `L a m` by metis_tac[] >>
  qpat_x_assum `!m shm bvv. _ ==> _` (drule_then (strip_assume_tac o UNDISCH)) >>
  drule operand_vv_cut_code >> disch_tac >>
  fs[s1PrefixDefsTheory.expr_vv_sim_full_pre_def] >>
  `create_cut_region a m s` by
    (drule_all create_cut_region_rules >> fs[]) >>
  `a.cs_next_id <= m.cs_next_id` by metis_tac[exprLoweringPropsTheory.compile_expr_grows] >>
  `m.cs_next_id <= b.cs_next_id` by
    (drule_all attribute_add_layout >> simp[]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u` by metis_tac[] >>
  qpat_x_assum `!a m b s. create_cut_code {} a m /\ _ ==> _`
    (qspecl_then [`a`,`m`,`b`,`s`] mp_tac) >>
  simp[] >> strip_tac >> irule attribute_vv_at_split >>
  first_assum (irule_at Any) >> simp[] >> metis_tac[]
QED

(* The guarded callback is used at the compiled base, before the field ADD.
   The value arm invokes the same generic forcing law as the other VV cases. *)
Theorem create_attribute_scoped_case:
  body_inv (cx_tops cx) ctx ce cx /\
  expr_body_pre ce cx env (Attribute ann obj fld) es /\
  (!a m b. cs_extends a m /\ cs_extends m b /\ L a b ==> L a m) /\
  (!a m b u. cs_extends a m /\ cs_extends m b /\ L a b /\
       create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) /\
  (!a m b s. create_cut_code {} a m /\ fn_has_code a m f /\ create_cut_region a m s /\
       m.cs_next_id <= b.cs_next_id /\
       (!u. create_cut_region a m u /\ ~create_operand_at m u ==> ~create_operand_at b u) ==>
       (!marks. create_operand_focus_scope a m (gas_explicit_sites ctx shctx) ctx f s marks ==>
                create_operand_focus_scope a b (gas_explicit_sites ctx shctx) ctx f s marks) /\
       (!marks r. exit_result r /\ create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx f s marks r ==>
                create_operand_full_scope a b (gas_explicit_sites ctx shctx) ctx f s marks r) /\
       (!left t. create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx f s left t ==>
                create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx f s left t)) /\
  (!e st0 a b sha shb op s G tn.
    expr_body_pre ce cx env e es /\ L a b /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty e es
      (st0,a,b,sha,shb,op,s,G,tn) /\
    (!m shm vv. L a m /\
       expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty e es
         (st0,a,m,sha,shm,vv,s,G,tn) ==>
       scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
         (cx_tops cx) cx st0 a m (eval_expr cx e) (es,s,G,tn)
         (\H res ee G' tn' t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx e
           (es,a,m,s,vv,G,tn) H res ee G' tn' t /\ create_operand_at m t)
         (create_operand_exit_post ctx cx) /\
       create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
         (eval_expr cx e) (es,s)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
      (cx_tops cx) cx st0 a b (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,f) ce cx e (es,a,b,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s)) /\
  (!st0 a m sha shm vv s G tn. L a m /\
     expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty obj es
       (st0,a,m,sha,shm,vv,s,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
       (cx_tops cx) cx st0 a m (eval_expr cx obj) (es,s,G,tn)
       (\H res ee G' tn' t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx obj
         (es,a,m,s,vv,G,tn) H res ee G' tn' t /\ create_operand_at m t)
       (create_operand_exit_post ctx cx) /\
     create_operand_cut a m (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
       (eval_expr cx obj) (es,s)) ==>
  (!st0 a b sha shb vv s G tn. L a b /\
     expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty (Attribute ann obj fld) es
       (st0,a,b,sha,shb,vv,s,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
       (cx_tops cx) cx st0 a b (eval_expr cx (Attribute ann obj fld)) (es,s,G,tn)
       (\H res ee G' tn' t. create_operand_vv_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld)
         (es,a,b,s,vv,G,tn) H res ee G' tn' t /\ create_operand_at b t)
       (create_operand_exit_post ctx cx) /\
     create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
       (eval_expr cx (Attribute ann obj fld)) (es,s)) /\
  (!st0 a b sha shb op s G tn. L a b /\
     expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,f,sf) ce cx ty (Attribute ann obj fld) es
       (st0,a,b,sha,shb,op,s,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,f,PG)
       (cx_tops cx) cx st0 a b (bind (eval_expr cx (Attribute ann obj fld)) (read_result cx)) (es,s,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,f) ce cx (Attribute ann obj fld) (es,a,b,s,op,G,tn))
       (create_operand_exit_post ctx cx) /\
     create_operand_cut a b (gas_explicit_sites ctx shctx) ctx f (cx_tops cx) cx st0
       (bind (eval_expr cx (Attribute ann obj fld)) (read_result cx)) (es,s))
Proof
  strip_tac >> conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[GSYM field_vv_scoped_post] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      irule attribute_vv_from_base >>
      qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >>
      qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
      qexists_tac `L` >> rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC >> NO_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!st0 a m sha shm vv s G tn. _ ==> _` (drule_all_then mp_tac) >>
      simp[GSYM field_vv_scoped_post] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!e st0 a b sha shb op s G tn. _ ==> _` irule >>
  simp[] >> metis_tac[]
QED
