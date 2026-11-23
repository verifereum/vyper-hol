(* A tuple selection has one recursive evaluation and one native ADD. *)
Theory entryCreateSubscriptTuple
Ancestors
  entryCreateSubscriptLayout entryCreateRegionLift entryCreateNativeFirstExit
  entryCreateIntervalLayout createSizePrefixReplay fragGasOriginPtrExec
  entryCreatePendingScope entryCreateScopedBind entryCreateEffectFocus
  entryCreatePathScope entryCreateFocusSpec entryCreateStmtCases
  entryCreateCompletedCut entryCreateBodyCut entryCreateAdminSequence
  createSizeOperandCode createSizeCutRegion createSizeCutCode
  bodyFullEmptyLeafData bodySim s1PrefixDefs exprSimFullBundleProps
  exprSimTuple exprSimAttributeProps exprSimHyps exprSimUnwrap emitHelperProps
  gasShadow gasShadowState gasShadowCompilePure gasShadowCompileStmtHelpers
  gasExemptCert gasOutcomeFullCompose gasSummary fragGasOriginPtr
  fragGasOrigin fragExec exprLoweringProps exprLowering gasExplicitSites
  abiEncoderProps compileEnv context venomInst venomState venomExecSemantics
  vyperStorageTrace vyperStorageFootprint vyperAST vyperInterpreter vyperState list
  ASCIInumbers string

Theorem tuple_suffix_admin[local]:
  emit_op ADD [baseop; Lit off] sm = (dst,sb) ==>
  cs_extends sm sb /\ sb.cs_current_bb = sm.cs_current_bb /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  sm.cs_next_id <= sb.cs_next_id /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
             i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (emitted_insts sm sb)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  fs[same_blocks_def, cs_extends_def, mk_inst_def, is_terminator_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem tuple_base_install[local]:
  expr_body_pre ce cx env obj es /\
  expr_type obj = TupleT tys /\ place_type ce obj = ValPT (TupleT tys) /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  emit_op ADD [vv_operand bvv; Lit off] sm = (dst,sb) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Subscript ann obj (Literal ity (IntL (&k)))) es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  fn_has_code sm sb func /\
  ?shm. expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty obj es
    (st0,sa,sm,sha,shm,bvv,s0,G0,tn0)
Proof
  strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[compile_expr_extends, tuple_suffix_admin] >>
  fs[expr_vv_sim_full_pre_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  simp[] >>
  `?shm. compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha =
      (bvv,shm) /\ gas_shadow_state sm shm` by
    (mp_tac (Q.INST [`sd` |-> `T`, `e` |-> `obj`, `cenv` |-> `ce`]
       gas_shadow_stmt_compile_expr_env) >>
     pure_rewrite_tac [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`sha`] mp_tac) >>
     Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha` >> simp[]) >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  qexists_tac `shm` >> simp[] >>
  `cs_extends sha shm` by metis_tac[compile_expr_extends] >>
  `cs_extends shm shb` suffices_by
    (strip_tac >>
     `fn_has_code sha shm shfunc` by (drule_all fn_has_code_split >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _`
    (mp_tac o REWRITE_RULE [gas_shadow_expr_def]) >> strip_tac >>
  drule_at (Pat `compile_expr _ _ (Subscript _ _ _) _ = _`) compile_expr_tuple_subscript >>
  simp[gas_shadow_place_type] >> strip_tac >> gvs[] >>
  metis_tac[tuple_suffix_admin]
QED

(* A suffix visit is administrative even when the selected source evaluation
   is not successful. In particular there is no pending child of the ADD. *)
Theorem tuple_suffix_visit[local]:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code sm sb func /\ emit_op ADD [baseop; Lit off] sm = (dst,sb) /\
  create_interior_visit sm sb E ctx func (p,d,k) t (back,hit,after) ==>
  ?key inst u. hit = (key,func,inst,u) /\
    inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2
Proof
  strip_tac >> drule create_subscript_tuple_suffix_code >> strip_tac >>
  `create_cut_region sm sb t` by
    (drule_all create_cut_region_rules >> disch_then (irule o cj 1) >>
     fs[create_interior_visit_def, create_operand_at_def]) >>
  drule create_interior_visit_cases >> strip_tac >>
  `create_cut_region sm sb u` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_operand_fetch_def,create_operand_at_def,EVERY_MEM] >> metis_tac[]
QED

Theorem tuple_selected_cut[local]:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ create_cut_code {} sa sm /\
  emit_op ADD [baseop; Lit off] sm = (dst,sb) /\
  create_operand_cut sa sm E ctx func tops cx st0 (eval_expr cx obj) (es,s0) ==>
  create_operand_cut sa sb E ctx func tops cx st0
    (eval_expr cx (Subscript ann obj (Literal ity (IntL (&k))))) (es,s0)
Proof
  strip_tac >> drule create_subscript_tuple_suffix_code >> strip_tac >>
  simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >> strip_tac
  >- (simp[tuple_source] >> irule create_cut_bind_left >>
      simp[storage_trace_frame_select] >> fs[create_operand_cut_def] >> metis_tac[]) >>
  drule_all tuple_suffix_visit >> strip_tac >> gvs[] >>
  irule create_cut_noncreate_visit >> simp[]
QED

Theorem tuple_prefix_extend_right[local]:
  sa.cs_next_id <= sm.cs_next_id /\ create_expr_prefix sm sb E ctx func t ms u ==>
  create_expr_prefix sa sb E ctx func t ms u
Proof
  strip_tac >> irule create_expr_prefix_mono >>
  first_assum (irule_at Any) >>
  simp[create_prefix_step_def,frag_ids_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem tuple_join_full[local]:
  sa.cs_next_id <= sm.cs_next_id /\ create_expr_prefix sa sb E ctx func s left t /\
  create_operand_full_scope sm sb E ctx func t right r ==>
  create_operand_full_scope sa sb E ctx func s (left ++ right) r
Proof
  Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[tuple_prefix_extend_right,create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem tuple_join_focus[local]:
  body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_cut_code {} sm sb /\ fn_has_code sm sb func /\ create_cut_region sm sb t /\
  sa.cs_next_id <= sm.cs_next_id /\ create_expr_prefix sa sb E ctx func s left t /\
  create_operand_focus_scope sm sb E ctx func t right ==>
  create_operand_focus_scope sa sb E ctx func s (left ++ right)
Proof
  simp[create_operand_focus_scope_def] >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix sm sb E ctx func t front stop` >>
  `create_expr_prefix sa sb E ctx func s (left ++ front) stop` by
    metis_tac[tuple_prefix_extend_right,create_expr_prefix_append] >>
  qexistsl_tac [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
  `create_cut_region sm sb stop` by metis_tac[create_expr_prefix_cut_region] >>
  disj2_tac >> rpt strip_tac >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED

Theorem tuple_base_posts[local]:
  expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t <=>
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at sb t
Proof
  simp[expr_vv_sim_full_post_def,expr_sim_full_endpoint_def,
       create_operand_vv_post_def,create_operand_at_def] >>
  eq_tac >> strip_tac >> simp[] >> qexists_tac `tv` >> simp[]
QED

(* The ordinary tuple supplier is deliberately parameterized by its published
   sequent. The supplier and its legacy full client need no scoped imports. *)
Definition tuple_select_landing_law_def:
  tuple_select_landing_law <=>
  !cenv cx env obj es k tys ity gs tv mid st0 s ty sa bvv sm p sb func
   DF lo d ctx s0 G0 tn0 G1 tn1 explicit PG.
  expr_body_pre cenv cx env obj es /\
  expr_body_pre cenv cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_type obj = TupleT tys /\ post_value_type cenv obj = TupleT tys /\
  k < LENGTH tys /\
  eval_expr cx obj (es with gas_obs := gs) = (INL tv,mid) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~s.vs_halted /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))]
    sm = (p,sb) /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx obj
         (es,sa,sm,s0,bvv,G0,tn0) H (INL tv : eval_result + exception) mid G1 tn1 s) ==>
  ?tv' w t G2 tn2.
    eval_operand (vv_operand bvv) s = SOME w /\
    t = (update_var (STRING #"%" (toString sm.cs_next_var))
         (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) s
         with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!tail. select_result cx (TupleT tys) tv (ValueSubscript (IntV (&k)))
         (mid with gas_obs := tail) = (INL tv',mid with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
           (s,G1,tn1) [] (OK t,G2,tn2) /\
         expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx
           (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
           (es,sa,sb,s0,LocatedValue (EL k tys) (mk_ptr p (vv_loc bvv)),G0,tn0)
           H (INL tv' : eval_result + exception) mid G2 tn2 t)
End

Theorem tuple_selection_outcome[local]:
  tuple_select_landing_law /\
  expr_body_pre ce cx env obj es /\
  expr_body_pre ce cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_type obj = TupleT tys /\ post_value_type ce obj = TupleT tys /\ k < LENGTH tys /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))]
    sm = (p,sb) /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!tail. eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (res,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ create_operand_at sm s /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx obj
      (es,sa,sm,s0,bvv,G0,tn0) H res mid G1 tn1 s /\
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) marks (OK s,G1,tn1)) ==>
  ?tv. res = INL tv /\
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sm sb
      (select_result cx (TupleT tys) tv (ValueSubscript (IntV (&k)))) (mid,s,G1,tn1)
      (expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx
         (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
         (es,sa,sb,s0,LocatedValue (EL k tys) (mk_ptr p (vv_loc bvv)),G0,tn0)) R
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [expr_vv_sim_full_post_def]) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  rename1 `eval_expr cx obj _ = (INL tv,_)` >>
  `~s.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[APPEND_NIL,th])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx obj
      (es,sa,sm,s0,bvv,G0,tn0) H (INL tv : eval_result + exception) mid G1 tn1 s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `tuple_select_landing_law`
    (drule_all_then (qspecl_then [`PG`,`E`]
       (qx_choosel_then [`child`,`w`,`stop`,`G2`,`tn2`] strip_assume_tac)) o
     Q.INST [`explicit` |-> `E`,`PG` |-> `PG`] o
     SPEC_ALL o REWRITE_RULE [tuple_select_landing_law_def]) >>
  simp[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qexistsl_tac [`INL child`,`mid`,`OK stop`,`G2`,`tn2`] >>
  simp[gas_explicit_def] >> conj_tac
  >- (qpat_assum `stop = _` SUBST1_TAC >> irule create_subscript_tuple_suffix_scope >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

(* The scoped carrier presents posts with the GAS tail cleared. *)
Theorem tuple_clear_base_tail[local]:
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sm
    source (es,s,G,tn) Q (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 sa sm
    source (es,s,G,tn) (\H res ee G1 tn1 t. Q H res ee G1 tn1 t /\ ee.gas_obs = [])
    (\H res ee gt r. (?ex. res = INR ex) /\ create_operand_exit_post ctx cx H res ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks` >> simp[]
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[] >>
      Cases_on `res` >> fs[create_operand_exit_post_def,exprSimDefsTheory.expr_exit_def]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem tuple_bind_scoped[local]:
  tuple_select_landing_law /\ body_inv tops ctx ce cx /\ MEM func ctx.ctx_functions /\
  create_layout sa sb /\ expr_body_pre ce cx env obj es /\
  expr_body_pre ce cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_type obj = TupleT tys /\ post_value_type ce obj = TupleT tys /\ k < LENGTH tys /\
  compile_expr ce ty obj sa = (bvv,sm) /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))] sm = (p,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  create_operand_at sa s0 /\
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sm
    (eval_expr cx obj) (es,s0,G0,tn0)
    (expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx obj (es,sa,sm,s0,bvv,G0,tn0))
    (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sb
    (eval_expr cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))) (es,s0,G0,tn0)
    (expr_vv_sim_full_post (DF,lo,d,ctx,func) ce cx
       (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
       (es,sa,sb,s0,LocatedValue (EL k tys) (mk_ptr p (vv_loc bvv)),G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >> drule compile_expr_extends >> strip_tac >>
  drule tuple_suffix_admin >> strip_tac >>
  drule create_subscript_tuple_suffix_code >> strip_tac >>
  `create_cut_code {} sa sm` by
    (mp_tac (Q.SPECL [`ce`,`ty`,`obj`,`sa`] (cj 1 create_operand_cut_code)) >> simp[]) >>
  `create_cut_region sa sm s0` by
    (drule_all create_cut_region_rules >> disch_then (irule o cj 1) >> fs[create_operand_at_def]) >>
  `!u. create_cut_region sa sm u /\ ~create_operand_at sm u ==> ~create_operand_at sb u` by
    (rpt strip_tac >> drule_all create_layout_left_stop >> simp[]) >>
  `!marks t. create_operand_full_scope sa sm E ctx func s0 marks (OK t) ==>
      create_expr_prefix sa sb E ctx func s0 marks t /\ create_cut_region sm sb t` by
    (simp[create_operand_full_scope_def] >> rpt strip_tac
     >- (drule_all create_left_prefix_lift_at >> simp[]) >>
     metis_tac[cj 1 create_cut_region_rules]) >>
  drule tuple_clear_base_tail >> strip_tac >>
  simp[tuple_source] >> irule scoped_operand_bind_all >>
  first_assum (irule_at Any) >> simp[storage_trace_frame_select, evaluate_storage_trace_frame] >>
  rpt conj_tac >> rpt strip_tac
  >~ [`gas_exempt_cert _ _ _ _ _ (left ++ right) _ _`]
  >- (simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_result >> simp[GSYM ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC)
  >- metis_tac[create_left_terminal_lift_at]
  >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      `mid.gas_obs = []` by metis_tac[] >>
      irule tuple_selection_outcome >> simp[] >>
      rpt conj_tac
      >- (qexists_tac `marks` >> simp[])
      >- (qexists_tac `ty` >> simp[]) >> qexists_tac `env` >> simp[]) >>
  metis_tac[tuple_join_full,tuple_join_focus,create_left_focus_lift_at]
QED

(* The recursive callback is used only on the installed base interval. *)
Theorem create_tuple_subscript_at:
  tuple_select_landing_law /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ place_type ce obj = ValPT (TupleT tys) /\
  post_value_type ce obj = expr_type obj /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Subscript ann obj idx) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  create_layout sa sb /\
  (!sm shm bvv. expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty obj es
      (st0,sa,sm,sha,shm,bvv,s0,G0,tn0) /\ create_layout sa sm ==>
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sm
      (eval_expr cx obj) (es,s0,G0,tn0)
      (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,func) ce cx obj
         (es,sa,sm,s0,bvv,G0,tn0) H res ee G tn t /\ create_operand_at sm t)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sm E ctx func tops cx st0 (eval_expr cx obj) (es,s0)) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sb
    (eval_expr cx (Subscript ann obj idx)) (es,s0,G0,tn0)
    (\H res ee G tn t. create_operand_vv_post (DF,lo,d,ctx,func) ce cx (Subscript ann obj idx)
       (es,sa,sb,s0,vv,G0,tn0) H res ee G tn t /\ create_operand_at sb t)
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb E ctx func tops cx st0 (eval_expr cx (Subscript ann obj idx)) (es,s0)
Proof
  strip_tac >>
  `compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb)` by
    fs[expr_vv_sim_full_pre_def] >>
  drule_all create_subscript_tuple_layout >> strip_tac >>
  gvs[exprLoweringTheory.literal_int_index_def] >>
  drule_all tuple_base_install >> strip_tac >>
  drule_then strip_assume_tac compile_expr_extends >>
  drule_then strip_assume_tac tuple_suffix_admin >>
  `create_layout sa sm` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  qpat_assum `!sm shm bvv. _ ==> _ /\ _`
    (qspecl_then [`sm`,`shm`,`bvv`] mp_tac) >>
  simp[GSYM tuple_base_posts] >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ (Subscript _ _ _) _ _` kall_tac >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ obj _ _`
    (strip_assume_tac o REWRITE_RULE [expr_vv_sim_full_pre_def]) >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  conj_tac
  >- (CONV_TAC (DEPTH_CONV ETA_CONV) >>
      rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
      irule tuple_bind_scoped >>
      simp[] >> rpt conj_tac
      >- (qexists_tac `tops` >> simp[])
      >- (qexists_tac `env` >> simp[]) >> qexistsl_tac [`sm`,`ty`] >> simp[]) >>
  irule tuple_selected_cut >>
  qpat_assum `create_operand_cut sa sm _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[cj 1 create_operand_cut_code,pairTheory.SND]
QED
