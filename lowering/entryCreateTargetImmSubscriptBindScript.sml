(* Selected constructor-immutable target subscript: base, index, then suffix. *)
Theory entryCreateTargetImmSubscriptBind
Ancestors
  entryCreateImmSubscriptIntervals entryCreateScopedBind entryCreateReplayBind
  bodyFullTargetSubscript bodyFullImmSubscriptIndexPre bodyFullTargetRoots
  bodyInvCodeProps bodyFullShared gasShadowCompileStmtHelpers
  immutableDeployAssignFacts allocLimits vyperTypeEnv targetPlaceSim
  exprLowering compileEnv entryCreateCompletedCut entryCreateFocusSpec exprSimDefs
  vyperState finite_map bodyFullTargetDefs vyperTypeSystem exprSimHypsDefs
  targetSubscriptContinuation gasShadowState gasShadow exprLoweringProps
  fragExec entryCreateIntervalLayout exprSimFullBundleProps gasContext
  targetPlaceSimCases s1PrefixDefs fragGasOriginPtrExec vyperStorageFootprint

(* Only the suffix implementation is abstract. This is the same sequent as
   immutable_target_array_tail with its physical interval and cut exposed. *)
Definition immutable_array_tail_rule_def:
  immutable_array_tail_rule <=>
  !tops ctx cenv cx env ee st0 id off itv iv k etv bd et av arg iop sgn sn dst sb
   s G tn iw i func sa s0 DF lo es d G0 tn0 explicit PG path.
  body_inv tops ctx cenv cx /\ cenv.ce_is_ctor /\ cenv.ce_module = NONE /\
  expr_sim_inv cenv cx env ee /\ ee.gas_obs = [] /\
  storage_trace_domain cx st0 ee.storage_trace /\
  FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables NONE imms) id = SOME (itv,iv) /\
  off + type_memory_size itv < dimword (:256) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  compile_array_subscript arg iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32
    (type_memory_size etv) sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb) /\
  eval_operand arg s = SOME (n2w (off+k)) /\ copy_old_operand sn arg /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  eval_operand iop s = SOME iw /\ copy_old_operand sn iop /\
  op_taint tn iop = {} /\ op_prov G iop = NONE /\
  (!l. arg <> Label l /\ iop <> Label l) /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sn /\
  sa.cs_next_var <= sn.cs_next_var /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    wb_frame cenv es ee sa s0 s /\ ghost_inv_at (DF H) lo d cenv cx ee G tn s /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
  scoped_operand_outcome (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0 sn sb
    (bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
             (ValueSubscript (IntV i))) get_place) (ee,s,G,tn)
    (\H res fin G' tn' q.
       res = INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])) /\
       imm_target_post H ctx func cenv cx es sa sb s0 fin id
         (path ++ [ValueSubscript (IntV i)]) et (dst,SOME LocCode,SOME (ValPT et)) q /\
       q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
       s0.vs_alloca_next <= q.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx fin G' tn' q /\
       target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])))
         (dst,SOME LocCode,SOME (ValPT et)) G' tn' q /\
       op_prov G' dst = NONE /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sn sb explicit ctx func (cx_tops cx) cx st0
    (bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
             (ValueSubscript (IntV i))) get_place) (ee,s)
End

Theorem immutable_target_compiled_type[local]:
  !bt cenv root st r s pt.
  FLOOKUP cenv.ce_module_vars root = SOME (ImmutableLoc off) /\
  cenv.ce_hashmap_info root = NONE /\ target_root bt = TopLevelNameTarget root /\
  compile_get_target_ptr cfn cenv bt st = (r,s) /\
  target_place_type cenv bt = SOME pt ==>
  FST (SND r) = SOME LocCode /\ SND (SND r) = SOME pt
Proof
  recInduct targetPlaceSimCasesBaseTheory.base_assignment_target_induct >>
  rpt conj_tac >> simp[target_root_def]
  >- (rpt strip_tac >> gvs[Once compile_get_target_ptr_def,comp_return_def,target_place_type_def]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `compile_get_target_ptr cfn cenv bt st` >>
  rename1 `compile_get_target_ptr _ _ bt _ = (rb,sm)` >>
  Cases_on `target_place_type cenv bt` >> fs[target_place_type_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `compile_get_target_ptr _ _ _ st = (r,_)`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_get_target_ptr_def]) >>
  Cases_on `x` >> fs[comp_bind_def,LET_THM,comp_return_def] >>
  rpt (pairarg_tac >> fs[comp_bind_def,comp_return_def,LET_THM]) >>
  strip_tac >> gvs[] >> Cases_on `t` >> gvs[AllCaseEqs()]
QED

Theorem immutable_bind_laws[local]:
  immutable_scoped_bind_law (:'a) (:'b) /\ immutable_replay_bind_law (:'a) (:'b)
Proof
  conj_tac
  >- (rewrite_tac[immutable_scoped_bind_law_def] >>
      rpt gen_tac >> MATCH_ACCEPT_TAC scoped_operand_bind_all_mixed) >>
  rewrite_tac[immutable_replay_bind_law_def] >>
  rpt gen_tac >> MATCH_ACCEPT_TAC create_operand_cut_bind_replay
QED

Theorem immutable_scope_post_map[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b src (es,s,G,tn) Q R /\
  (!H res ee G' tn' t.
    (?xs. !tail. src (es with gas_obs := xs ++ tail) = (res,ee with gas_obs := tail)) /\
    Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b src (es,s,G,tn) Q' R'
Proof
  simp[scoped_operand_outcome_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `marks` assume_tac) strip_assume_tac) >>
  qexists_tac `marks` >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[] >> reverse disj2_tac >> simp[] >> disj1_tac >>
  qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
  gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac)
  >- (disj1_tac >> qexists_tac `t` >> simp[] >> first_x_assum irule >>
      simp[] >> qexists_tac `gas_explicit marks s.vs_gas_readings` >> simp[]) >>
  metis_tac[]
QED

Theorem immutable_shift_exit[local]:
  create_operand_exit_post C cx H (res:'a + exception) ee gt r ==>
  ?exc. res = INR exc /\ create_operand_exit_post C cx H (INR exc:'b + exception) ee gt r
Proof
  Cases_on `res` >> simp[create_operand_exit_post_def,expr_exit_def] >>
  rename1 `expr_exit (INR ex) r /\ _ ==> _` >>
  Cases_on `ex` >> Cases_on `r` >> simp[expr_exit_def,halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem create_immutable_subscript_from_tail:
  immutable_array_tail_rule /\
  body_inv tops ctx cenv cx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  immutable_root cx bt /\
  imm_target_place_sim_judgment
    (\(D,l,E,C,f,P) ts x st0 a b source (ee,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) ts x st0 a b source (ee,s,G,tn) Q R /\
      create_operand_cut a b E C f ts x st0 source (ee,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  (!mid st0 a b sha shb op t G tn.
     body_const_cells_agree [(NONE,tops)] cx env mid /\
     expr_sim_inv cenv cx env mid /\ expr_body_pre cenv cx env e mid /\
     body_expr_full_ok cx e /\ create_layout a b /\
     expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type e) e mid (st0,a,b,sha,shb,op,t,G,tn) ==>
     scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 a b (bind (eval_expr cx e) (read_result cx)) (mid,t,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (mid,a,b,t,op,G,tn))
       (create_operand_exit_post ctx cx) /\
     create_operand_cut a b (gas_explicit_sites ctx shadow_ctx) ctx func
       (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,t)) ==>
  imm_target_place_sim_judgment
    (\(D,l,E,C,f,P) ts x st0 a b source (ee,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) ts x st0 a b source (ee,s,G,tn) Q R /\
      create_operand_cut a b E C f ts x st0 source (ee,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env
    (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[imm_target_place_sim_judgment_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> strip_tac >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = _`
    (strip_assume_tac o REWRITE_RULE [type_place_target_SubscriptTarget]) >>
  drule_all_then strip_assume_tac immutable_target_place_type >> gvs[] >>
  rename1 `type_place_target env bt = SOME (Type bty)` >>
  `?et bd. bty = ArrayT et bd` by (Cases_on `bty` >> fs[subscript_vtype_def]) >> gvs[] >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule_all_then strip_assume_tac typed_immutable_target_root >>
  `cenv.ce_hashmap_info (NONE,id) = NONE` by fs[expr_sim_inv_def] >>
  drule_all_then (strip_assume_tac o Q.SPEC `compile_expr`)
    immutable_assign_target_layout >>
  drule_then strip_assume_tac target_subscript_compile_decompose >>
  drule_all_then strip_assume_tac immutable_target_compiled_type >>
  `rb = (FST rb,SOME LocCode,SOME (ValPT (ArrayT et bd)))` by
    (PairCases_on `rb` >> gvs[]) >>
  drule_all_then strip_assume_tac target_subscript_compile_intervals >>
  `?shadow_sm.
     compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
     gas_shadow_state sm shadow_sm` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_def] (Q.INST [`sd` |-> `T`, `cenv` |-> `cenv`, `bt` |-> `bt`] gas_shadow_stmt_get_target_ptr_env)) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     Cases_on `compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa` >> simp[]) >>
  `?shadow_sn.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sm = (ix,shadow_sn) /\
     gas_shadow_state sn shadow_sn` by
    (mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`sd` |-> `T`, `ty` |-> `expr_type e`] gas_shadow_stmt_lower_value_env)) >>
     disch_then (qspecl_then [`sm`,`shadow_sm`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sm` >> simp[]) >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\ ci_mono shadow_sn shadow_sb` by
    (qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target (SubscriptTarget _ _)) _ = _`
       (strip_assume_tac o SIMP_RULE std_ss [gas_shadow_expr_type] o
        MATCH_MP target_subscript_compile_decompose o SIMP_RULE std_ss [gas_shadow_expr_def]) >>
     irule target_subscript_compile_intervals >>
     qexistsl_tac [`gas_shadow_target bt`,`gas_shadow_env T cenv`,`gas_shadow_expr e`,
       `ix`,`r`,`rb`] >> gvs[]) >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `create_layout sa sm /\ create_layout sm sn` by
    metis_tac[create_layout_subinterval,cs_extends_refl,cs_extends_trans] >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sm,sn,shadow_sm,shadow_sn)` by
    simp[expr_sim_full_code_def] >>
  drule_then (fn th => REWRITE_TAC[th,GSYM bind_assoc]) immutable_target_subscript_source >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_place_res_ok_def] >>
     qpat_assum `gas_admissible (eval_target_place _ (SubscriptTarget _ _)) _ _`
       (qspec_then `gs` mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     simp[immutable_target_subscript_source,Once bind_def,target_place_res_ok_def]) >>
  qpat_x_assum `imm_target_place_sim_judgment _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE[imm_target_place_sim_judgment_def]) >>
  disch_then (qspecl_then [`st0`,`ArrayT et bd`,`sa`,`sm`,`shadow_sa`,
    `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >> strip_tac >>
  qpat_x_assum `NONE = cenv.ce_module`
    (fn th => let val eq = SYM th in
      RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> REWRITE_TAC [eq] >> assume_tac eq end) >>
  qmatch_asmsub_abbrev_tac
    `scoped_operand_outcome _ _ _ _ _ _ (eval_target_place cx bt) _ childQ childR` >>
  qmatch_goalsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ parentQ _` >>
  qabbrev_tac `P = \H p ee G tn t. childQ H (INL p) ee G tn t` >>
  qabbrev_tac `Idx = \(p:place) mid t G1 tn1 H v ee G2 tn2 u.
    expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (mid,sm,sn,t,ix,G1,tn1)
      H (INL v) ee G2 tn2 u` >>
  `body_inv (cx_tops cx) ctx cenv cx` by (drule body_inv_main_code >> simp[]) >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  qpat_assum `Abbrev (childR = _)`
    (fn th => ONCE_REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  irule immutable_subscript_selected_binds >>
  simp[immutable_bind_laws] >>
  qexistsl_tac [`Idx`,`P`,`FST rb`,`bd`,`cenv`,`et`,`ix`,`LocCode`,`r`,`sm`,`sn`] >>
  simp[] >> reverse conj_tac
  >- suspend "base_post" >>
  qx_genl_tac [`left`,`p`,`mid1`,`t1`,`G1`,`tn1`] >> strip_tac >>
  suspend "selected_index"
QED

Resume create_immutable_subscript_from_tail[base_post]:
  conj_tac
  >- (qpat_assum `rb = (FST rb,_,_)`
        (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  irule immutable_scope_post_map >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ (eval_target_place _ _) _ _ _`
    (irule_at Any) >>
  simp[Abbr `P`] >> conj_tac
  >- (qunabbrev_tac `childQ` >> simp[] >> metis_tac[]) >>
  qunabbrev_tac `childR` >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]
QED

Resume create_immutable_subscript_from_tail[selected_index]:
  qpat_x_assum `immutable_subscript_return _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_subscript_return_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `P` >> qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid1.storage_trace`
      (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
  rename1 `p = ImmutablePlace NONE id path` >>
  qpat_x_assum `p = ImmutablePlace NONE id path` SUBST_ALL_TAC >>
  `eval_base_place cx bt (es with gas_obs := gas_explicit left s0.vs_gas_readings) =
      (INL (PlaceR (ImmutablePlace NONE id path)),mid1) /\
   body_const_cells_agree [(NONE,tops)] cx env mid1 /\
   expr_sim_inv cenv cx env mid1 /\ expr_body_pre cenv cx env e mid1 /\
   body_expr_full_ok cx e /\
   expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e mid1 (st0,sm,sn,shadow_sm,shadow_sn,ix,t1,G1,tn1)` by
    suspend "index_pre" >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e mid1 (st0,sm,sn,shadow_sm,shadow_sn,ix,t1,G1,tn1)` by
    (qpat_assum `expr_sim_full_hypotheses _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [expr_sim_full_hypotheses_def,expr_sim_full_code_def,
       expr_sim_full_pre_def,GSYM CONJ_ASSOC] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!mid st0 a b sha shb op t G tn. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`mid1`,`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`ix`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >> simp[] >> conj_tac
  >- suspend "index_post" >>
  suspend "tail"
QED

Resume create_immutable_subscript_from_tail[index_pre]:
  irule immutable_subscript_index_pre >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G0`,`ArrayT et bd`,`rb`,`sa`,`tn0`] >> simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >> gvs[]
QED

Resume create_immutable_subscript_from_tail[index_post]:
  irule immutable_scope_post_map >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (irule_at Any) >>
  simp[Abbr `Idx`,expr_sim_full_post_def] >>
  qunabbrev_tac `childR` >> BETA_TAC >> rpt gen_tac >>
  rewrite_tac[create_operand_exit_post_def] >>
  MATCH_ACCEPT_TAC (REWRITE_RULE [create_operand_exit_post_def] immutable_shift_exit)
QED

Resume create_immutable_subscript_from_tail[tail]:
  qx_genl_tac [`right`,`v`,`mid2`,`t2`,`G2`,`tn2`] >>
  disch_then (strip_assume_tac o REWRITE_RULE [immutable_subscript_return_def]) >>
  `eval_target_place cx bt (es with gas_obs := gas_explicit left s0.vs_gas_readings) =
     (INL (ImmutablePlace NONE id path),mid1)` by
    (`mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid1 with gas_obs := [] = mid1`
       (fn th => pure_rewrite_tac [listTheory.APPEND_NIL,th]) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (mid1 with gas_obs := gas_explicit right t1.vs_gas_readings) = (INL v,mid2)` by
    (`mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid2 with gas_obs := [] = mid2`
       (fn th => pure_rewrite_tac [listTheory.APPEND_NIL,th]) >> simp[]) >>
  qunabbrev_tac `Idx` >> RULE_ASSUM_TAC BETA_RULE >>
  match_mp_tac (ONCE_REWRITE_RULE [AND_IMP_INTRO]
    (Q.INST [`iop` |-> `ix`, `base_gas` |-> `gas_explicit left s0.vs_gas_readings`,
      `index_gas` |-> `gas_explicit right t1.vs_gas_readings`] immutable_subscript_tail_at_index)) >>
  simp[create_operand_at_def] >> conj_tac
  >- (conj_tac
      >- (gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
            (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >> gvs[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
        (qspec_then `storage_trace_horizon mid2.storage_trace`
          (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
            [expr_sim_full_post_def,expr_sim_full_endpoint_def]))) >> simp[] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def])) >> simp[]) >>
  qx_genl_tac [`etv`,`itv`,`current`,`k`,`av`,`iw`,`dst`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  disch_then (mk_asm "tail_map") >>
  qabbrev_tac `i = if is_signed_type (expr_type e) then w2i iw else &(w2n iw)` >>
  `v = IntV i` by simp[Abbr `i`] >>
  qabbrev_tac `src = bind (extend_place cx (PlaceR (ImmutablePlace NONE id path))
                         (ValueSubscript (IntV i))) get_place` >>
  qabbrev_tac `tailQ = \H (res:place + exception) ee G tn t.
    res = INL (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])) /\
    imm_target_post H ctx func cenv cx es sa sb s0 ee id
      (path ++ [ValueSubscript (IntV i)]) et (dst,SOME LocCode,SOME (ValPT et)) t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
    target_ptr_ok cenv (PlaceR (ImmutablePlace NONE id (path ++ [ValueSubscript (IntV i)])))
      (dst,SOME LocCode,SOME (ValPT et)) G tn t /\
    op_prov G dst = NONE /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn` >>
  `scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 sn sb src (mid2,t2,G2,tn2) tailQ
     (create_operand_exit_post ctx cx) /\
   create_operand_cut sn sb (gas_explicit_sites ctx shadow_ctx) ctx func
     (cx_tops cx) cx st0 src (mid2,t2)` by suspend "suffix_pair" >>
  simp[] >> irule immutable_scope_post_map >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ src _ tailQ _` (irule_at Any) >>
  reverse conj_tac
  >- simp[Abbr `childR`,create_operand_exit_post_def] >>
  simp[Abbr `tailQ`] >> rpt gen_tac >> strip_tac >>
  asm "tail_map" irule >> simp[] >> qexists_tac `xs` >> simp[]
QED

Resume create_immutable_subscript_from_tail[suffix_pair]:
  simp[Abbr `tailQ`,Abbr `src`] >>
  qpat_x_assum `immutable_array_tail_rule`
    (irule o SPEC_ALL o REWRITE_RULE [immutable_array_tail_rule_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid2.storage_trace`
      (drule_then (strip_assume_tac o SIMP_RULE (srw_ss())
        [expr_sim_full_post_def,expr_sim_full_endpoint_def]))) >>
  simp[Abbr `i`,arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> stmt_state_rel H ctx func cenv cx mid2 t2 /\ _`
        (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (qexistsl_tac [`FST rb`,`ix`,`iw`,`is_signed_type (expr_type e)`] >> simp[]) >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[]
QED

Finalise create_immutable_subscript_from_tail
