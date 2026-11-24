(* Finite-horizon composition for a framed runtime code-array base. *)
Theory bodyFullSubscriptArrayCode
Ancestors vyperTyping[qualified,ignore_grammar] vyperValueOperation[qualified,ignore_grammar] exprSimHypsDefs[qualified,ignore_grammar]
  bodyFullShadowBodyInv
  bodyFullOfVV bodyFullPreds bodyFullSimProjection bodySimFull gasOutcomeFullCompose
  bodyFullAttributeAdd bodyFullGhostFrame bodyFullPathHistory
  bodyFullSubscriptArrayCodeBounds bodyFullSubscriptArrayCodeOps
  bodyFullEmptyLeafData exprSimFullBundleProps
  bodyFullIfExpReach bodyFullHashKeccakFixed stateRelProj exprSimSubscriptArraySuffix
  gasShadowCompileStmtHelpers bodyPtrPrecompileBuiltinsGhost
  exprSimSubscriptArrayEndpoint exprSimSubscriptArrayOrigin
  exprSimSubscriptArrayCompose exprSimSubscriptArraySource
  exprSimSubscriptArrayFramed exprSimHyps exprSimSource
  exprOperandVar exprLoweringProps exprSimUnwrap fragExec
  exprSimVVFrame exprSimProps
  gasShadowCompile gasShadowState gasShadow gasExemptCert
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom
  bodyPtrDefs loweringPosts compileEnv vyperInterpreter vyperState vyperAST
  bodyFullBuiltinWordPowCompose[qualified,ignore_grammar]

Theorem code_array_operand_readonly_tail[local]:
  (!q. op = Var q ==> not_fresh_at st q) /\
  (!l. op <> Label l) /\
  (!q. not_fresh_at st q ==> lookup_var q sf = lookup_var q it) ==>
  eval_operand op sf = eval_operand op it
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def] >>
  rpt strip_tac >> simp[]
QED

Theorem code_array_post_readonly_tail[local]:
  vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin tv (LocatedValue (ArrayT et bd) p) it /\
  p.ptr_location = LocCode /\
  sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
  contract_storage sf = contract_storage it /\
  contract_transient sf = contract_transient it /\
  eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it /\
  (!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x it) /\
  stmt_state_rel H ctx func cenv cx fin sf ==>
  vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa sb s0 fin tv (LocatedValue (ArrayT et bd) p) sf
Proof
  simp[expr_type_def] >> strip_tac >>
  `vv_holds cenv cx (ArrayT et bd) tv (LocatedValue (ArrayT et bd) p) fin sf` by
    (irule vv_holds_vars_frame >> qexists_tac `it` >>
     gvs[vv_post_def, expr_type_def, contextTheory.vv_operand_def]) >>
  `locals_kept cenv es fin s0 sf` by
    (irule locals_kept_mem_tail >> qexists_tac `it` >> gvs[vv_post_def]) >>
  `pure_frame cenv func es sa s0 sf <=> pure_frame cenv func es sa s0 it` by
    (irule pure_frame_state_cong >> simp[]) >>
  `vv_place_ptr cenv cx fin sf tv (LocatedValue (ArrayT et bd) p)` by
    (Cases_on `tv` >> gvs[vv_post_def, vv_place_ptr_def, slot_loc_def] >>
     rename1 `PlaceR pl` >> Cases_on `pl` >>
     gvs[vv_place_ptr_def, slot_loc_def] >> metis_tac[]) >>
  gvs[vv_post_def, vv_at_def, vv_own_def, expr_type_def] >>
  metis_tac[]
QED

Theorem code_array_selected_post_tail[local]:
  vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa st2 s0 fin tv (LocatedValue (ArrayT et bd) p) it /\
  p.ptr_location = LocCode /\
  sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
  contract_storage sf = contract_storage it /\
  contract_transient sf = contract_transient it /\
  eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it /\
  (!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x it) /\
  stmt_state_rel H ctx func cenv cx fin sf /\
  eval_operand p.ptr_operand it = SOME w /\
  expr_type obj = ArrayT et bd /\
  read_result cx tv fin = (INL (ArrayV av),fin) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf etv v /\ value_has_type etv v /\
  read_result cx child fin = (INL v,fin) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst sf = SOME (w + n2w j) /\
  expr_sim_inv cenv cx env mid /\
  eval_result_typed (env,cx,mid) tv (Type (ArrayT et bd)) /\
  fin.scopes = mid.scopes /\ fin.immutables = mid.immutables /\
  (!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx (ArrayT et bd) tv (ValueSubscript (IntV i)) fin = (INL child,fin) /\
  mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  (!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV i)] /\ tv = PlaceR (MemoryPlace id path)) ==>
  vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
    (LocatedValue et (mk_ptr dst LocCode)) sf
Proof
  strip_tac >>
  `vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx)
    es sa sb s0 fin tv (LocatedValue (ArrayT et bd) p) sf` by
    (metis_tac[code_array_post_readonly_tail]) >>
  `vv_place_ptr cenv cx fin sf tv (LocatedValue (ArrayT et bd) p)` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ sb _ _ _ _ sf` mp_tac >>
     simp[NoAsms, vv_post_def]) >>
  `eval_operand p.ptr_operand sf = SOME w` by simp[] >>
  `vv_place_ptr cenv cx fin sf child (LocatedValue et (mk_ptr dst p.ptr_location))` by
    (irule exprSimHashTheory.vv_place_ptr_select_step >> simp[] >>
     goal_assum (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_result_typed _ _ _`)) >> simp[] >>
     qexists_tac `ArrayT et bd` >> simp[]) >>
  `LocCode = p.ptr_location` by simp[] >> pop_assum SUBST1_TAC >>
  irule vv_post_array_element >> simp[] >>
  qexistsl_tac [`ArrayT et bd`, `av`, `i`, `tv`] >> simp[]
QED

Theorem code_array_ghost_readonly_tail[local]:
  ghost_inv_at D lo d cenv cx fin G tn it /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv st2 /\ sa.cs_next_var <= st2.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x. not_fresh_at st2 x ==>
    lookup_var x sf = lookup_var x it /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  sf.vs_memory = it.vs_memory /\ sf.vs_allocas = it.vs_allocas /\
  sf.vs_alloca_next = it.vs_alloca_next /\
  sf.vs_call_ctx = it.vs_call_ctx /\ sf.vs_accounts = it.vs_accounts /\
  sf.vs_transient = it.vs_transient /\ sf.vs_immutables = it.vs_immutables /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm ==>
  ghost_inv_at D lo d cenv cx fin Gf tnf sf /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >> conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `fin`, `it`, `st2`, `tn`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at st2 x` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  gvs[ghost_kept_at_def] >>
  conj_tac >- metis_tac[] >> metis_tac[]
QED

(* The selector supplies the ordinary post at its chosen landing, before
   that landing is hidden by the existential in gas_outcome_full. *)
Theorem code_array_selected_landing:
  ~cenv.ce_is_ctor /\ fin.gas_obs = [] /\
  (!tail. select_result cx (ArrayT et bd) tv (ValueSubscript (IntV i))
     (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)) /\
  (!v. child <> Value v) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (it,Gi,tni) [] (OK sf,Gf,tnf) /\
    vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
      (LocatedValue et (mk_ptr out LocCode)) sf /\
    ghost_inv_at (DF H) lo d cenv cx fin Gf tnf sf) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf /\
  expr_sim_full_endpoint func sb s0 sf /\
  op_taint tnf out = {} /\ op_prov Gf out = NONE ==>
  (!tail. select_result cx (ArrayT et bd) tv (ValueSubscript (IntV i))
     (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (it,Gi,tni) [] (OK sf,Gf,tnf) /\
    expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript et obj idx)
      (es,sa,sb,s0,LocatedValue et (mk_ptr out LocCode),G0,tn0)
      H (INL child : eval_result + exception) fin Gf tnf sf)
Proof
  strip_tac >> conj_tac >- simp[] >> qx_gen_tac `H` >> strip_tac >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sf` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms,vv_post_def] >> strip_tac >>
     first_assum (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  simp[expr_vv_sim_full_post_def,expr_type_def,contextTheory.mk_ptr_def,
       exprSimMemDefsTheory.vv_store_bound_nonmem,ptr_vv_ok_def] >>
  fs[contextTheory.mk_ptr_def]
QED

Theorem code_array_selected_outcome_tail[local]:
  ~it.vs_halted /\ ~cenv.ce_is_ctor /\ fin.gas_obs = [] /\
  (!tail. select_result cx (ArrayT et bd) tv (ValueSubscript (IntV i))
     (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)) /\
  (!v. child <> Value v) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (it,Gi,tni) [] (OK sf,Gf,tnf) /\
    vv_post H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin child
      (LocatedValue et (mk_ptr out LocCode)) sf /\
    ghost_inv_at (DF H) lo d cenv cx fin Gf tnf sf) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf /\
  sf.vs_current_bb = sb.cs_current_bb /\
  sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func sf /\ s0.vs_alloca_next <= sf.vs_alloca_next /\
  op_taint tnf out = {} /\ op_prov Gf out = NONE ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et bd) tv (ValueSubscript (IntV i)))
    (fin,it,Gi,tni)
    (expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Subscript et obj idx)
      (es,sa,sb,s0,LocatedValue et (mk_ptr out LocCode),G0,tn0)) R
Proof
  strip_tac >>
  `expr_sim_full_endpoint func sb s0 sf` by simp[expr_sim_full_endpoint_def] >>
  drule_all code_array_selected_landing >> strip_tac >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`Gf`, `fin`, `INL child`, `sf`, `tnf`] >>
  `fin with gas_obs := [] = fin` by
    (qpat_x_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!K. valid_horizon _ _ K _ ==> _ /\ expr_vv_sim_full_post _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Theorem subscript_array_framed_code_full:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 /\ body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et bd /\
    place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
       eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    ~cenv.ce_is_ctor /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e1 es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base,
              exprSimTopLevelPropsTheory.array_slot_base_compile_location] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e1 es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  simp[expr_vv_sim_full_via_bundle,expr_vv_sim_full_hypotheses_def,
       expr_sim_full_code_def] >>
  qx_genl_tac [`st0`, `sa`, `sb`, `shadow_sa`, `shadow_sb`, `vv`, `s0`, `G0`, `tn0`] >>
  strip_tac >> drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty e1 sa = (bvv,sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by
    (irule cs_extends_trans >> qexists_tac `st2` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1)
       shadow_sa = (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e1)
        (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa` >> simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    suspend "shadow_extends" >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx e1) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> (gvs[]))) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  suspend "bind_base"
QED

Resume subscript_array_framed_code_full[shadow_extends]:
  reverse conj_tac
  >- (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
      simp[gas_shadow_expr_def] >> strip_tac >>
      qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr e1) _) _ = _`
        (mp_then Any mp_tac compile_expr_array_subscript) >>
      fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
      rename1 `lower_value _ _ _ (gas_shadow_expr e2) shadow_sm = (_,shadow_st2)` >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) _ = _`
        (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
      `cs_extends shadow_st2 shadow_sb` by
        (`ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
         qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
           (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
         irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
      irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  drule compile_expr_extends >> simp[]
QED

Resume subscript_array_framed_code_full[bind_base]:
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule gas_outcome_full_bind_all_path >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >> simp[] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_select] >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_base" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`]
  >> (metis_tac[])
QED

Resume subscript_array_framed_code_full[after_base]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> simp[]) >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_x_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `body_expr_full_ok cx e2` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  `?shadow_st2. lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2)
      shadow_sm = (iop,shadow_st2) /\ gas_shadow_state st2 shadow_st2` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e2)
        (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sm`, `shadow_sm`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr e2) shadow_sm` >> simp[]) >>
  `cs_extends shadow_sm shadow_st2 /\ cs_extends shadow_st2 shadow_sb` by
    (`cs_extends shadow_sm shadow_st2` by
       (qpat_assum `lower_value _ _ _ _ shadow_sm = _`
          (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     drule compile_expr_array_subscript >>
     fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
     `ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `fn_has_code sm st2 func /\ fn_has_code shadow_sm shadow_st2 shadow_func` by
    metis_tac[fn_has_code_split] >>
  `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
      es sa sm s0 mid tv bvv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> fs[vv_post_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `st2`, `shadow_sm`, `shadow_st2`,
                          `iop`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt conj_tac
     >~ [`local_ptrs_reserved _ _`] >- metis_tac[local_ptrs_reserved_next_var]
     >~ [`gas_admissible _ _ _`] >- metis_tac[expr_body_pre_gas_admissible]
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
           metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G1,tn1)` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
           qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
             (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
              CONJ path o CONJ no_phi))))
     >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[vv_post_def])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ indexQ indexR` >>
  irule gas_outcome_full_bind_all >> simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "selection" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >>
  conj_tac >- simp[Abbr `indexR`, Abbr `baseR`] >>
  simp[Abbr `indexQ`, Abbr `indexR`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def] >>
  strip_tac >> conj_tac
  >- (irule exprSimHashTheory.expr_exit_INR_cast >> first_assum ACCEPT_TAC) >>
  gvs[exprSimDefsTheory.halt_exit_def]
QED

Resume subscript_array_framed_code_full[selection]:
  qx_genl_tac [`imarks`, `ires`, `fin`, `Gi`, `tni`, `it`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `indexQ (storage_trace_horizon fin.storage_trace) ires fin Gi tni it /\
   ~it.vs_halted /\ fin.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `indexQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `indexQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) = (INL v,fin)` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[] >>
     `fin with gas_obs := [] = fin` by
       (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `?ir. eval_expr cx e2 (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) =
      (INL ir,fin) /\ read_result cx ir fin = (INL v,fin)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> gvs[] >> metis_tac[]) >>
  `fin.scopes = mid.scopes /\ fin.immutables = mid.immutables` by
    (qpat_x_assum `!t r t'. eval_expr cx e2 t = _ ==> _` drule >> simp[]) >>
  `vv_location bvv = SOME LocCode` by metis_tac[pairTheory.FST] >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode` by
    (`vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
       es sa sm s0 mid tv bvv s` by metis_tac[] >>
     Cases_on `bvv` >> gvs[contextTheory.vv_location_def] >>
     metis_tac[vv_post_def, vv_holds_def, is_bytestring_type_def]) >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `!l. p.ptr_operand <> Label l` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac compile_array_pointer_not_label) >>
     disch_then irule >> simp[] >>
     qexists_tac `env` >> (metis_tac[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def])) >>
  `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` by metis_tac[] >>
  `expr_body_pre cenv cx env e2
     (mid with gas_obs := gas_explicit imarks s.vs_gas_readings)` by simp[] >>
  `?itv. evaluate_type (get_tenv cx) (expr_type e2) = SOME itv /\
     value_has_type itv v` by
    (drule_all expr_body_pre_runtime_typed >> strip_tac >> metis_tac[]) >>
  `expr_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx e2
     mid sm st2 s fin v iop it` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type e2)` by
    (qpat_x_assum `value_has_type itv v` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     qpat_x_assum `v = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type e2` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `ann = et` by
    (`well_typed_expr env (Subscript ann e1 e2) /\ well_typed_expr env e1` by
       metis_tac[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  gvs[] >>
  `ghost_kept cenv mid sm G1 tn1 s Gi tni` by
    (qpat_x_assum `ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `!l. iop <> Label l` by
    (qpat_assum `lower_value compile_expr cenv ty e2 sm = _`
       (mp_then Any mp_tac exprReasonOperandTheory.lower_compile_expr_not_label) >>
     disch_then (qspec_then `env` mp_tac) >>
     metis_tac[exprSimHypsDefsTheory.expr_body_pre_def,
               exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
     vv_post H ctx func cenv cx (Subscript (ArrayT ann bd) e1 e2)
       es sa st2 s0 fin tv (LocatedValue (ArrayT ann bd) p) it` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H mid.storage_trace` by
       (qpat_assum `bind _ _ _ = _` (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _` drule >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     `stmt_state_rel H ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx fin it` by
       metis_tac[expr_post_def] >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
     irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `env` >> simp[]) >>
  `vv_post (storage_trace_horizon fin.storage_trace) ctx func cenv cx
     (Subscript (ArrayT ann bd) e1 e2)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) sa st2 s0 fin tv
     (LocatedValue (ArrayT ann bd) p) it` by
    (simp[exprSimPropsTheory.vv_post_initial_gas] >> metis_tac[]) >>
  `vv_holds cenv cx (ArrayT ann bd) tv (LocatedValue (ArrayT ann bd) p) fin it /\
   vv_at cenv cx (ArrayT ann bd) sa st2 fin tv (LocatedValue (ArrayT ann bd) p) it` by
    (qpat_assum `vv_post _ _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, vv_post_def, expr_type_def]) >>
  `op_taint tn1 p.ptr_operand = {} /\ op_prov G1 p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    (conj_tac >- metis_tac[wordArgsPtrTheory.ghost_kept_operand] >>
     `op_prov Gi p.ptr_operand = op_prov G1 p.ptr_operand` suffices_by simp[] >>
     Cases_on `p.ptr_operand` >> fs[ptrDisciplineTheory.op_prov_def, ghost_kept_def]) >>
  `ptr_vv_ok cx (ArrayT ann bd) tv (LocatedValue (ArrayT ann bd) p) fin Gi tni it` by
    simp[ptr_vv_ok_def] >>
  drule_at (Pat `vv_post _ _ _ _ _ (Subscript _ _ _) _ _ _ _ _ _ _ _`)
    framed_array_post_view >>
  disch_then (qspecl_then
    [`mid`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni` by
    (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then (Pat `f st = _`) mp_tac valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx es s0` by
       (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> simp[]) >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
       (qpat_assum `eval_expr cx e1 _ = _`
          (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
     `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
        es sa sm s0 mid tv (LocatedValue (ArrayT ann bd) p) s` by metis_tac[] >>
     `wb_frame cenv es mid sa s0 s` by
       (qpat_assum `vv_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
        simp[NoAsms, vv_post_def, wb_frame_def] >> metis_tac[]) >>
     drule_all wordArgsPtrTheory.ghost_kept_at_wb_trans >> simp[]) >>
  `valid_index (ArrayTV etv bd) av
      (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) <=>
   idx_in_range (is_signed_type (expr_type e2)) iw
      (n2w (array_length (ArrayTV etv bd) av))` by
    (irule array_index_word_bounds >> simp[]) >>
  Cases_on `valid_index (ArrayTV etv bd) av
    (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)`
  >- suspend "valid_selection" >>
  suspend "rejected_selection"
QED

Resume subscript_array_framed_code_full[valid_selection]:
  drule vyperArrayTheory.array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  `?child. select_result cx (ArrayT ann bd) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))) fin =
        (INL child,fin) /\ read_result cx child fin = (INL x,fin)` by
    (irule framed_array_select_read >> simp[] >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                    `e1`, `sa`, `mid`, `ty`] >> simp[]) >>
  `!tail. select_result cx (ArrayT ann bd) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)))
      (fin with gas_obs := tail) = (INL child,fin with gas_obs := tail)` by
    (simp[select_result_nonstorage_gas_obs]) >>
  `!v. tv <> Value v` by
    ((qpat_assum `!v. tv = Value v ==> _` mp_tac >>
     simp[is_word_type_def, is_bytestring_type_def] >> (gvs[is_word_type_def, is_bytestring_type_def]))) >>
  `!v. child <> Value v` by
    (qpat_assum `select_result _ _ _ _ fin = (INL child,fin)` mp_tac >>
     qpat_assum `read_result cx tv fin = _` mp_tac >>
     qpat_assum `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` mp_tac >>
     qpat_assum `!v. tv <> Value v` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `tv` >> simp[read_result_def, raise_def] >>
     rename1 `read_place _ pl _ = _` >> Cases_on `pl` >>
     simp[select_result_def, extend_place_def, bind_def, ignore_bind_def,
          lift_sum_def, pairTheory.ELIM_UNCURRY, AllCaseEqs(), return_def, raise_def] >>
     rpt strip_tac >> gvs[]) >>
  `well_formed_type_value etv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type etv x` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
  `val_wf etv x` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV
       (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))] /\
       tv = PlaceR (MemoryPlace id path)` by
    (qpat_assum `select_result _ _ _ _ fin = (INL child,fin)`
       (mp_tac o MATCH_MP select_result_memory_place) >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`, `mid`] >> simp[]) >>
  `Num (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) = w2n iw` by
    (Cases_on `is_signed_type (expr_type e2)` >> fs[] >>
     Cases_on `w2n iw < INT_MIN (:256)` >>
     fs[integer_wordTheory.w2i_eq_w2n] >>
     `w2n iw < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
     intLib.COOPER_TAC) >>
  `expr_body_pre cenv cx env e1
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env mid /\
   eval_result_typed (env,cx,mid) tv (Type (ArrayT ann bd))` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  `array_length (ArrayTV etv bd) av <= (case bd of Fixed n => n | Dynamic n => n)` by
    ((qpat_assum `value_has_type (ArrayTV _ _) _` mp_tac >>
     Cases_on `bd` >> Cases_on `av` >>
     simp[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def] >> (gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]))) >>
  `0 <= (if is_signed_type (expr_type e2) then w2i iw else &w2n iw) /\
   w2n iw < array_length (ArrayTV etv bd) av` by
    (qpat_assum `valid_index _ _ _` mp_tac >>
     qmatch_goalsub_abbrev_tac `valid_index _ _ i` >>
     pure_rewrite_tac[vyperArrayTheory.valid_index_def] >> strip_tac >>
     `&(Num i) = i` by simp[integerTheory.INT_OF_NUM] >>
     metis_tac[integerTheory.INT_LT]) >>
  `mem_step_offset (ArrayTV etv bd)
     (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))) =
   SOME ((case bd of Fixed _ => 0 | Dynamic _ => 32) + w2n iw * type_memory_size etv,etv)` by
    (Cases_on `bd` >> fs[mem_step_offset_def]) >>
  Cases_on `bd`
  >- suspend "fixed_selection" >>
  suspend "dynamic_selection"
QED

Resume subscript_array_framed_code_full[fixed_selection]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[oneTheory.one] >>
  `ci_mono st2 cs'` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_bounds_check_def,
          exprSimArrayIndexTheory.array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC,
                 irule ci_mono_emit_op,
                 irule ci_mono_emit_void,
                 irule ci_mono_comp_return,
                 IF_CASES_TAC])) >>
  `ci_mono cs' sb` by
    (qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC,
                 irule ci_mono_emit_op,
                 irule ci_mono_comp_return])) >>
  `cs_extends st2 cs' /\ cs_extends cs' sb` by fs[ci_mono_def] >>
  `fn_has_code st2 cs' func` by metis_tac[fn_has_code_split] >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    fs[ptr_val_ok_def] >>
  `eval_operand (Lit (n2w n)) it = SOME (n2w n) /\
   op_taint tni (Lit (n2w n)) = {} /\ op_prov Gi (Lit (n2w n)) = NONE /\
   idx_in_range (is_signed_type (expr_type e2)) iw (n2w n) /\
   (!q. iop = Var q \/ Lit (n2w n) = Var q ==> not_fresh_at st2 q) /\
   (!l. iop <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    array_bounds_check_read_only_joint_ok_frame) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gb`,`tnb`,`ib`] strip_assume_tac) >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `!q. p.ptr_operand = Var q ==> not_fresh_at st2 q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand p.ptr_operand ib = SOME w /\
   op_taint tnb p.ptr_operand = {} /\ op_prov Gb p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand iop ib = SOME iw /\ op_taint tnb iop = {} /\ op_prov Gb iop = NONE` by
    (Cases_on `iop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!q. p.ptr_operand = Var q ==> not_fresh_at cs' q` by
    metis_tac[ci_mono_def, freshWritesTheory.not_fresh_at_mono] >>
  `fn_has_code cs' sb func` by metis_tac[fn_has_code_split] >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[exprSimArrayIndexTheory.array_elem_ptr_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  `?off. offset = Var off` by
    (qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     pure_rewrite_tac[loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >> gvs[] >>
  `?out. dst = Var out` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     pure_rewrite_tac[loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >> gvs[] >>
  `eval_operand iop ib = SOME (n2w (w2n iw))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ib` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp it` mp_tac >>
     qpat_assum `ib.vs_allocas = it.vs_allocas` (fn allocas =>
       qpat_assum `ib.vs_fmp = it.vs_fmp` (fn fmp =>
         qpat_assum `ib.vs_initial_fmp = it.vs_initial_fmp` (fn initial =>
           POP_ASSUM_LIST (K all_tac) >>
           simp[ptrDisciplineTheory.allocas_below_fmp_def, allocas, fmp, initial] >>
           metis_tac[])))) >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullSubscriptArrayCodeOpsTheory.scalar_mul_add_joint_frame_observed) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`]
    (CONJUNCTS_THEN2 (mk_asm "address_run") strip_assume_tac)) >>
  `!q. not_fresh_at st2 q ==> not_fresh_at cs' q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[ci_mono_def, cs_extends_def]) >>
  `!q. not_fresh_at st2 q ==>
    lookup_var q sf = lookup_var q it /\ FLOOKUP Gf q = FLOOKUP Gi q /\
    op_taint tnf (Var q) = op_taint tni (Var q)` by
    metis_tac[] >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx fin Gf tnf sf` by
    (rpt strip_tac >>
     irule (cj 1 code_array_ghost_readonly_tail) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule (cj 2 code_array_ghost_readonly_tail) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`DF (storage_trace_horizon fin.storage_trace)`, `cx`, `d`, `fin`] >>
     simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it` by
    (irule code_array_operand_readonly_tail >> simp[] >> qexists_tac `st2` >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin sf` by
    (rpt strip_tac >> first_assum irule >> conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `st2` >>
         fs[ci_mono_def, cs_extends_def]) >>
     first_assum irule >> simp[] >> metis_tac[expr_post_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 fin child
      (LocatedValue ann (mk_ptr (Var out) p.ptr_location)) sf` by
    (rpt strip_tac >>
     `p.ptr_location = LocCode` by simp[] >>
     asm_rewrite_tac[] >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any mp_tac code_array_selected_post_tail) >>
     disch_then (drule_at (Pat `eval_result_typed _ _ _`)) >>
     disch_then (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
     disch_then irule >>
     simp[] >>
     rpt (goal_assum (drule_at Any) >> simp[]) >>
     simp[venomStateTheory.eval_operand_def, elem_size_in_location_def,
          is_slot_addressed_def, venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def,
          AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  pop_assum (mk_asm "child_post") >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
     `allocas_from lo ib` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
     qpat_assum `!D lo explicit. allocas_from lo it ==> _`
       (qspecl_then [`DF H`, `lo`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
     simp[] >> disch_then irule >> simp[]) >>
  `alloca_inv it` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     simp[NoAsms, expr_post_def] >> metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `alloca_history func sf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  irule code_array_selected_outcome_tail >> simp[] >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >>
  simp[] >> rpt strip_tac >>
  asm "child_post" (qspec_then `H` mp_tac) >> simp[]
QED

Resume subscript_array_framed_code_full[dynamic_selection]:
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[oneTheory.one] >>
  `ci_mono st2 cs'` by
    (qpat_x_assum `compile_ptr_load _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_runtime,
          ci_mono_emit_op]) >>
  `ci_mono cs' cs''` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_bounds_check_def,
          exprSimArrayIndexTheory.array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return, IF_CASES_TAC])) >>
  `ci_mono cs'' sb` by
    (qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_comp_return])) >>
  `cs_extends st2 cs' /\ cs_extends cs' cs'' /\ cs_extends cs'' sb` by fs[ci_mono_def] >>
  `fn_has_code st2 cs' func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `compile_imm_load_word F cenv.ce_imm_alloca p.ptr_operand st2 = (len_op,cs')` by
    fs[contextTheory.compile_ptr_load_def] >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `stmt_state_rel (storage_trace_horizon fin.storage_trace) ctx func cenv cx fin it` by
    metis_tac[expr_post_def] >>
  `immutable_holds cenv cx (ArrayT ann (Dynamic n)) tv w fin it` by
    (fs[vv_holds_def] >> gvs[]) >>
  `w2n w <= LENGTH it.vs_data_section` by
    (drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >>
     simp[] ) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullSubscriptArrayCodeOpsTheory.compile_imm_load_word_runtime_joint_run) >>
  disch_then (qspecl_then [`PG`, `Gi`] mp_tac) >>
  disch_then (qx_choosel_then [`lenvar`, `Gl`, `tnl`, `il`]
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 (mk_asm "length_run") strip_assume_tac)))) >>
  `word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) it.vs_data_section ++ REPLICATE 32 0w)) =
      n2w (array_length (ArrayTV etv (Dynamic n)) av)` by
    (drule_all exprSimSubscriptArraySuffixTheory.framed_array_code_length_view >> simp[]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `eval_operand iop il = SOME iw /\ op_taint tnl iop = {} /\ op_prov Gl iop = NONE` by
    (Cases_on `iop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!q. not_fresh_at st2 q ==> not_fresh_at cs' q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[ci_mono_def, cs_extends_def]) >>
  `!q. len_op = Var q ==> not_fresh_at cs' q` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime,
          loweringShapeRulesTheory.emit_op_eq] >> strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `eval_operand len_op il = SOME (n2w (array_length (ArrayTV etv (Dynamic n)) av)) /\
    (!l. len_op <> Label l)` by simp[venomStateTheory.eval_operand_def] >>
  `(!q. iop = Var q \/ len_op = Var q ==> not_fresh_at cs' q) /\
   (!l. iop <> Label l /\ len_op <> Label l)` by metis_tac[] >>
  `fn_has_code cs' cs'' func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp il` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp it` mp_tac >>
     qpat_assum `il.vs_allocas = it.vs_allocas` (fn allocas =>
       qpat_assum `il.vs_fmp = it.vs_fmp` (fn fmp =>
         qpat_assum `il.vs_initial_fmp = it.vs_initial_fmp` (fn initial =>
           POP_ASSUM_LIST (K all_tac) >>
           simp[ptrDisciplineTheory.allocas_below_fmp_def, allocas, fmp, initial] >>
           metis_tac[])))) >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    array_bounds_check_read_only_joint_ok_frame) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gb`, `tnb`, `ib`] strip_assume_tac) >>
  `!q. p.ptr_operand = Var q ==> not_fresh_at st2 q` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!q. not_fresh_at st2 q ==> not_fresh_at cs'' q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[ci_mono_def, cs_extends_def] >>
     metis_tac[cs_extends_trans]) >>
  `!q. not_fresh_at st2 q ==>
    lookup_var q ib = lookup_var q it /\ FLOOKUP Gb q = FLOOKUP Gi q /\
    op_taint tnb (Var q) = op_taint tni (Var q)` by metis_tac[] >>
  `eval_operand p.ptr_operand ib = SOME w /\
   op_taint tnb p.ptr_operand = {} /\ op_prov Gb p.ptr_operand = NONE` by
    (Cases_on `p.ptr_operand` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `eval_operand iop ib = SOME iw /\ op_taint tnb iop = {} /\ op_prov Gb iop = NONE` by
    (Cases_on `iop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `fn_has_code cs'' sb func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
  simp[exprSimArrayIndexTheory.array_elem_ptr_def,
       comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `?data. data_ptr = Var data` by
    (qpat_x_assum `emit_op ADD [p.ptr_operand; _] _ = _` mp_tac >>
     pure_rewrite_tac[loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >> gvs[] >>
  `?off. offset = Var off` by
    (qpat_x_assum `emit_op MUL _ _ = _` mp_tac >>
     pure_rewrite_tac[loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >> gvs[] >>
  `?out. dst = Var out` by
    (qpat_x_assum `emit_op ADD [Var _; _] _ = _` mp_tac >>
     pure_rewrite_tac[loweringShapeRulesTheory.emit_op_eq, pairTheory.PAIR_EQ] >>
     strip_tac >> gvs[]) >> gvs[] >>
  fs[compileEnvTheory.word_scale_def] >>
  `!q. iop = Var q ==> not_fresh_at cs'' q` by metis_tac[] >>
  `eval_operand iop ib = SOME (n2w (w2n iw))` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ib` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp it` mp_tac >>
     qpat_assum `ib.vs_allocas = it.vs_allocas` (fn allocas =>
       qpat_assum `ib.vs_fmp = it.vs_fmp` (fn fmp =>
         qpat_assum `ib.vs_initial_fmp = it.vs_initial_fmp` (fn initial =>
           POP_ASSUM_LIST (K all_tac) >>
           simp[ptrDisciplineTheory.allocas_below_fmp_def, allocas, fmp, initial] >>
           metis_tac[])))) >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullSubscriptArrayCodeOpsTheory.code_dynamic_address_joint_frame_observed) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`]
    (CONJUNCTS_THEN2 (mk_asm "address_run") strip_assume_tac)) >>
  `!q. not_fresh_at st2 q ==>
    lookup_var q sf = lookup_var q it /\ FLOOKUP Gf q = FLOOKUP Gi q /\
    op_taint tnf (Var q) = op_taint tni (Var q)` by metis_tac[] >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx fin Gf tnf sf` by
    (rpt strip_tac >>
     irule (cj 1 code_array_ghost_readonly_tail) >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule (cj 2 code_array_ghost_readonly_tail) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`DF (storage_trace_horizon fin.storage_trace)`, `cx`, `d`, `fin`] >>
     simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand p.ptr_operand sf = eval_operand p.ptr_operand it` by
    (irule code_array_operand_readonly_tail >> simp[] >> qexists_tac `st2` >> simp[]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin il` by
    (rpt strip_tac >> first_assum irule >> simp[] >> metis_tac[expr_post_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin ib` by
    (rpt strip_tac >> first_assum irule >> simp[] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `st2` >>
     fs[ci_mono_def, cs_extends_def]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin sf` by
    (rpt strip_tac >> first_assum irule >> simp[] >>
     irule local_ptrs_reserved_next_var >> qexists_tac `st2` >>
     fs[ci_mono_def, cs_extends_def] >> metis_tac[cs_extends_trans]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 fin child
      (LocatedValue ann (mk_ptr (Var out) p.ptr_location)) sf` by
    (rpt strip_tac >>
     `p.ptr_location = LocCode` by simp[] >>
     asm_rewrite_tac[] >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any mp_tac code_array_selected_post_tail) >>
     disch_then (drule_at (Pat `eval_result_typed _ _ _`)) >>
     disch_then (drule_at (Pat `select_result _ _ _ _ _ = _`)) >>
     disch_then irule >>
     simp[] >>
     rpt (goal_assum (drule_at Any) >> simp[]) >>
     simp[venomStateTheory.eval_operand_def, elem_size_in_location_def,
          is_slot_addressed_def, venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def,
          AC arithmeticTheory.MULT_ASSOC arithmeticTheory.MULT_COMM] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  pop_assum (mk_asm "child_post") >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (it,Gi,tni) [] (OK sf,Gf,tnf)` by
    (rpt strip_tac >>
     `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
     `allocas_from lo il` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
     `allocas_from lo ib` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (il,Gl,tnl) [] (OK ib,Gb,tnb)` by metis_tac[] >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (ib,Gb,tnb) [] (OK sf,Gf,tnf)` by metis_tac[] >>
     `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (il,Gl,tnl) [] (OK sf,Gf,tnf)` by
       (qpat_assum `gas_origin_ptr_path _ (il,Gl,tnl) [] (OK ib,Gb,tnb)`
          (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
        simp[] >> disch_then irule >> simp[]) >>
     qpat_assum `!D lo explicit. allocas_from lo it ==> _`
       (qspecl_then [`DF H`, `lo`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     drule fragGasOriginPtrTheory.gas_origin_ptr_path_append >>
     simp[] >> disch_then irule >> simp[]) >>
  `alloca_inv it` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_tac o CONJUNCT1) >>
     simp[NoAsms, expr_post_def] >> metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `alloca_history func sf` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     drule_all body_full_path_alloca_history >> simp[]) >>
  irule code_array_selected_outcome_tail >> simp[] >>
  qexistsl_tac [`Gf`, `sf`, `tnf`] >>
  simp[] >> rpt strip_tac >>
  asm "child_post" (qspec_then `H` mp_tac) >> simp[]
QED

Resume subscript_array_framed_code_full[rejected_selection]:
  `select_result cx (ArrayT ann bd) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw))) fin =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
    (irule framed_array_select_error >> simp[] >> conj_tac
     >- fs[vyperArrayTheory.valid_index_def] >>
     qexistsl_tac [`cenv`, `env`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `e1`, `mid`] >> simp[]) >>
  `!tail. select_result cx (ArrayT ann bd) tv
      (ValueSubscript (IntV (if is_signed_type (expr_type e2) then w2i iw else &w2n iw)))
      (fin with gas_obs := tail) =
      (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin with gas_obs := tail)` by
    simp[select_result_nonstorage_gas_obs] >>
  Cases_on `bd`
  >- suspend "fixed_rejection" >>
  suspend "dynamic_rejection"
QED

Resume subscript_array_framed_code_full[fixed_rejection]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[oneTheory.one] >>
  `ci_mono st2 cs'` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_bounds_check_def,
          exprSimArrayIndexTheory.array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return, IF_CASES_TAC])) >>
  `ci_mono cs' sb` by
    (qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op, irule ci_mono_comp_return])) >>
  `fn_has_code st2 cs' func` by metis_tac[fn_has_code_split, ci_mono_def] >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `~idx_in_range (is_signed_type (expr_type e2)) iw (n2w n)` by fs[] >>
  `eval_operand (Lit (n2w n)) it = SOME (n2w n) /\
   op_taint tni (Lit (n2w n)) = {} /\ op_prov Gi (Lit (n2w n)) = NONE /\
   (!q. iop = Var q \/ Lit (n2w n) = Var q ==> not_fresh_at st2 q) /\
   (!l. iop <> Label l /\ Lit (n2w n) <> Label l)` by
    simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
         ptrDisciplineTheory.op_prov_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``] array_bounds_check_joint_oob_frame) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_exit >> simp[] >>
  qexistsl_tac [`Gf`, `fin`, `Abort Revert_abort sf`,
     `INR (Error (RuntimeError "evaluate_subscripts array_index"))`, `tnf`] >>
  simp[fragExecTheory.exit_result_def, Abbr `baseR`, exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def] >>
  rpt strip_tac >>
  `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
  simp[]
QED

Resume subscript_array_framed_code_full[dynamic_rejection]:
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[oneTheory.one] >>
  `ci_mono st2 cs'` by
    (qpat_x_assum `compile_ptr_load _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[contextTheory.compile_ptr_load_def, contextTheory.compile_imm_load_word_runtime,
          ci_mono_emit_op]) >>
  `ci_mono cs' cs''` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_bounds_check_def,
          exprSimArrayIndexTheory.array_bounds_valid_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_emit_void, irule ci_mono_comp_return, IF_CASES_TAC])) >>
  `ci_mono cs'' sb` by
    (qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     simp[exprSimArrayIndexTheory.array_elem_ptr_def] >>
     rpt (FIRST [irule ci_mono_bind >> conj_tac,
                 gen_tac >> BETA_TAC, irule ci_mono_emit_op,
                 irule ci_mono_comp_return])) >>
  `cs_extends st2 cs' /\ cs_extends cs' cs'' /\ cs_extends cs'' sb` by fs[ci_mono_def] >>
  `fn_has_code st2 cs' func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `compile_imm_load_word F cenv.ce_imm_alloca p.ptr_operand st2 = (len_op,cs')` by
    fs[contextTheory.compile_ptr_load_def] >>
  `op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = NONE` by
    fs[ptr_vv_ok_def] >>
  `stmt_state_rel (storage_trace_horizon fin.storage_trace) ctx func cenv cx fin it` by
    metis_tac[expr_post_def] >>
  `immutable_holds cenv cx (ArrayT ann (Dynamic n)) tv w fin it` by
    (fs[vv_holds_def] >> gvs[]) >>
  `w2n w <= LENGTH it.vs_data_section` by
    (drule_all exprSimBopRestWordLoadSafetyTheory.rest_word_immutable_region_bound >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp it` by simp[] >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``]
    bodyFullSubscriptArrayCodeOpsTheory.compile_imm_load_word_runtime_joint_run) >>
  disch_then (qspecl_then [`PG`, `Gi`] mp_tac) >>
  disch_then (qx_choosel_then [`lenvar`, `Gl`, `tnl`, `il`]
      (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac
          (CONJUNCTS_THEN2 (mk_asm "length_run") strip_assume_tac)))) >>
  `word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n w) it.vs_data_section ++ REPLICATE 32 0w)) =
      n2w (array_length (ArrayTV etv (Dynamic n)) av)` by
    (drule_all exprSimSubscriptArraySuffixTheory.framed_array_code_length_view >> simp[]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by fs[ptr_val_ok_def] >>
  `eval_operand iop il = SOME iw /\ op_taint tnl iop = {} /\ op_prov Gl iop = NONE` by
    (Cases_on `iop` >>
     gvs[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_prov_def,
         ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!q. not_fresh_at st2 q ==> not_fresh_at cs' q` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st2` >> fs[ci_mono_def, cs_extends_def]) >>
  `!q. len_op = Var q ==> not_fresh_at cs' q` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_imm_load_word_runtime,
          loweringShapeRulesTheory.emit_op_eq] >> strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `eval_operand len_op il = SOME (n2w (array_length (ArrayTV etv (Dynamic n)) av)) /\
    (!l. len_op <> Label l)` by simp[venomStateTheory.eval_operand_def] >>
  `(!q. iop = Var q \/ len_op = Var q ==> not_fresh_at cs' q) /\
   (!l. iop <> Label l /\ len_op <> Label l)` by metis_tac[] >>
  `fn_has_code cs' cs'' func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp il` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp it` mp_tac >>
     qpat_assum `il.vs_allocas = it.vs_allocas` (fn allocas =>
       qpat_assum `il.vs_fmp = it.vs_fmp` (fn fmp =>
         qpat_assum `il.vs_initial_fmp = it.vs_initial_fmp` (fn initial =>
           POP_ASSUM_LIST (K all_tac) >>
           simp[ptrDisciplineTheory.allocas_below_fmp_def, allocas, fmp, initial] >>
           metis_tac[])))) >>
  drule_all (INST_TYPE [``:'a`` |-> ``:256``] array_bounds_check_joint_oob_frame) >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gf`,`tnf`,`sf`] (map_every assume_tac o CONJUNCTS)) >>
  irule gas_outcome_full_exit >> simp[] >>
  qexistsl_tac [`Gf`, `fin`, `Abort Revert_abort sf`,
     `INR (Error (RuntimeError "evaluate_subscripts array_index"))`, `tnf`] >>
  simp[fragExecTheory.exit_result_def, Abbr `baseR`, exprSimDefsTheory.expr_exit_def,
       exprSimDefsTheory.halt_exit_def] >>
  rpt strip_tac >>
  `allocas_from lo it` by metis_tac[ghost_inv_at_def] >>
  `allocas_from lo il` by metis_tac[ptrDisciplineTheory.allocas_from_def] >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (il,Gl,tnl) [] (Abort Revert_abort sf,Gf,tnf)` by metis_tac[] >>
  qpat_assum `!D lo explicit. allocas_from lo it ==> _`
    (qspecl_then [`DF H`, `lo`, `gas_explicit_sites ctx shadow_ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qpat_assum `gas_origin_ptr_path _ (it,Gi,tni) [] (OK il,Gl,tnl)`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule >> simp[]
QED

Finalise subscript_array_framed_code_full
