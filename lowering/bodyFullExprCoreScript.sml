(*
 * The expression core of the full body induction, as direct joint proofs
 * over bodySimFull's finite-horizon judgments: the leaf expressions (names,
 * top-level names, flag members, literals) and the binary operators, by
 * the operand families exprSimOperators' compile_bop_case splits on.
 *
 * TOP-LEVEL:
 *   name_expr_full_ok, toplevel_name_expr_full_ok, flag_member_expr_full_ok,
 *   literal_expr_full_ok -- the leaves bodyFullCases' body_expr_full_ok_leaf
 *     joins
 *   bop_word_sim_full, bop_bytes_eq_sim_full, bop_bytestring_eqne_sim_full,
 *   bop_rest_word_sim_full, bop_in_literal_word_sim_full -- the operator
 *     families bodyFullCases' bop_expr_full_ok and bop_in_expr_full_ok join
 *)
Theory bodyFullExprCore
Ancestors
  bodyFullShadowBodyInv bodyFullIntCallReturnHalt bodyFullHashKeccakFixed
  bodyFullToplevelValue bodyFullToplevelVV bodyFullIfExpReach[qualified,ignore_grammar]
  bodyFullLiteralWord bodyFullLiteralBuffer bodyFullLiteralNonword
  bodyFullEmptyLeafData exprSimFullBundleProps
  bodyFullNameVV bodyFullNameNonword bodyFullNameWord exprSimOperators
  bodyFullBopInLiteralOperands bodyFullBopInLiteralTail exprSimBopInLiteralWord
  bodyFullBopBytesEqLayout bodyFullBopBytesEqSuffix exprBopSimProps
  exprSimWordArgs freshWrites exprSimHyps gasShadowCompileStmtHelpers
  exprSimUnopProps fragExec gasExemptCert vyperStorageTrace gasOutcomeFull
  vyperStorageFootprint exprSimDefs contextRawReachable unitMemInv
  exprSimExtract32Post bodyFullGhostFrame stmtSimDefs bodyPtrHashBuiltinsGhostCompose
  bodyFullBopWordLayout bodyFullBopWordOperands bodyFullBopWordSuffix bodyFullBopWordExtract
  bodyFullBopRestWordCompose exprSimBopRestWordFacts
  gasOutcomeFullCompose exprSimProps exprSimSource exprLoweringProps
  bodyFullBopBytestringCuts bodyFullBopBytestringChild bodyFullBopBytestringPost
  bodyFullBopBytestringIntervals bodyFullBopBytestringFinalPost
  bodyFullBopBytestringHash bodyFullBopBytestringDigest bodyFullBopBytestringFinish
  exprBopDigestProps bytestringHashProps vyperFiniteStoragePreservation
  exprLowering vyperTyping vyperTypeSystem loweringPosts valueEncoding vyperValueOperation
  exprSimMemDefs bodyPtrDefs gasShadow fragGasOriginPtr ptrDiscipline loweringSlice
  bodyFullSimProjection bodyFullPreds bodySimFull bodySim exprSimHypsDefs compileEnv
  vyperContext vyperAST vyperInterpreter vyperState vyperValue venomState list

val _ = Parse.hide "body";

(* Lift endpoint posts from the supplier's execution. *)
fun expr_core_outcome_room_tac rewrites outcome =
  irule gas_outcome_full_post_mono >>
  irule_at Any (MATCH_MP gas_outcome_full_halt_room (BETA_RULE outcome)) >>
  BETA_TAC >> simp rewrites >>
  rpt gen_tac >> disch_then (qx_choose_then `v` strip_assume_tac) >>
  qexists_tac `v` >> simp[] >>
  first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o
               CONJUNCT1 o REWRITE_RULE [expr_post_def]);

fun operand_path_no_wrap horizon path =
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
           (CONJ inv member))))) >>
  qpat_assum path (qspec_then horizon mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (fn reached =>
    qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
    qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn nowrap =>
      ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom
        (LIST_CONJ [reached,phi,nowrap])))));

(* ===== Leaves ===== *)

Theorem name_expr_full_ok:
  !cx ann id. body_expr_full_ok cx (Name ann id)
Proof
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac >- (Cases_on `is_word_type ann` >>
    metis_tac[name_word_full, name_nonword_full]) >>
  irule name_vv_full >> metis_tac[]
QED

Theorem toplevel_name_expr_full_ok:
  !cx ann nsid. body_expr_full_ok cx (TopLevelName ann nsid)
Proof
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- (irule toplevel_name_value_full >> metis_tac[]) >>
  irule toplevel_name_vv_full >> metis_tac[]
QED

(* A flag member compiles to StackValue (Lit _) and emits no instruction
   (compile_expr_def), in runtime and constructor frames alike; the source
   side is exprSimProps' eval_expr_flag_member_gas. *)
Theorem flag_member_value_nil:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
  sb = sa /\ ?v.
    (!tail. bind (eval_expr cx (FlagMember ann nsid mid)) (read_result cx)
              (es with gas_obs := tail) = (INL v,es with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (FlagMember ann nsid mid)
           (es,sa,sb,s0,op,G0,tn0) H (INL v : value + exception)
           (es with gas_obs := []) G0 tn0 s0)
Proof
  simp[expr_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  strip_tac >> PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0,nsid1)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[gas_shadow_expr_def] >>
  qpat_x_assum `lower_value _ _ _ _ sa = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       unwrap_value_def] >> strip_tac >> gvs[] >>
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, expr_store_bound_def,
       expr_type_def, is_word_type_def, ptr_val_ok_def, op_taint_def,
       ghost_inv_at_def, ghost_kept_at_def] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, expr_type_def,
       is_word_type_def, typed_val_to_w256_word_value, word_value_def,
       val_to_w256_def, eval_operand_def, locals_kept_def] >>
  gvs[ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def]
  >- (rpt gen_tac >>
      qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
      Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def])
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  gvs[expr_type_def, is_word_type_def]
QED

Theorem flag_member_vv_nil:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es /\
  expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  sb = sa /\ ?res.
    (!tail. eval_expr cx (FlagMember ann nsid mid) (es with gas_obs := tail) =
            (res,es with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (FlagMember ann nsid mid)
           (es,sa,sb,s0,vv,G0,tn0) H res (es with gas_obs := []) G0 tn0 s0)
Proof
  simp[expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  strip_tac >> PairCases_on `nsid` >>
  `gas_admissible (bind (eval_expr cx (FlagMember ann (nsid0,nsid1) mid))
     (read_result cx)) expr_res_ok es` by
    (irule exprSimStackTheory.eval_expr_force_admissible >> simp[] >>
     rpt gen_tac >> simp[Once evaluate_def, lookup_flag_mem_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> simp[raise_def, return_def]) >> rw[]) >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0,nsid1)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[gas_shadow_expr_def] >>
  qpat_x_assum `compile_expr _ _ _ sa = _` mp_tac >>
  simp[compile_expr_def, comp_return_def] >> strip_tac >> gvs[] >>
  qexists_tac `INL (Value (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid)))` >>
  conj_tac >- simp[Once evaluate_def, lookup_flag_mem_def, return_def] >>
  simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[gas_origin_ptr_path_rules, vv_store_bound_def, contextTheory.vv_location_def,
       expr_type_def, is_word_type_def, ptr_vv_ok_def, ptr_val_ok_def,
       read_result_def, return_def, op_taint_def,
       ghost_inv_at_def, ghost_kept_at_def] >>
  `stmt_state_rel H ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[NoAsms]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, vv_storage_live_def,
       read_result_def, return_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, is_word_type_def, typed_val_to_w256_word_value,
       word_value_def, val_to_w256_def, eval_operand_def, locals_kept_def] >>
  gvs[ghost_inv_at_def, vyperStorageFootprintTheory.storage_well_formed_on_def]
  >- (rpt gen_tac >>
      qpat_x_assum `!b slot tv. _` (qspec_then `b` mp_tac) >>
      Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def])
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  gvs[expr_type_def, is_word_type_def] >>
  gvs[contextTheory.vv_location_def]
QED

Theorem flag_member_value_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_sim_full_via_bundle] >>
  drule_all flag_member_value_nil >> strip_tac >>
  irule gas_outcome_full_unchanged >>
  gvs[expr_sim_full_hypotheses_def] >> first_assum ACCEPT_TAC
QED

Theorem flag_member_vv_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_vv_sim_full_via_bundle] >>
  drule_all flag_member_vv_nil >> strip_tac >>
  irule gas_outcome_full_unchanged >>
  gvs[expr_vv_sim_full_hypotheses_def] >> first_assum ACCEPT_TAC
QED

Theorem flag_member_expr_full_ok:
  !cx ann nsid mid. body_expr_full_ok cx (FlagMember ann nsid mid)
Proof
  simp[body_expr_full_ok_def] >> rpt strip_tac >>
  metis_tac[flag_member_value_full, flag_member_vv_full]
QED

Theorem literal_expr_full_ok:
  !cx ann l. body_expr_full_ok cx (Literal ann l)
Proof
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type ann`
  >- metis_tac[literal_word_value_full, literal_word_vv_full] >>
  metis_tac[literal_nonword_value_full, literal_nonword_vv_full]
QED

(* ===== Binary operators =====
   Each family is a binary operator lowered to a StackValue
   (exprSimOperators' compile_bop_stack), so only the value judgment is
   stated; the vv judgment follows from it. *)

(* in and not in on an array literal of words, which the lowering unrolls
   to a comparison with each element, so it takes the elements'
   judgments where e1 evaluates and is read. *)
Theorem bop_in_literal_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 a t n elems es.
    (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
    body_expr_full_ok cx e1 /\
    ((?s0 tv s1 s2 v s3. eval_expr cx e1 s0 = (INL tv, s1) /\
                         read_result cx tv s2 = (INL v, s3)) ==>
     builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
     body_exprs_full_ok cx elems) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env
      (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems])
      es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_typing >> strip_tac >>
  drule_all literal_body_evaluate_types >> strip_tac >>
  `body_exprs_full_ok cx (e1::elems)` by
    (simp[Once body_exprs_full_ok_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[builtin_args_length_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[] >>
  `is_ArrayT a` by gvs[vyperASTTheory.is_ArrayT_def] >>
  drule_all literal_lower_value >> strip_tac >>
  `wb_args_shape cenv expr_type (e1::elems)` by
    (irule literal_args_shape >> metis_tac[]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by
    (Cases_on `bop = In` >> gvs[] >>
     metis_tac[literal_membership_straight, exprSimUnopPropsTheory.straight_fresh_cs_extends]) >>
  `fn_has_code sa sm func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `!shadow_xs shadow_sm.
    lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr (e1::elems)) shadow_sa =
      (shadow_xs,shadow_sm) ==> fn_has_code shadow_sa shadow_sm shadow_func` by
    (rpt strip_tac >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[NoAsms, gas_shadow_expr_def, gas_shadow_builtin_def] >>
     disch_then (mp_then Any strip_assume_tac literal_lower_value) >>
     qpat_x_assum `(bop = In \/ bop = NotIn) /\ is_ArrayT a ==> _` mp_tac >>
     simp[] >> strip_tac >>
     `shadow_sm = sm'` by gvs[] >>
     `cs_extends sm' shadow_sb` by
       (Cases_on `bop = In` >> gvs[] >>
        metis_tac[literal_membership_straight, straight_fresh_cs_extends]) >>
     irule fn_has_code_mid >>
     reverse conj_tac
     >- (qexistsl_tac [`shadow_sb`, `shadow_sa`] >>
         simp[compileEnvTheory.cs_extends_refl]) >>
     `!args ss oo ff.
        lower_word_args (gas_shadow_env T cenv) expr_type args ss = (oo,ff) ==> cs_extends ss ff` by
       (Induct >> simp[lower_word_args_nil, compileEnvTheory.cs_extends_refl] >>
        rpt gen_tac >> simp[lower_word_args_cons] >> rpt strip_tac >>
        metis_tac[cj 2 compile_expr_grows, compileEnvTheory.cs_extends_trans]) >>
     metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
  drule_all (Q.SPEC `e1::elems` bop_in_literal_operands_clean_full_halt) >>
  disch_then (qspec_then `PG` (assume_tac o MATCH_MP gas_outcome_full_halt_room)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ PrefixPost _` >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  qpat_x_assum `a = _` SUBST_ALL_TAC >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  irule gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >- simp[storage_trace_frame_return] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> metis_tac[]) >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G tn u. PrefixPost H res ee G tn u /\
    ~u.vs_halted /\ ee.gas_obs = []` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      BETA_TAC >> conj_tac >- simp[] >>
      rpt gen_tac >> disch_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type,
          halt_exit_def] >>
      rpt strip_tac >> gvs[expr_exit_def]) >>
  map_every qx_gen_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`s1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  qunabbrev_tac `PrefixPost` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `(?vs. _)` strip_assume_tac >>
  Cases_on `vs` >- gvs[] >>
  rename1 `LIST_REL _ (needle::xs) (v::vs)` >>
  disj1_tac >> qexists_tac `v::vs` >> simp[] >>
  `fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `EVERY (\x. !p. x = Var p ==> not_fresh_at sm p) (needle::xs)` by
    (qpat_assum `EVERY (\x. _ /\ (!l. x <> Label l)) _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  simp[expr_type_def, post_value_type_def, is_word_type_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx mid s1`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  irule (SRULE [is_word_type_def] bop_in_literal_continuation_full_exit) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (`(mid with gas_obs := []) = mid` by
        simp[evaluation_state_component_equality] >>
      simp[] >> rpt gen_tac >> disch_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` drule >>
      simp[] >> strip_tac >>
      simp[EXISTS_MEM, EVERY_MEM])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qexistsl_tac [`expr_type e1`,`needle`,`sm`,`tv`,`xs`] >>
      simp[NoAsms] >>
      gvs[is_word_type_def]) >>
  first_assum ACCEPT_TAC
QED

(* == and != on bytestrings: keccak256 of each operand's bytes. *)
Theorem bop_bytestring_eqne_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    metis_tac[well_typed_binop_def] >>
  simp[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  simp[] >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`, `\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[Abbr `R`] >>
  irule (BETA_RULE (Q.SPEC
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
    (Q.GEN `R` gas_outcome_full_halt_room))) >>
  qunabbrev_tac `Q` >>
  drule_all bop_bytestring_selected_compile_cuts >> strip_tac >>
  drule_all bop_bytestring_selected_code_intervals >> strip_tac >>
  `(!m cb. bytestring_literal_hash (gas_shadow_expr e1) = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa = (m,cb) ==>
      fn_has_code shadow_sa cb shadow_func) /\
   (!m cb. bytestring_literal_hash (gas_shadow_expr e2) = NONE /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2) shadow_sh1 = (m,cb) ==>
      fn_has_code shadow_sh1 cb shadow_func)` by
    (qpat_x_assum `lower_value _ _ _ (Builtin _ _ [e1;e2]) _ = _` kall_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _`
       (assume_tac o SIMP_RULE (srw_ss()) [gas_shadow_expr_def, gas_shadow_builtin_def, MAP]) >>
     `is_bytestring_type (expr_type (gas_shadow_expr e1)) /\
      expr_type (gas_shadow_expr e2) = expr_type (gas_shadow_expr e1)` by simp[] >>
     drule_all bop_bytestring_selected_code_intervals >>
     simp[] >> strip_tac >> simp[]) >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     (conj_tac >- gvs[expr_body_pre_def]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_full_ok _ _`
       (strip_assume_tac o REWRITE_RULE [body_exprs_full_ok_def]) >>
     qpat_x_assum `body_expr_full_ok cx e1` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule gas_outcome_full_bind_all_path >>
  irule_at (Pos last)
    (gasOutcomeFullTheory.gas_outcome_full_post_mono |> Q.INST [`Q'` |-> `Q`] |> SIMP_RULE std_ss []) >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_selected_child_full_halt >>
  simp[] >>
  qexistsl_tac [`tops`, `sh1`, `shadow_func`, `shadow_ctx`, `sa`, `h1`, `env`, `d`, `cenv`] >>
  simp[] >> conj_tac
  >- (disch_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!m cb. bytestring_literal_hash e1 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
      strip_tac >> qexistsl_tac [`shadow_sa`, `shadow_cb`] >> simp[] >>
      irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >>
    rename1 `expr_exit result stop /\ _ ==> _` >>
    Cases_on `result` >> simp[expr_exit_def]) >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    operand_path_no_wrap `storage_trace_horizon mid.storage_trace`
      `!H. valid_horizon _ _ H mid.storage_trace ==>
         gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> ?v contents. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v1` (qx_choose_then `contents1`
    (map_every assume_tac o CONJUNCTS))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx mid t`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  disj1_tac >> qexists_tac `v1` >> simp[] >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)`
       (mp_then Any mp_tac (cj 1 exprSimSourceTheory.expr_body_pre_eval)) >>
     simp[SF ETA_ss] >>
     qpat_x_assum `bind _ _ _ = _` (assume_tac o REWRITE_RULE [APPEND_NIL]) >>
     disch_then drule >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by
       qpat_assum `expr_body_pre cenv cx env e1 es`
         (ACCEPT_TAC o cj 2 o REWRITE_RULE [exprSimHypsDefsTheory.expr_body_pre_def]) >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     qexistsl_tac [`ann`, `[e1; e2]`, `Bop bop`, `es`] >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (qpat_assum `body_exprs_full_ok _ _`
       (strip_assume_tac o REWRITE_RULE [body_exprs_full_ok_def]) >>
     `body_expr_full_ok cx e2` by
       (first_x_assum irule >>
        qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
        simp[NoAsms, vyperStateTheory.bind_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[] >> metis_tac[]) >>
     qpat_x_assum `body_expr_full_ok cx e2` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sh1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     `storage_well_formed_on cx mid (FST H)` suffices_by metis_tac[] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `res = INL v1` (fn th =>
       simp[NoAsms, th, vyperStateTheory.bind_def, AllCaseEqs()]) >>
     strip_tac >> drule vyperStateTheory.read_result_state >>
     disch_then (SUBST_ALL_TAC o SYM) >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `eval_expr _ _ _ = _`
          (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
        simp[evaluate_storage_trace_frame]) >>
     `storage_well_formed_on cx (mid with gas_obs := []) (FST H)` suffices_by
       (simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
        strip_tac >> rpt gen_tac >>
        qpat_x_assum `!b slot tv. _`
          (qspecl_then [`b`, `slot`, `tv`] mp_tac) >>
        Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     irule (cj 1 (cj 5 vyperFiniteStoragePreservationTheory.eval_storage_well_formed_on_mutual)) >>
     simp[] >>
     reverse conj_tac >-
       (qpat_assum `valid_horizon cx st0 H mid.storage_trace`
          (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
        strip_tac >>
        qpat_assum `expr_body_pre cenv cx env e1 es`
          (strip_assume_tac o REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
        simp[] >>
        qexistsl_tac [`e1`, `env`, `v`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >>
        simp[] >>
        `storage_well_formed_on cx es (FST H)` by metis_tac[] >>
        reverse conj_tac >-
          (qpat_x_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
           simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def] >>
           strip_tac >> rpt gen_tac >>
           qpat_x_assum `!b slot tv. _` (qspecl_then [`b`, `slot`, `tv`] mp_tac) >>
           Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
        qpat_assum `expr_body_pre cenv cx env e1 es` mp_tac >>
        simp[expr_body_pre_def, expr_sim_inv_def,
             vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
     qpat_assum `expr_sim_inv cenv cx env mid`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     simp[]) >>
  irule gas_outcome_full_bind_all >>
  irule_at (Pos last)
    (gasOutcomeFullTheory.gas_outcome_full_post_mono |> Q.INST [`Q'` |-> `Q`] |> SIMP_RULE std_ss []) >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_selected_child_full_halt >>
  simp[] >>
  qexistsl_tac [`tops`, `sh2`, `shadow_func`, `shadow_ctx`, `sh1`, `h2`, `env`, `d`, `cenv`] >>
  simp[] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >-
    qpat_assum `expr_type e2 = expr_type e1` (fn ty_eq =>
      qpat_assum `expr_sim_full _ cenv cx (expr_type e2) e2 mid`
        (ACCEPT_TAC o REWRITE_RULE [ty_eq]))) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `lower_value compile_expr cenv (expr_type e2) e2 sh1 = (m,cb)` by metis_tac[] >>
     qpat_assum `!m cb. bytestring_literal_hash e2 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
     strip_tac >> qexistsl_tac [`shadow_sh1`, `shadow_cb`] >> simp[] >>
     `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
       (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
     simp[] >> conj_tac >- metis_tac[] >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[] >>
     fs[wb_frame_def]) >>
  conj_tac >- (rpt gen_tac >>
    rename1 `expr_exit result stop /\ _ ==> _` >>
    Cases_on `result` >> simp[expr_exit_def]) >>
  conj_tac >- simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >-
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v2` (qx_choose_then `contents2`
    (map_every assume_tac o CONJUNCTS))) >>
  disj1_tac >> qexists_tac `v2` >> simp[] >>
  `eval_operand h1 t' = SOME (word_of_bytes_be (Keccak_256_w64 contents1)) /\
   op_prov G1' h1 = NONE /\ op_taint tn1' h1 = {}` by
    (qpat_assum `wb_frame cenv mid mid' sh1 t t'`
       (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
     qpat_assum `ghost_kept_at lo cenv mid sh1 G1 tn1 t G1' tn1'`
       (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
     qpat_x_assum `eval_operand h1 t = _` mp_tac >>
     qpat_x_assum `op_prov G1 h1 = NONE` mp_tac >>
     qpat_x_assum `op_taint tn1 h1 = {}` mp_tac >>
     qpat_x_assum `!z. h1 = Var z ==> _` mp_tac >>
     qpat_x_assum `!l. h1 <> Label l` mp_tac >>
     Cases_on `h1` >> simp[eval_operand_def, op_prov_def, op_taint_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `!z. h1 = Var z ==> not_fresh_at sh2 z` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `allocas_from lo t'` by fs[ghost_inv_at_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (qpat_assum `stmt_state_rel _ ctx func cenv cx mid' t'`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp)) >>
  drule_all bop_bytestring_digest_operational >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] assume_tac) >>
  `(?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
             (INL v1,mid with gas_obs := [])) /\
      (?gs. bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs) =
             (INL v2,mid' with gas_obs := []))` by
       (conj_tac >- (qexists_tac `gas_explicit marks s0.vs_gas_readings ++ []` >> metis_tac[]) >>
        qexists_tac `gas_explicit marks' t.vs_gas_readings ++ []` >> metis_tac[]) >>
     qpat_assum `expr_body_pre cenv cx env e1 es`
       (mp_then Any mp_tac bodyPtrBopTypedSourceTheory.bop_typed_source_witness) >>
     disch_then (qspecl_then [`v1`, `mid with gas_obs := []`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >>
     qpat_assum `expr_body_pre cenv cx env e2 mid`
       (mp_then Any mp_tac bodyPtrBopTypedSourceTheory.bop_typed_source_witness) >>
     disch_then (qspecl_then [`v2`, `mid' with gas_obs := []`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac >>
  `tv' = tv` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv' = tv` SUBST_ALL_TAC >>
  irule gas_outcome_full_post_source >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_digest_suffix_full_exit >>
  qexistsl_tac [`word_of_bytes_be (Keccak_256_w64 contents2)`,
    `word_of_bytes_be (Keccak_256_w64 contents1)`, `tv`] >>
  qpat_x_assum `?raw t Gf tnf. _` strip_assume_tac >>
  qexistsl_tac [`tnf`, `t''`, `sb`, `sh2`, `raw`, `op`] >>
  `?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
         expr_type e1 = BaseT (StringT cap)` by
    metis_tac[bodyMemBopHeldFactsTheory.held_bytestring_eqne_types] >>
  qexistsl_tac [`cap`,
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`, `Gf`] >> simp[] >>
  (conj_tac >- metis_tac[byteTheory.word_of_bytes_be_def]) >>
  (conj_tac >- metis_tac[byteTheory.word_of_bytes_be_def]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = _`
       (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  qpat_assum `!H. valid_horizon cx st0 H mid'.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `local_ptrs_reserved cenv sh2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh2 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh2 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `sa.cs_next_id <= sh1.cs_next_id` by
    (Q.UNDISCH_TAC `(case bytestring_literal_hash e1 of
        NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e1) e1 sa))
       (SND (lower_value compile_expr cenv (expr_type e1) e1 sa))
      | SOME digest => (Lit digest,sa)) = (h1,sh1)` >>
     Cases_on `bytestring_literal_hash e1`
     >- (Cases_on `lower_value compile_expr cenv (expr_type e1) e1 sa` >>
         simp[NoAsms] >> disch_tac >> drule (cj 2 compile_expr_grows) >>
         drule compile_bytestring_hash_shape >>
         simp[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     simp[NoAsms] >> strip_tac >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `MAP FDOM es.scopes = _` mp_tac >> simp[NoAsms]) >>
  `storage_well_formed_on cx mid' (FST H)` by
    (Q.UNDISCH_THEN `!tail. bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit marks' t.vs_gas_readings ++ tail) =
      (res',mid' with gas_obs := tail)` (qspec_then `[]` mp_tac) >>
     Q.PAT_ASSUM `res' = INL v2` (fn th =>
       simp[NoAsms, th, vyperStateTheory.bind_def, AllCaseEqs()]) >>
     strip_tac >> drule vyperStateTheory.read_result_state >>
     disch_then (SUBST_ALL_TAC o SYM) >>
     `!b. get_storage cx (mid' with gas_obs := []) b = get_storage cx mid' b` by
       (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     `storage_well_formed_on cx (mid' with gas_obs := []) (FST H)` suffices_by
       (simp[vyperStorageFootprintTheory.storage_well_formed_on_def]) >>
     irule (cj 1 (cj 5 vyperFiniteStoragePreservationTheory.eval_storage_well_formed_on_mutual)) >>
     simp[] >>
     reverse conj_tac >-
       (qpat_assum `valid_horizon cx st0 H mid'.storage_trace`
          (mp_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
        strip_tac >>
        qpat_assum `expr_body_pre cenv cx env e2 mid`
          (strip_assume_tac o REWRITE_RULE [expr_body_pre_def, expr_sim_inv_def]) >>
        simp[] >>
        qexistsl_tac [`e2`, `env`, `v'`,
          `mid with gas_obs := gas_explicit marks' t.vs_gas_readings`] >>
        simp[] >>
        `storage_well_formed_on cx mid (FST H)` by metis_tac[] >>
        reverse conj_tac >-
          (`!b. get_storage cx (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) b =
                 get_storage cx mid b` by
             (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
           Q.UNDISCH_TAC `storage_well_formed_on cx mid (FST H)` >>
           qpat_x_assum `!b. get_storage cx (mid with gas_obs := _) b = _`
             (fn th => simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def, th])) >>
        qpat_assum `expr_body_pre cenv cx env e2 mid` mp_tac >>
        simp[expr_body_pre_def, expr_sim_inv_def,
             vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
     qpat_assum `expr_sim_inv cenv cx env mid`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
     simp[]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (qmatch_goalsub_rename_tac `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ final` >>
  qmatch_abbrev_tac `postA /\ postB /\ postTail` >>
  qsuff_tac `postA /\ postB /\ final.vs_current_bb = sb.cs_current_bb /\
    final.vs_inst_idx = LENGTH sb.cs_current_insts /\ postTail`
  >- simp[] >>
  map_every qunabbrev_tac [`postA`, `postB`, `postTail`] >>
  pure_rewrite_tac[post_value_type_def] >>
  irule (PURE_REWRITE_RULE [post_value_type_def] bop_bytestring_final_post) >>
  simp[] >>
  conj_tac >-
    (`!b. get_storage cx (mid' with gas_obs := []) b = get_storage cx mid' b` by
       (Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     qpat_assum `storage_well_formed_on cx mid' (FST H)` mp_tac >>
     qpat_x_assum `!b. get_storage cx (mid' with gas_obs := []) b = _`
       (fn th => simp[NoAsms, vyperStorageFootprintTheory.storage_well_formed_on_def, th])) >>
  qexistsl_tac [`G1`, `G1'`, `mid`, `h1`, `h2`, `raw'`, `raw`,
    `sh1`, `sh2`, `t`, `tn1`, `tn1'`, `t'`] >>
  simp[] >>
  conj_tac >-
    (qpat_x_assum `final = _` SUBST_ALL_TAC >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sh2 x ==> lookup_var x _ = _ /\ _`
       (qspec_then `z` mp_tac) >> simp[]) >>
  simp[exprSimWordArgsTheory.wb_frame_gas_obs] >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid' G1' tn1' t'` mp_tac >>
  simp[NoAsms, ghost_inv_at_def] >> strip_tac >> simp[])
QED

(* ===== Binary operators =====
   Each family is a binary operator lowered to a StackValue
   (exprSimOperators' compile_bop_stack), so only the value judgment is
   stated; the vv judgment follows from it. *)

(* Both operands of word_value_type. *)
Theorem bop_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `is_word_type ann` by metis_tac[well_typed_binop_word_result] >>
  `post_value_type cenv (Builtin ann (Bop bop) [e1;e2]) = ann` by
    simp[post_value_type_word, expr_type_def] >>
  simp[] >>
  drule_all bop_word_full_layout >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`, `\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[Abbr `R`] >>
  irule (BETA_RULE (Q.SPEC
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
    (Q.GEN `R` gas_outcome_full_halt_room))) >>
  irule (SRULE [LET_THM] bop_word_operands_full_cps_exit) >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`cenv`, `d`, `env`, `s1`, `s2`, `sa`, `shadow_func`,
    `shadow_s1`, `shadow_s2`, `shadow_sa`, `tops`, `x`, `y`] >>
  simp[] >>
  rpt gen_tac >> strip_tac >> simp[] >>
  mp_tac (SRULE [LET_THM] bop_word_suffix_full_halt) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (expr_core_outcome_room_tac [Abbr `Q`, expr_type_def])
QED

(* == and != on address and bytesN. *)
Theorem bop_bytes_eq_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\
    (expr_type e1 = BaseT AddressT \/
     ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_type e2 = expr_type e1 /\ ann = BaseT BoolT` by
    (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
     gvs[well_typed_binop_def]) >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all bop_bytes_eq_layout >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\
   ci_mono shadow_sa sh1 /\ ci_mono sh1 sh2` by
    (rpt conj_tac >>
     metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND]) >>
  `cs_extends s2 sb /\ cs_extends sh2 shadow_sb` by
    metis_tac[compile_binop_shape] >>
  `fn_has_code sa s1 func /\ fn_has_code shadow_sa sh1 shadow_func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (fs[body_exprs_full_ok_def] >>
     metis_tac[body_expr_full_ok_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `sh1`, `x`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[bop_first_admissible])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ firstQ firstR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`, `\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[Abbr `R`, Abbr `firstR`] >>
  irule (BETA_RULE (Q.SPEC
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
    (Q.GEN `R` gas_outcome_full_halt_room))) >>
  qunabbrev_tac `Q` >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- (irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
      simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def]) >>
  qexists_tac `\H res ee G tn t. firstQ H res ee G tn t /\
     ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "second" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  metis_tac[]
QED

Resume bop_bytes_eq_sim_full[second]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `firstQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    operand_path_no_wrap `storage_trace_horizon mid.storage_trace`
      `!H. valid_horizon _ _ H mid.storage_trace ==>
         gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o
                 CONJUNCT1 o REWRITE_RULE [expr_post_def]) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >> BETA_TAC >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid)` by
    (`mid with gas_obs := [] = mid` by
       fs[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pop_assum (fn th => rewrite_tac[th, APPEND_NIL])) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by metis_tac[] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by
       qpat_assum `expr_body_pre cenv cx env e1 es`
         (ACCEPT_TAC o cj 2 o REWRITE_RULE [expr_body_pre_def]) >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) (read_result cx) _ = (INL v,mid)`
       (irule_at Any) >> simp[]) >>
  `body_expr_full_ok cx e2` by
    (gnvs[body_exprs_full_ok_def] >>
     metis_tac[eval_expr_read_INL]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e2 mid` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `sh1`, `sh2`, `y`,
    `t`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt conj_tac
     >- (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans])
     >- (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans])
     >- metis_tac[local_ptrs_reserved_next_var, ci_mono_def]
     >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def]
     >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def]
     >- (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qexistsl_tac [`cenv`, `s0`, `sa`] >>
         fs[ci_mono_def, expr_post_def])
     >- metis_tac[] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >> fs[expr_post_def])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ secondQ secondR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t'`, `v'`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def]) >>
  qexists_tac `\H res ee G tn u. secondQ H res ee G tn u /\
     ~u.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "suffix" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ secondQ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `secondR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >> metis_tac[]
QED

Resume bop_bytes_eq_sim_full[suffix]:
  qx_genl_tac [`marks2`, `res2`, `mid2`, `G2`, `tn2`, `u`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `secondQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res2 = INL _` SUBST_ALL_TAC >>
  qexists_tac `v'` >> simp[] >> BETA_TAC >>
  `bind (eval_expr cx e2) (read_result cx)
     (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings) =
     (INL v', mid2)` by
    (`mid2 with gas_obs := [] = mid2` by
       fs[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ (mid with gas_obs := _) = _`
       (qspec_then `[]` mp_tac) >>
     pop_assum (fn th => rewrite_tac[th, APPEND_NIL])) >>
  `?ot. evaluate_type (get_tenv cx) (expr_type e1) = SOME ot` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION,
         is_word_type_def]) >>
  `?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
      value_has_type tv1 v` by
    (`expr_body_pre cenv cx env e1
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >> simp[]) >>
  `?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
      value_has_type tv2 v'` by
    (`expr_body_pre cenv cx env e2
       (mid with gas_obs := gas_explicit marks2 t.vs_gas_readings)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >> simp[]) >>
  `(!z. x = Var z ==> not_fresh_at s1 z) /\
   (!z. y = Var z ==> not_fresh_at s2 z)` by
    (conj_tac
     >- (qpat_assum `lower_value _ _ _ e1 sa = _`
           (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
         metis_tac[]) >>
     qpat_assum `lower_value _ _ _ e2 s1 = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     metis_tac[]) >>
  `(!z. x = Var z ==> not_fresh_at s2 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv1 v) /\
   eval_operand y u = SOME (typed_val_to_w256 tv2 v')` by
    (conj_tac >> fs[expr_post_def, expr_val_rel_def]) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv1 v)` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     strip_tac >>
     qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
     strip_tac >> Cases_on `x`
     >- (qpat_x_assum `eval_operand _ t = _` mp_tac >> simp[eval_operand_def])
     >- (rename1 `Var z` >>
         qpat_x_assum `!x w. not_fresh_at s1 x /\ _ ==> _`
           (qspecl_then [`z`, `typed_val_to_w256 tv1 v`] mp_tac) >>
         simp[] >>
         qpat_x_assum `eval_operand _ t = _` mp_tac >> simp[eval_operand_def]) >>
     metis_tac[]) >>
  `fn_has_code s2 sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  drule_all bop_bytes_eq_suffix_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `allocas_from lo u` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid2 _ _ u`
       (mp_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >> simp[]) >>
  `op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    (qpat_assum `ptr_val_ok _ _ _ y G2 tn2 u`
       (mp_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def]) >> simp[]) >>
  `op_prov G2 x = NONE /\ op_taint tn2 x = {}` by
    (qpat_assum `ptr_val_ok _ _ _ x G1 tn1 t`
       (mp_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def]) >>
     simp[] >> strip_tac >>
     qpat_assum `ghost_kept_at lo _ _ s1 G1 tn1 t G2 tn2`
       (mp_tac o SIMP_RULE (srw_ss()) [ghost_kept_at_def]) >>
     strip_tac >> Cases_on `x` >> simp[op_prov_def, op_taint_def] >>
     rename1 `Var z` >>
     qpat_x_assum `!x. not_fresh_at s1 x ==> _`
       (qspec_then `z` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `op_prov G1 (Var z) = NONE` mp_tac >>
     qpat_x_assum `op_taint tn1 (Var z) = {}` mp_tac >>
     simp[op_prov_def, op_taint_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `expr_post _ ctx func cenv cx e2 _ _ _ _ _ _ _ u`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o
        CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
  drule_all bop_bytes_eq_suffix_ptr >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  `tv2 = tv1` by metis_tac[optionTheory.SOME_11] >>
  `?b1 b2. v = BytesV b1 /\ v' = BytesV b2 /\
    (tv1 = BaseTV AddressT \/
     ?m. tv1 = BaseTV (BytesT (Fixed m)) /\ m <= 32)` by
    (qpat_assum `value_has_type tv1 v` mp_tac >>
     qpat_assum `value_has_type tv2 v'` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME tv1` mp_tac >>
     qpat_assum `expr_type e1 = _ \/ _` mp_tac >>
     qpat_assum `tv2 = tv1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `v` >> fs[value_has_type_def] >>
     Cases_on `v'` >> fs[value_has_type_def]) >>
  `typed_val_to_w256 tv1 v = typed_val_to_w256 tv2 v' <=> v = v'` by
    (gvs[] >> irule exprSimCompareTheory.typed_val_to_w256_bytes_11 >> simp[]) >>
  `bop_result cx ann bop [expr_type e1; expr_type e2] v v' mid2 =
     INL (BoolV (eval_compare bop (expr_type e1)
       (typed_val_to_w256 tv1 v) (typed_val_to_w256 tv2 v')))` by
    (qpat_assum `typed_val_to_w256 tv1 v = _ <=> _` mp_tac >>
     qpat_assum `v = BytesV b1` mp_tac >>
     qpat_assum `v' = BytesV b2` mp_tac >>
     qpat_assum `bop = Eq \/ bop = NotEq` mp_tac >>
     qpat_assum `expr_type e1 = _ \/ _` mp_tac >>
     qpat_assum `expr_type e2 = expr_type e1` mp_tac >>
     qpat_assum `ann = BaseT BoolT` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[exprBopSimDefsTheory.bop_result_def, evaluate_builtin_def,
         evaluate_binop_def, binop_negate_def, arithmeticPropsTheory.eval_compare_def, oEL_def,
         vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
     IF_CASES_TAC >> simp[]) >>
  suspend "post"
QED

Resume bop_bytes_eq_sim_full[post]:
  markerLib.RESUME_TAC >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G'`, `mid2`, `INL (BoolV (eval_compare bop (expr_type e1)
    (typed_val_to_w256 tv1 v) (typed_val_to_w256 tv2 v')))`,
    `u' with vs_inst_idx := LENGTH sb.cs_current_insts`, `tn'`] >>
  simp[] >>
  (conj_tac
   >- (qpat_x_assum `bop_result _ _ _ _ _ _ _ = _` mp_tac >>
       simp[exprBopSimDefsTheory.bop_result_def])) >>
  suspend "endpoint"
QED

Resume bop_bytes_eq_sim_full[endpoint]:
  markerLib.RESUME_TAC >> gen_tac >> disch_tac >>
  `straight_fresh (compile_binop bop x y (expr_type e1) NONE NONE)` by
    (irule exprSimCompareTheory.straight_fresh_compare >> simp[] >> metis_tac[]) >>
  `writes_fresh s2 (emitted_insts s2 sb) /\
   sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb` by
    metis_tac[freshWritesTheory.straight_fresh_def] >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (conj_tac
   >- (drule_all fragGasFreshTheory.straight_fresh_code_prefix >> strip_tac >>
      drule fragGasFreshTheory.writes_fresh_path_opcodes >> strip_tac >>
      drule fragGasFreshTheory.writes_fresh_gas_count >> strip_tac >>
      `run_inst_seq_mem_ok (emitted_insts s2 sb) u` by
        metis_tac[bodyUnopFragMemoryTheory.writes_fresh_mem_ok] >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts s2 sb)` by fs[EVERY_MEM] >>
      (* The whitelist of fresh writes excludes DALLOCA at any suffix step. *)
      `(ctx_has_dalloca ctx ==> !pre i post v.
        emitted_insts s2 sb = pre ++ i::post /\
        run_inst_seq pre u = OK v ==> dalloca_no_wrap i v)` by
        (rpt strip_tac >>
         irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         `MEM i (emitted_insts s2 sb)` by simp[] >>
         qpat_assum `writes_fresh _ _`
           (qspec_then `i` mp_tac o REWRITE_RULE[writes_fresh_def, EVERY_MEM]) >>
         Cases_on `i.inst_opcode = DALLOCA` >> simp[fresh_write_op_def]) >>
      qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `DF H` assume_tac) >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      fs[LENGTH_NIL] >> simp[])) >>
  suspend "joint"
QED

Resume bop_bytes_eq_sim_full[joint]:
  markerLib.RESUME_TAC >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx mid2 u` by
    metis_tac[expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx mid2
     (u' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule bodyPtrSignedConvertSourceFrameTheory.stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`u`, `s2`] >> simp[] >>
     qpat_assum `u' = u with vs_vars := _` mp_tac >>
     qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[lookup_var_def, venom_state_component_equality]) >>
  `storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!tail. bind _ _ (es with gas_obs := _) = _`
       (qspec_then `[]` assume_tac) >>
     drule_all valid_horizon_frame >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `!tail. bind _ _ (es with gas_obs := _) = _`
       (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >> simp[]) >>
  (conj_tac
   >- (simp[exprSimExtract32PostTheory.extract32_expr_post_end_gas_obs] >>
       irule exprBopSimPropsTheory.expr_post_bop >>
       simp[is_word_type_def, word_value_def, val_to_w256_def] >>
       (conj_tac >- (qmatch_goalsub_abbrev_tac `bool_to_word b` >>
                     Cases_on `b` >> simp[])) >>
       (conj_tac >- (qpat_assum `stmt_state_rel H ctx func cenv cx mid2
          (u' with vs_inst_idx := _)` mp_tac >>
          qpat_assum `sb.cs_current_insts = _ ++ _` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx])) >>
       qexistsl_tac [`mid`, `s1`, `s2`, `t`, `u`, `v`, `v'`, `x`, `y`] >>
       simp[] >>
       (conj_tac >- (qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def])) >>
       (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality] >> metis_tac[])) >>
       (conj_tac >- fs[ci_mono_def]) >>
       (conj_tac >- fs[ci_mono_def]) >>
       (conj_tac >- fs[ci_mono_def]) >>
       (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality])) >>
       (conj_tac >- (
         qpat_assum `expr_post H _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
         qpat_assum `INL v = INL _` mp_tac >>
         qpat_assum `v = BytesV b1` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])) >>
       qpat_assum `expr_post H _ _ _ _ e2 _ _ _ _ _ _ _ _` mp_tac >>
       qpat_assum `INL v' = INL _` mp_tac >>
       qpat_assum `v' = BytesV b2` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[])) >>
  suspend "resources"
QED

Resume bop_bytes_eq_sim_full[resources]:
  markerLib.RESUME_TAC >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u'` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid2 (u' with vs_inst_idx := _)`
       (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
     POP_ASSUM_LIST (K all_tac) >> simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `sb.cs_current_bb = s2.cs_current_bb` by
    metis_tac[freshWritesTheory.straight_fresh_def] >>
  simp[expr_type_def, is_word_type_def, exprSimMemDefsTheory.expr_store_bound_word] >>
  (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
    qpat_assum `u.vs_current_bb = _` mp_tac >>
    qpat_assum `cs_extends s2 sb` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality, cs_extends_def] >> metis_tac[])) >>
  (conj_tac >- (
    `alloca_inv u` by metis_tac[stmt_state_rel_def] >>
    `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 sb)` by
      (drule fragGasFreshTheory.writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
    `alloca_history func (u' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
      (irule entryDecoderHistoryFrameTheory.entry_straight_line_alloca_history >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       qexistsl_tac [`u`, `s2`] >> simp[] >>
       simp[rich_listTheory.IS_PREFIX_APPEND]) >>
    qpat_x_assum `alloca_history func (u' with vs_inst_idx := _)` mp_tac >>
    qpat_assum `sb.cs_current_insts = _ ++ _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[])) >>
  (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
    qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
    qpat_assum `t.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality] >> decide_tac)) >>
  (conj_tac >- (
    irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
    qexistsl_tac [`G2`, `mid2`, `u`, `s2`, `tn2`] >>
    simp[] >>
    (conj_tac >- (rpt strip_tac >>
      `sa.cs_next_var <= s2.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
      metis_tac[freshWritesTheory.not_fresh_at_mono])) >>
    (conj_tac >- (rpt strip_tac >>
      `sa.cs_next_var <= s2.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
      metis_tac[freshWritesTheory.not_fresh_at_mono])) >>
    (conj_tac >- (
      qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
      qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP G' z = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def, op_taint_def])) >>
    qpat_assum `u' = u with vs_vars := _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality])) >>
  (conj_tac >- (
    qpat_assum `op_prov G' op = NONE` mp_tac >>
    qpat_assum `op_taint tn' op = {}` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def, is_word_type_def])) >>
  suspend "kept"
QED

Resume bop_bytes_eq_sim_full[kept]:
  markerLib.RESUME_TAC >>
  `(!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
   (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
   sa.cs_next_id <= s1.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G1 tn1` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  `ghost_kept cenv mid s1 G1 tn1 t G2 tn2` by
    (qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `expr_post H _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `local_ptrs_rel func cenv es.scopes s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM mid.scopes` mp_tac >>
     qpat_assum `!z. not_fresh_at sa z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `sa.cs_next_id <= s1.cs_next_id` mp_tac >>
     qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
     qpat_assum `ghost_kept cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all hash_expr_post_ghost_kept_compose >> simp[]) >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
  qpat_assum `!z. not_fresh_at sa z ==> not_fresh_at s2 z` mp_tac >>
  qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP G' z = _ /\ _` mp_tac >>
  qpat_assum `tn'.t_mem = tn2.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[ghost_kept_at_def, ghost_kept_def, op_taint_def] >>
  rpt strip_tac >> metis_tac[]
QED

Finalise bop_bytes_eq_sim_full





(* The rest, as exprSimBopRestWord's compile_bop_rest_word_case leaves it:
   in and not in on an array of words that is not a literal. *)
Theorem bop_bytes_sim_full[local]:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
    MEM bop [And;Or;XOr;ShL;ShR] /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv` by
    (qpat_assum `expr_body_pre _ _ _ e1 _`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type ann /\ is_word_type (expr_type e1) /\
   is_word_type (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = BaseT (BytesT (Fixed m))` SUBST_ALL_TAC >>
     gvs[well_typed_binop_def, is_int_type_def, is_word_type_def,
         vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `expr_type e2` >> gvs[is_int_type_def, is_word_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  `post_value_type cenv (Builtin ann (Bop bop) [e1;e2]) = ann` by
    simp[post_value_type_word, expr_type_def] >>
  simp[] >>
  drule_all bop_full_layout >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`, `\H res ee gt r.
    (expr_exit res r /\ halt_exit H cx ee res r) /\
    (ctx_has_dalloca ctx ==> !h. r = Halt h ==> allocas_below_fmp h)`] >>
  BETA_TAC >> simp[Abbr `R`] >>
  irule (BETA_RULE (Q.SPEC
    `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`
    (Q.GEN `R` gas_outcome_full_halt_room))) >>
  mp_tac (BETA_RULE (Q.INST
    [`R` |-> `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r`]
    (SRULE [LET_THM] bop_operands_full_cps_exit))) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- simp[NoAsms] >>
     rpt gen_tac >> strip_tac >>
  mp_tac (SRULE [LET_THM] bop_bytes_suffix_extract) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >~ [`?n. expr_type e1 = BaseT (BytesT (Fixed n))`]
     >- (qexists_tac `m` >> first_assum ACCEPT_TAC) >>
     fs[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SRULE [LET_THM] bop_suffix_full_halt) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (fn outcome =>
       irule gas_outcome_full_post_mono >>
       irule_at Any (BETA_RULE outcome) >> BETA_TAC >>
       simp[Abbr `Q`, expr_type_def] >>
       rpt gen_tac >> disch_then (qx_choose_then `v` strip_assume_tac) >>
       qexists_tac `v` >> simp[] >>
       first_assum (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o
                    CONJUNCT1 o REWRITE_RULE [expr_post_def]))) >>
  simp[]
QED

Theorem bop_rest_word_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
    ~((bop = In \/ bop = NotIn) /\ ~is_word_type (expr_type e1)) /\
    ~(word_value_type (expr_type e1) /\ word_value_type (expr_type e2)) /\
    ~((bop = Eq \/ bop = NotEq) /\
      (expr_type e1 = BaseT AddressT \/
       ?m. expr_type e1 = BaseT (BytesT (Fixed m)))) /\
    ((bop = In \/ bop = NotIn) ==>
     !a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    fs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  drule_all rest_word_typed_membership >> strip_tac
  >- (irule bop_bytes_sim_full >> metis_tac[]) >>
  irule compile_rest_word_membership_full >> metis_tac[]
QED
