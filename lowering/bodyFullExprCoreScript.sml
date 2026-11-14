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
  bodyFullNameVV bodyFullNameNonword bodyFullNameWord
  bodyFullBopInLiteralOperands bodyFullBopInLiteralTail exprSimBopInLiteralWord
  exprSimWordArgs freshWrites exprSimHyps gasShadowCompileStmtHelpers
  exprSimUnopProps fragExec gasExemptCert vyperStorageTrace gasOutcomeFull
  vyperStorageFootprint
  gasOutcomeFullCompose exprSimProps exprSimSource exprLoweringProps
  exprLowering vyperTyping vyperTypeSystem loweringPosts valueEncoding vyperValueOperation
  exprSimMemDefs bodyPtrDefs gasShadow fragGasOriginPtr ptrDiscipline loweringSlice
  bodyFullPreds bodySimFull bodySim exprSimHypsDefs compileEnv
  vyperContext vyperAST vyperInterpreter vyperState vyperValue venomState list

val _ = Parse.hide "body";

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
  cheat
QED

(* A flag member compiles to StackValue (Lit _) and emits no instruction
   (compile_expr_def), in runtime and constructor frames alike; the source
   side is exprSimFlagWord's. *)
Theorem flag_member_value_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_sim_full_def] >> PairCases_on `nsid` >>
  drule eval_expr_flag_member_gas >> strip_tac >>
  `cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid = i` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `ann = FlagT (nsid0,nsid1)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[gas_shadow_expr_def] >>
  qpat_x_assum `lower_value _ _ _ _ sa = _` mp_tac >>
  simp[lower_value_def, compile_expr_def, comp_bind_def, comp_return_def,
       unwrap_value_def] >> strip_tac >> gvs[] >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`,
    `INL (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid))`,
    `s0`, `tn0`] >>
  simp[] >> rpt strip_tac >>
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

Theorem flag_member_vv_full[local]:
  expr_body_pre cenv cx env (FlagMember ann nsid mid) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (FlagMember ann nsid mid) es
Proof
  rw[expr_vv_sim_full_def] >> PairCases_on `nsid` >>
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
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`,
    `INL (Value (FlagV (2 ** cenv.ce_flag_member_id (nsid_to_string (nsid0,nsid1)) mid)))`,
    `s0`, `tn0`] >>
  conj_tac >- simp[Once evaluate_def, lookup_flag_mem_def, return_def] >>
  simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
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

Theorem flag_member_expr_full_ok:
  !cx ann nsid mid. body_expr_full_ok cx (FlagMember ann nsid mid)
Proof
  simp[body_expr_full_ok_def] >> rpt strip_tac >>
  metis_tac[flag_member_value_full, flag_member_vv_full]
QED

Theorem literal_expr_full_ok:
  !cx ann l. body_expr_full_ok cx (Literal ann l)
Proof
  cheat
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
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
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
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* == and != on bytestrings: keccak256 of each operand's bytes. *)
Theorem bop_bytestring_eqne_sim_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop
   e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
    body_exprs_full_ok cx [e1; e2] /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

(* The rest, as exprSimBopRestWord's compile_bop_rest_word_case leaves it:
   in and not in on an array of words that is not a literal. *)
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
    expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED

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
    lower_word_args cenv expr_type (MAP gas_shadow_expr (e1::elems)) shadow_sa =
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
        lower_word_args cenv expr_type args ss = (oo,ff) ==> cs_extends ss ff` by
       (Induct >> simp[lower_word_args_nil, compileEnvTheory.cs_extends_refl] >>
        rpt gen_tac >> simp[lower_word_args_cons] >> rpt strip_tac >>
        metis_tac[cj 2 compile_expr_grows, compileEnvTheory.cs_extends_trans]) >>
     metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
  drule_all (Q.SPEC `e1::elems` bop_in_literal_operands_clean_full) >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ PrefixPost _` >>
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
      gvs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type]) >>
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
  irule (SRULE [is_word_type_def] bop_in_literal_continuation_full) >>
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
