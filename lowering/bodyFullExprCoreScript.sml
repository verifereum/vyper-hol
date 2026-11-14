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
  bodyFullBopBytestringCuts bodyFullBopBytestringChild bodyFullBopBytestringPost
  bodyFullBopBytestringIntervals bodyFullBopBytestringFinalPost
  bodyFullBopBytestringHash bodyFullBopBytestringDigest bodyFullBopBytestringFinish
  exprBopDigestProps exprBopSimProps bytestringHashProps fragExec
  gasOutcomeFullCompose vyperStorageTrace vyperFiniteStoragePreservation
  gasExemptCert exprSimProps exprSimSource exprLoweringProps
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_binop ann bop (expr_type e1) (expr_type e2)` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def]) >>
  `ann = BaseT BoolT /\ expr_type e2 = expr_type e1` by
    metis_tac[well_typed_binop_def] >>
  simp[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all bop_bytestring_selected_compile_cuts >> strip_tac >>
  drule_all bop_bytestring_selected_code_intervals >> strip_tac >>
  `(!m cb. bytestring_literal_hash (gas_shadow_expr e1) = NONE /\
      lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa = (m,cb) ==>
      fn_has_code shadow_sa cb shadow_func) /\
   (!m cb. bytestring_literal_hash (gas_shadow_expr e2) = NONE /\
      lower_value compile_expr cenv (expr_type e2) (gas_shadow_expr e2) shadow_sh1 = (m,cb) ==>
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
  irule gas_outcome_full_bind_all >>
  irule_at (Pos last)
    (gasOutcomeFullTheory.gas_outcome_full_post_mono |> Q.INST [`Q'` |-> `Q`] |> SIMP_RULE std_ss []) >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_selected_child_full >>
  simp[] >>
  qexistsl_tac [`tops`, `sh1`, `shadow_func`, `shadow_ctx`, `sa`, `h1`, `env`, `d`, `cenv`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!m cb. bytestring_literal_hash e1 = NONE /\ _ ==> ?shadow_cb. _` drule_all >>
      strip_tac >> qexistsl_tac [`shadow_sa`, `shadow_cb`] >> simp[] >>
      irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  conj_tac >- (Cases >> simp[]) >>
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
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `v1` (qx_choose_then `contents1`
    (map_every assume_tac o CONJUNCTS))) >>
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
     fs[expr_body_pre_def, expr_sim_inv_def, vyperStorageFootprintTheory.valid_horizon_def]) >>
  irule gas_outcome_full_bind_all >>
  irule_at (Pos last)
    (gasOutcomeFullTheory.gas_outcome_full_post_mono |> Q.INST [`Q'` |-> `Q`] |> SIMP_RULE std_ss []) >>
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_selected_child_full >>
  simp[] >>
  qexistsl_tac [`tops`, `sh2`, `shadow_func`, `shadow_ctx`, `sh1`, `h2`, `env`, `d`, `cenv`] >>
  simp[] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- metis_tac[]) >>
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
  conj_tac >- (Cases >> simp[]) >>
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
  irule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`) bop_bytestring_digest_suffix_full >>
  qexistsl_tac [`word_of_bytes_be (Keccak_256_w64 contents2)`,
    `word_of_bytes_be (Keccak_256_w64 contents1)`, `tv`] >>
  qpat_x_assum `?raw t Gf tnf. _` strip_assume_tac >>
  qexistsl_tac [`tnf`, `t''`, `sb`, `sh2`, `raw`, `op`] >>
  `?cap. expr_type e1 = BaseT (BytesT (Dynamic cap)) \/
         expr_type e1 = BaseT (StringT cap)` by
    metis_tac[bodyMemBopHeldFactsTheory.held_bytestring_eqne_types] >>
  qexistsl_tac [`cap`, `Gf`] >> simp[] >>
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
        NONE => (\(m,cb). compile_bytestring_hash m cb)
          (lower_value compile_expr cenv (expr_type e1) e1 sa)
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
     fs[expr_body_pre_def, expr_sim_inv_def, vyperStorageFootprintTheory.valid_horizon_def]) >>
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
  conj_tac >-
    (qpat_x_assum `(if bop = Eq then emit_op EQ _ _ else _) = (op,sb)` mp_tac >>
     simp[NoAsms, LET_THM]) >>
  simp[exprSimWordArgsTheory.wb_frame_gas_obs] >>
  qpat_assum `ghost_inv_at (DF H) lo d cenv cx mid' G1' tn1' t'` mp_tac >>
  simp[NoAsms, ghost_inv_at_def] >> strip_tac >> simp[])
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
  cheat
QED
