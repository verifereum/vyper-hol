(*
 * Expression simulation: compile_subscript_array_case, a case of exprSimPlaces on its
 * own so it can be proved apart.
 *
 * TOP-LEVEL:
 *   compile_subscript_array_case — an element of a static or dynamic array,
 *     with the bounds-check abort, by two subcases:
 *     compile_subscript_array_framed_base_case for a base the index's frame
 *     keeps (a runtime immutable, or a static array of no dynamic array in
 *     memory), and compile_subscript_array_place_base_case, admitted, for
 *     the rest.
 *)

Theory exprSimSubscriptArray
Ancestors words[qualified,ignore_grammar]
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimSubscriptArrayFramed exprSimSubscriptArrayCompose
  abiEncodeArgsSim abiEncodeArgsCase exprSimAbiEncodeArgsMaterializePath targetSubscriptMemory
  exprSimSliceOrdinaryContinue
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* An element of an array whose index leaves the locals and the immutables
   as they were, and whose base the index's fragment keeps as it is: an
   immutable at runtime (LocCode outside the constructor), or a static array
   with no dynamic array inside it in memory (a local or a temporary).
   compile_subscript lowers the index after the
   base, and the base's value_vv must still hold its value when the index's
   fragment ends.  At runtime an immutable sits in the data section, which
   immutables_rel relates to the unchanged source immutables, and
   immutable_holds there pins the base's offset by sub_layout; the
   lowering reads a dynamic array's length with compile_ptr_load's
   compile_imm_load_word (DLOAD).  A memory base's bytes lie in one of the
   base's own allocations or in a live local's region (vv_at), and
   contain no length word, so the index's expr_post H keeps them (its
   allocation frame, locals_kept); a static array needs no length load.
   With the source locals unchanged, the base's place reads at the index's
   end what it read before.  The bounds check itself, a source RuntimeError
   for an index out of range against compile_array_subscript's ASSERT,
   which aborts, is in expr_exit's allowance (exprSimArrayIndex). *)
Theorem compile_subscript_array_framed_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    (!t r t'. eval_expr cx idx t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    ((~cenv.ce_is_ctor /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
     ((?n. bd = Fixed n) /\
      (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory)) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (Cases_on `nocalls` >> fs[] >>
     `int_calls_expr obj = []` by fs[int_calls_expr_def] >>
     drule post_value_type_no_calls >> simp[]) >>
  drule_all_then assume_tac
    exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ obj` mp_tac >>
     simp[expr_vv_case_def] >> disch_then irule >>
     conj_tac
     >- (strip_tac >> fs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  simp[exprSimDefsTheory.expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb` by
    (mp_tac exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     disch_then (qspecl_then
       [`vv_operand bvv`,`iop`,
        `case bd of Fixed _ => F | Dynamic _ => T`,
        `case bd of Fixed n => n | Dynamic _ => 0`,
        `word_scale loc`,`elem_size_in_location cenv loc et`,
        `is_signed_type (expr_type idx)`,
        `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc`,`st2`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load] >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends sm sb` by
    (irule compileEnvTheory.cs_extends_trans >> qexists_tac `st2` >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_vv_sim_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "base_bad"
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "base_normal"
      >> suspend "base_exit") >>
  suspend "base_exempt"
QED

Resume compile_subscript_array_framed_base_case[base_bad]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         vyperStorageTraceTheory.storage_trace_frame_select]
QED
Resume compile_subscript_array_framed_base_case[base_exit]:
  qexists_tac `marks` >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (disj1_tac >>
      qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         vyperStorageTraceTheory.storage_trace_frame_select] >>
      metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  disj2_tac >> disj1_tac >>
  Cases_on `res`
  >- (gvs[] >> metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  rename1 `INR exc` >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  fs[] >> disj2_tac >> first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_framed_base_case[base_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_framed_base_case[base_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o BETA_RULE) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
         vyperStorageTraceTheory.evaluate_storage_trace_frame,
         vyperStorageTraceTheory.storage_trace_frame_read_result,
         vyperStorageTraceTheory.storage_trace_frame_select] >>
      metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?tv. res = INL tv` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (qspec_then `H0` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `res = _` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    metis_tac[] >>
  gnvs[] >>
  qmatch_goalsub_abbrev_tac `mk_ptr dst loc` >>
  qpat_x_assum `expr_vv_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` kall_tac >>
  qpat_x_assum `expr_body_pre _ _ _ obj _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr cx obj) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_expr cx (Subscript _ _ _)) _ _` kall_tac >>
  qpat_x_assum `fn_has_code sa sm func` kall_tac >>
  qpat_x_assum `~s0.vs_halted` kall_tac >>
  qpat_x_assum `s0.vs_current_bb = _` kall_tac >>
  qpat_x_assum `s0.vs_inst_idx = _` kall_tac >>
  `gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_expr cx (Subscript ann obj idx)) (es,s0)
     (\H res ee t'. ?tv. res = INL tv /\
        vv_post H ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee tv
          (LocatedValue ann (mk_ptr dst loc)) t' /\
        t'.vs_current_bb = sb.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sb.cs_current_insts)
     (\H res ee out. expr_exit res out)` suffices_by
    simp[gasOutcomeTheory.gas_outcome_def] >>
  qpat_assum `~subscript_reads_base _ _ _`
    (irule o MATCH_MP framed_array_after_base) >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  conj_tac >- suspend "base_suffix" >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre cenv cx env idx (es_end with gas_obs := [])` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx idx` by metis_tac[] >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      simp[loweringPostsTheory.vv_post_def]) >>
  conj_tac
  >- metis_tac[gasSummaryTheory.gas_marked_exec_def,
               fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac
  >- (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
      `expr_body_pre cenv cx env idx (es_end with gas_obs := gs)` by fs[] >>
      drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]) >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ idx` mp_tac >>
  simp[expr_sim_case_def] >> disch_then irule >>
  conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
  qexists_tac `env` >> simp[]
QED
Resume compile_subscript_array_framed_base_case[base_suffix]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s tv t. eval_expr _ _ _ = _ ==> expr_sim_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `nocalls ==> _` kall_tac >>
  `vyperState$bind (eval_expr cx idx) (read_result cx)
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
     (INL v, raw with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `?ir. eval_expr cx idx
      (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
      read_result cx ir (raw with gas_obs := []) = (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >> metis_tac[]) >>
  reverse (Cases_on `storage_trace_domain cx st0 raw.storage_trace`)
  >- (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `?Hw. valid_horizon cx st0 Hw raw.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H raw.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `vyperState$bind _ _ _ = _`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
            vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result,
            vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                          gas_explicit imarks t.vs_gas_readings) =
      (INL tv,es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit imarks t.vs_gas_readings` mp_tac o CONJUNCT1) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `eval_expr cx obj _ = (INL tv, _)`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
            vyperStorageTraceTheory.evaluate_storage_trace_frame,
            vyperStorageTraceTheory.storage_trace_frame_read_result,
            vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `raw.scopes = es_end.scopes /\ raw.immutables = es_end.immutables` by
    (qpat_x_assum `!t r t'. eval_expr cx idx t = _ ==> _` drule >> simp[]) >>
  `~u.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
              fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` kall_tac >>
  qpat_x_assum `vyperState$bind _ _ _ = _` kall_tac >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ loc = p.ptr_location` by
    ( `vv_location bvv = SOME LocCode \/ vv_location bvv = SOME LocMemory` by
        metis_tac[pairTheory.FST] >>
      Cases_on `bvv` >>
      gvs[contextTheory.vv_location_def] >>
      qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==>
                      vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `Hw` mp_tac) >>
      (impl_tac >- metis_tac[]) >>
      disch_then (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
         REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
      simp[loweringPostsTheory.vv_holds_def, compileEnvTheory.is_bytestring_type_def] >> rpt strip_tac >>
      gvs[Abbr `loc`, contextTheory.vv_location_def]) >>
  qpat_x_assum `bvv = _` SUBST_ALL_TAC >>
  qpat_x_assum `loc = _` SUBST_ALL_TAC >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (CONJUNCT1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `expr_body_pre cenv cx env idx
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `expr_sim_inv cenv cx env
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `eval_expr cx obj _ = _`
      (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `p.ptr_location = LocCode \/ p.ptr_location = LocMemory` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `!ty st. vv_location _ = _`
       (qspecl_then [`ty`,`sa`] mp_tac) >>
     simp[contextTheory.vv_location_def]) >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base] >>
  `!l. p.ptr_operand <> Label l` by
    (drule exprSimSubscriptArrayOriginTheory.compile_array_pointer_not_label >>
     disch_then irule >> simp[] >>
     qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     strip_tac >> gvs[subscript_type_ok_def]
     >>~- ([`is_int_type (expr_type idx)`], Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
         rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[vyperTypeSystemTheory.is_int_type_def, compileEnvTheory.is_word_type_def]) >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >> simp[] >> strip_tac >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def] >>
     Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
         rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[vyperTypeSystemTheory.is_int_type_def, compileEnvTheory.is_word_type_def]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >>
     impl_tac
     >- (conj_tac >- fs[expr_body_pre_def] >>
         metis_tac[expr_body_pre_var_types_well_formed]) >>
     simp[]) >>
  `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` by metis_tac[] >>
  `((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
    ?n. bd = Fixed n) /\
   ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
    ((?n. bd = Fixed n) /\
     (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
     p.ptr_location = LocMemory))` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `!ty st. vv_location _ = _`
       (qspecl_then [`ty`,`sa`] assume_tac) >>
     gvs[contextTheory.vv_location_def] >>
     disj1_tac >> qexists_tac `ty` >>
     simp[contextTheory.vv_location_def]) >>
  `expr_sim_inv cenv cx env es_end` by fs[] >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac
      exprSimSubscriptArraySuffixTheory.framed_array_suffix_outcome) >>
  simp[NoAsms, exprSimPropsTheory.vv_post_initial_gas,
       vv_post_final_gas, expr_post_initial_gas,
       contextTheory.vv_operand_def] >>
  disch_then irule >>
  simp[SF SFY_ss, vv_post_final_gas, expr_post_initial_gas,
       contextTheory.vv_operand_def] >>
  qexistsl_tac [`iop`,`sm`,`st2`,`t`] >>
  fs[contextTheory.vv_operand_def, vv_post_final_gas,
     expr_post_initial_gas] >>
  qspecl_then [`sm`,`st2`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >>
  gvs[]
QED
Finalise compile_subscript_array_framed_base_case

(* Every other array subscript: a base in storage or transient storage, an
   immutable in the constructor, a dynamic array or one with a dynamic
   array inside it in memory, a base whose source result is a storage
   place, or an index that changes the locals or the immutables.  ADMITTED (cheat).  NOT DERIVABLE from these hypotheses,
   though no miscompile is known: vv_post H does not tie the base's pointer
   to its source place.  vv_at and local_val_at pick the local's path by
   its type alone, immutable_holds' constructor form takes any offset of
   the staged buffer that holds the value, and storage_holds pins the slot
   only by what it reads; so the base's pointer may lie in dead bytes that
   hold an equal value (past a dynamic array's length, in the staged
   buffer, in dead slots), which nothing keeps across the index's
   fragment: state_rel H and immutables_rel relate only the live parts,
   locals_kept exempts every dynamic array's length word, and expr_post H
   has no frame on Venom storage.  Witness: x : DynArray[DynArray[uint256,
   2], 2] holding [[5, 1]], with [5, 1] and its length word 2 left at
   x[1]'s bytes by an earlier pop; for x[0][i], with i a local, a pointer
   at x[1]'s offset satisfies every hypothesis on the base, i's fragment
   may rewrite that length word, and the bounds check then loads a word
   unrelated to x[0]'s length.  Further cases need more than that:
   - x[1][x.pop()[0]] pops x[1], and the base's place then reads the
     snapshot x's popped history keeps (read_memory_path), which no
     invariant relates to memory;
   - self.a[0][self.f()], with f popping self.a to empty, leaves a[0]'s
     slots dead, and storage_rel after the call relates nothing there;
   - in the constructor, with a : DynArray[DynArray[DynArray[uint256, 2],
     2], 2] holding [[[1, 2], [0, 5]]], a[0][1][a[0].pop()[0]] (the
     pinned Python compiler accepts a pop of an immutable's member in
     __init__) is false: the source's read of the base's place raises a
     RuntimeError, an immutable keeping no popped history, while the
     lowering ILOADs the stale length 2 and goes on, where expr_exit asks
     for an abort.
   A place-pointer clause in vv_post H replaces most of this lemma: a
   conjunct vv_place_ptr cenv cx es' s tv vv, as place_ptr_rel says for
   targets, with
     vv_place_ptr cenv cx es s (PlaceR (MemoryPlace id path))
                  (LocatedValue t p) <=>
       p.ptr_location = LocMemory /\
       ?q sz b t0 tv0 k tvk.
         FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz) /\
         lookup_var q s = SOME b /\ cenv.ce_var_type id = SOME t0 /\
         evaluate_type (get_tenv cx) t0 = SOME tv0 /\
         mem_path_offset tv0 path = SOME (k, tvk) /\
         eval_operand p.ptr_operand s = SOME (b + n2w k)
     vv_place_ptr cenv cx es s (PlaceR (StoragePlace tr slot tv))
                  (LocatedValue t p) <=>
       p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot
     (and the same for HashMapRef tr slot kt vt)
     vv_place_ptr cenv cx es s (PlaceR (ImmutablePlace src id path))
                  (LocatedValue t p) <=>
       p.ptr_location = LocCode /\ src = cenv.ce_module /\
       ?off itv iv k tvk.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module, id) =
           SOME (ImmutableLoc off) /\
         FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                    NONE => FEMPTY
                  | SOME imms => get_source_immutables cenv.ce_module imms)
                 id = SOME (itv, iv) /\
         mem_path_offset itv path = SOME (k, tvk) /\
         eval_operand p.ptr_operand s = SOME (n2w (off + k))
     vv_place_ptr cenv cx es s _ _ <=> T
   Its producers are the expressions whose source result can be a place:
   Name, TopLevelName, Subscript (array, tuple, mapping), Attribute, Pop,
   and IfExp (conditional_result keeps a memory aggregate's place, and the
   PHI carries the arm's pointer).  With it, and the base live at the
   index's end, the rest goes through but for popped snapshots, dead
   storage slots and the constructor immutable above. *)
Theorem compile_subscript_array_place_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t s' tv' t'. eval_expr cx obj s = (INL tv, t) /\
       (if subscript_reads_base cx obj idx
        then do v <- read_result cx tv; return (Value v) od
        else return tv) s' = (INL tv', t') ==>
       expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    ~(~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
      (!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

Theorem compile_builtin_body_stack_annotation[local]:
  compile_builtin_dispatch_body cfn ce ret_ty ty bi args sa =
    (StackValue vt op,sb) ==> vt = ret_ty
Proof
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, as_stack_val_def, as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  suspend "arm"
QED
Resume compile_builtin_body_stack_annotation[arm]:
  markerLib.RESUME_TAC >>
  gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[] >>
  gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  suspend "remaining"
QED
Resume compile_builtin_body_stack_annotation[remaining]:
  markerLib.RESUME_TAC
  >~ [`method_id_literal _ = SOME bs`] >-
    (Cases_on `ret_ty` >> gvs[compile_literal_vv_def, compileEnvTheory.comp_return_def] >>
     rpt (BasicProvers.FULL_CASE_TAC >> gvs[compileEnvTheory.comp_bind_def,
                             compileEnvTheory.comp_return_def]) >>
     rpt (pairarg_tac >> gvs[])) >>
  gvs[oneline as_stack_val_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED
Finalise compile_builtin_body_stack_annotation

Theorem compile_expr_body_builtin_regular[local]:
  bi <> AddMod /\ bi <> MulMod /\ bi <> PowMod256 ==>
  compile_expr_body cfn bfn tfn ce ty (Builtin ann bi args) sa =
    bfn ce ann ty bi args sa
Proof
  strip_tac >> Cases_on `args`
  >- simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  rename1 `h::rest` >> Cases_on `h`
  >~ [`Name at a :: rest`] >-
    (Cases_on `rest`
     >- simp[compile_expr_body_def, vyperASTTheory.expr_type_def] >>
     rename1 `Name at a :: h :: rest` >> Cases_on `h`
     >~ [`Name at a :: Name bt b :: rest`] >-
       (Cases_on `rest`
        >- (Cases_on `bi` >> gvs[compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
        rename1 `Name at a :: Name bt b :: h :: rest` >> Cases_on `h`
        >~ [`Name at a :: Name bt b :: Name mt m :: rest`] >-
          (Cases_on `rest` >> Cases_on `bi` >> gvs[compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
        simp[compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
     simp[compile_expr_body_def, vyperASTTheory.expr_type_def]) >>
  simp[compile_expr_body_def, vyperASTTheory.expr_type_def]
QED

Theorem compile_array_vv_type[local]:
  compile_expr ce ty e sa = (vv,sb) /\
  expr_type e = ArrayT et bd /\ post_value_type ce e = expr_type e /\
  vv_post H ctx func ce cx e es sa sb s0 es' tv vv s ==>
  vv_type vv = ArrayT et bd
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue vt op` >>
      Cases_on `e`
      >~ [`Builtin ann bi args`] >- suspend "builtin" >>
      gvs[vyperASTTheory.expr_type_def, Once (CONJUNCT1 compile_expr_raw_def),
          compile_expr_body_def, contextTheory.vv_type_def] >>
      suspend "stack") >>
  gvs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
      contextTheory.vv_type_def, compileEnvTheory.is_bytestring_type_def]
QED

Resume compile_array_vv_type[stack]:
  markerLib.RESUME_TAC >>
  rpt (pairarg_tac >> gvs[])
  >- (rename1 `compile_literal_vv _ lit _ = _` >> Cases_on `lit`
      >- (Cases_on `b` >> gvs[compile_literal_vv_def, compileEnvTheory.comp_return_def]) >>
      gvs[compile_literal_vv_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_return_def] >> rpt (pairarg_tac >> gvs[]))
  >- suspend "topname"
  >- suspend "name"
  >- suspend "typebuiltin"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "ifexp"
  >> suspend "call"
QED
Resume compile_array_vv_type[topname]:
  gvs[AllCaseEqs()]
QED
Resume compile_array_vv_type[name]:
  Cases_on `FLOOKUP ce.ce_vars s'`
  >- (gvs[compile_name_vv_def, compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
      rpt (pairarg_tac >> gvs[])) >>
  Cases_on `x` >>
  gvs[compile_name_vv_def, compileEnvTheory.comp_ignore_bind_def,
      compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED
Resume compile_array_vv_type[builtin]:
  gvs[vyperASTTheory.expr_type_def, contextTheory.vv_type_def] >>
  Cases_on `bi = AddMod \/ bi = MulMod \/ bi = PowMod256`
  >- suspend "optimized" >>
  gvs[] >> suspend "regular"
QED
Resume compile_array_vv_type[regular]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [CONV_RULE (DEPTH_CONV ETA_CONV)
    (CONJUNCT1 compile_expr_raw_def)] >>
  simp[compile_expr_body_builtin_regular, Excl "builtin_child_callback_def"] >>
  rewrite_tac [exprCallBoundsTheory.builtin_child_callback_def] >>
  simp[] >>
  pure_once_rewrite_tac [CONV_RULE (DEPTH_CONV ETA_CONV)
    (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def))] >>
  metis_tac[compile_builtin_body_stack_annotation]
QED
Resume compile_array_vv_type[optimized]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [CONV_RULE (DEPTH_CONV ETA_CONV)
    (CONJUNCT1 compile_expr_raw_def)] >>
  Cases_on `args`
  >- suspend "optimized_leaf" >>
  rename1 `h::rest` >> Cases_on `h`
  >~ [`Name at a :: rest`] >-
    (Cases_on `rest`
     >- suspend "optimized_leaf" >>
     rename1 `Name at a :: h :: rest` >> Cases_on `h`
     >~ [`Name at a :: Name bt b :: rest`] >-
       (Cases_on `rest`
        >- suspend "optimized_leaf" >>
        rename1 `Name at a :: Name bt b :: h :: rest` >> Cases_on `h`
        >~ [`Name at a :: Name bt b :: Name mt m :: rest`] >-
          (Cases_on `rest` >> suspend "optimized_leaf") >>
        suspend "optimized_leaf") >>
     suspend "optimized_leaf") >>
  suspend "optimized_leaf"
QED
Resume compile_array_vv_type[optimized_leaf]:
  markerLib.RESUME_TAC >>
  pure_rewrite_tac [compile_expr_body_def, vyperASTTheory.expr_type_def] >>
  simp[Excl "builtin_child_callback_def"] >>
  suspend "optimized_output"
QED
Resume compile_array_vv_type[optimized_output]:
  markerLib.RESUME_TAC >>
  simp[compile_addmod_names_def, compile_mulmod_names_def,
       compile_powmod256_names_def, oneline as_stack_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  suspend "optimized_last"
QED
Resume compile_array_vv_type[optimized_last]:
  markerLib.RESUME_TAC >>
  pure_once_rewrite_tac [CONV_RULE (DEPTH_CONV ETA_CONV)
    (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def))] >>
  strip_tac >>
  imp_res_tac compile_builtin_body_stack_annotation >>
  gvs[AllCaseEqs()]
QED
Resume compile_array_vv_type[typebuiltin]:
  gvs[compile_attribute_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED
Resume compile_array_vv_type[subscript]:
  gvs[compile_subscript_def, compileEnvTheory.comp_bind_def,
      compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `place_type ce e'` >>
  gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `t` >>
  gvs[compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED
Resume compile_array_vv_type[attribute]:
  gvs[compileEnvTheory.is_word_type_def]
QED
Resume compile_array_vv_type[ifexp]:
  qpat_x_assum `compile_type_builtin_dispatch _ _ _ _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac [CONV_RULE (DEPTH_CONV ETA_CONV)
    (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def))] >>
  Cases_on `t0` >>
  simp[compile_type_builtin_dispatch_body_def, oneline as_stack_val_def,
       oneline as_ptr_val_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  suspend "type_output"
QED
Resume compile_array_vv_type[type_output]:
  markerLib.RESUME_TAC >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[])
QED
Resume compile_array_vv_type[call]:
  Cases_on `c` >>
  gvs[compile_call_def, loweringPostsTheory.post_value_type_def,
      compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
      lowered_value_type_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  suspend "call_output"
QED
Resume compile_array_vv_type[call_output]:
  markerLib.RESUME_TAC >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[])
  >- (gvs[oneline as_stack_val_def, AllCaseEqs()]) >>
  PairCases_on `p` >>
  gvs[compile_call_def] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >> rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()]
QED
Finalise compile_array_vv_type

Theorem eval_expr_subscript_copied_bind[local]:
  subscript_reads_base cx obj idx ==>
  eval_expr cx (Subscript ann obj idx) =
  vyperState$bind (eval_expr cx obj) (\r.
    vyperState$bind (read_result cx r) (\base.
      vyperState$bind (vyperState$bind (eval_expr cx idx) (read_result cx)) (\v.
        select_result cx (expr_type obj) (Value base) (ValueSubscript v))))
Proof
  strip_tac >> simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def, vyperStateTheory.return_def]
QED

(* An overlapping index reads the captured value from a fresh memory copy.
   The copy is independent of the original place after the index runs. *)
Theorem copied_array_snapshot_after_index[local]:
  materialize_owned_post H ctx func ce cx obj es sa sm sc s0 es1 bv dst tv tc /\
  expr_post H ctx func ce cx idx es1 sc si tc ee iv iop u /\
  lowered_value_type ce obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv /\
  val_wf tv bv /\ local_ptrs_reserved ce sc /\
  (!x. dst = Var x ==> not_fresh_at sc x) /\ (!l. dst <> Label l) /\
  MAP FDOM ee.scopes = MAP FDOM es1.scopes ==>
  ?w. eval_operand dst u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
      val_in_memory tv bv (w2n w) u.vs_memory /\
      sm.cs_next_id < sc.cs_next_id /\
      (!n b len. local_region ce ee.scopes u n b len ==>
         w2n w + type_memory_size tv <= b \/ b + len <= w2n w)
Proof
  strip_tac >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
  `wb_frame ce es1 ee sc tc u` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `eval_operand dst u = SOME w` by
    (irule abi_args_operand_kept >> metis_tac[]) >>
  `mem_bytes_at (w2n w) (type_memory_size tv) u.vs_memory =
   mem_bytes_at (w2n w) (type_memory_size tv) tc.vs_memory` by
    (qpat_assum `wb_frame ce es1 ee sc tc u`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     first_x_assum irule >> conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
     qexists_tac `sm.cs_next_id` >> simp[]) >>
  qexists_tac `w` >> simp[] >> conj_tac
  >- metis_tac[loweringPostsTheory.wb_frame_def] >>
  conj_tac
  >- (irule exprSimPropsTheory.val_in_memory_footprint_agree >>
      conj_tac >- simp[] >> qexists_tac `tc.vs_memory` >> simp[] >>
      drule valueEncodingProofsTheory.mem_bytes_at_agree_window >>
      simp[exprSimPropsTheory.val_footprint_le]) >>
  rpt strip_tac >>
  `local_region ce es1.scopes tc n b len` by
    (irule exprSimPropsTheory.local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >>
         gvs[exprLoweringPropsTheory.stmt_state_rel_def,
             loweringStateRelDefsTheory.state_rel_def]) >>
     qexistsl_tac [`sc`, `ee.scopes`, `u`] >>
     gvs[loweringPostsTheory.wb_frame_def]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem copied_array_owned_child_endpoint[local]:
  materialize_owned_post H ctx func ce cx obj es sa sm sc s0 es1
    (ArrayV av) dst (ArrayTV etv bd) tc /\
  expr_post H ctx func ce cx idx es1 sc si tc ee iv iop u /\
  stmt_state_rel H ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sc.cs_next_id <= sf.cs_next_id /\
  (!x w. not_fresh_at sc x /\ lookup_var x u = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = u.vs_memory /\ stmt_state_rel H ctx func ce cx ee q /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n (w:bytes32),type_memory_size (ArrayTV etv bd)) /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) u.vs_memory /\
  sm.cs_next_id < sc.cs_next_id /\
  (!n b len. local_region ce ee.scopes q n b len ==>
    w2n w + type_memory_size (ArrayTV etv bd) <= b \/ b + len <= w2n w) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME child /\
  value_has_type etv child /\ val_wf etv child /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  j + val_footprint etv child <= type_memory_size (ArrayTV etv bd) /\
  eval_operand elem_ptr q = SOME dw /\ w2n dw = w2n w + j ==>
  vv_post H ctx func ce cx (Subscript et obj idx) es sa sf s0 ee (Value child)
    (LocatedValue et (mk_ptr elem_ptr LocMemory)) q
Proof
  strip_tac >>
  `wb_frame ce es es1 sa s0 tc` by
    gvs[materialize_owned_post_def] >>
  `wb_frame ce es1 ee sc tc u` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame ce es1 ee sc tc q` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `wb_frame ce es ee sa s0 q` by
    (`sa.cs_next_id <= sc.cs_next_id` by decide_tac >>
     drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[loweringPostsTheory.sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  `val_in_memory etv child (w2n dw) q.vs_memory` by
    gvs[loweringPostsTheory.sub_layout_def] >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame ce func es sa s0 q` by
    (strip_tac >>
     `pure_frame ce func es sa s0 tc` by gvs[materialize_owned_post_def] >>
     `pure_frame ce func es1 sc tc u` by
       (drule_all exprSimWordArgsTheory.expr_post_pure_frame >> simp[]) >>
     `pure_frame ce func es1 sc tc q` by
       (irule exprSimPropsTheory.pure_frame_mem_tail >> qexists_tac `u` >> simp[]) >>
     irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl_tac [`es1`,`sc`,`tc`] >> gvs[loweringPostsTheory.wb_frame_def] >> decide_tac) >>
  `storage_well_formed_on cx ee (FST H)` by gvs[loweringPostsTheory.expr_post_def] >>
  irule exprSimHashTheory.vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, loweringPostsTheory.expr_has_effect_thm,
       loweringPostsTheory.post_value_type_def, contextTheory.mk_ptr_def] >>
  conj_tac
  >- (gvs[loweringPostsTheory.vv_holds_def, contextTheory.mk_ptr_def,
           vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
      strip_tac >> irule exprSimPropsTheory.val_in_memory_word_type >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`et`,`get_tenv cx`] >> simp[]) >>
  simp[loweringPostsTheory.vv_at_def, contextTheory.mk_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  disj1_tac >> qexistsl_tac [`sm.cs_next_id`,`w2n w`,`type_memory_size (ArrayTV etv bd)`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!n b len. local_region _ _ _ _ _ _ ==> _` drule >> decide_tac
QED

Theorem copied_array_memory_suffix_family[local]:
  compile_array_subscript bop iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32 esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sf) /\
  fn_has_code si sf func /\ local_ptrs_reserved ce si /\
  (?H. P H) /\ (!H. P H ==> stmt_state_rel H ctx func ce cx ee u) /\
  ~u.vs_halted /\ u.vs_current_bb = si.cs_current_bb /\
  u.vs_inst_idx = LENGTH si.cs_current_insts /\ ee.gas_obs = [] /\
  (!x. bop = Var x ==> not_fresh_at si x) /\
  (!x. iop = Var x ==> not_fresh_at si x) /\
  (!l. bop <> Label l) /\ (!l. iop <> Label l) /\
  eval_operand bop u = SOME w /\ eval_operand iop u = SOME iw /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) u.vs_memory /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  (!child q. array_index (ArrayTV etv bd) av i = SOME child /\
    (!H. P H ==> stmt_state_rel H ctx func ce cx ee q) /\
    (!x v. not_fresh_at si x /\ lookup_var x u = SOME v ==> lookup_var x q = SOME v) /\
    (!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    q.vs_memory = u.vs_memory /\
    eval_operand dst q = SOME ((case bd of Fixed _ => w | Dynamic _ => w + n2w 32) + iw * n2w esz)
    ==> !H. P H ==> Q H child q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i))) (ee,u)
    (\res ef q. ?child. res = INL (Value child) /\ ef = ee /\
      (!H. P H ==> Q H child q) /\ q.vs_current_bb = sf.cs_current_bb /\
      q.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ef r. expr_exit res r)
Proof
  strip_tac >>
  `array_length (ArrayTV etv bd) av < dimword (:256)` by
    metis_tac[targetSubscriptMemoryTheory.target_memory_array_length_bound] >>
  `idx_in_range sgn iw (case bd of Fixed n => n2w n | Dynamic _ => mload (w2n w) u) <=>
    valid_index (ArrayTV etv bd) av i` by
    (Cases_on `bd` >> simp[]
     >- (rename1 `Fixed n` >>
         `array_length (ArrayTV etv (Fixed n)) av = n` by
           (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
         simp[exprSimSubscriptArraySuffixTheory.idx_in_range_integer]) >>
     drule_all targetSubscriptMemoryTheory.target_memory_array_header >> strip_tac >>
     simp[exprSimSubscriptArraySuffixTheory.idx_in_range_integer]) >>
  `stmt_state_rel H ctx func ce cx ee u` by simp[] >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  `~idx_in_range sgn iw (if (case bd of Fixed _ => F | Dynamic _ => T)
      then mload (w2n w) u else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >> gvs[]) >>
  drule_all targetSubscriptMemoryTheory.target_memory_array_abort_path >> strip_tac >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (Cases_on `bd` >> Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all exprSimSubscriptArraySourceTheory.evaluate_array_subscript_oob >> strip_tac >>
  irule exprSimSubscriptArraySuffixTheory.select_result_counted_summary >> simp[] >>
  qexistsl_tac [`Abort Revert_abort t`, `INR (Error (RuntimeError "evaluate_subscripts array_index"))`] >>
  drule exprSimSubscriptArraySourceTheory.select_value_result >> disch_then (fn th => rewrite_tac[th]) >>
  simp[exprSimSubscriptArraySourceTheory.select_value_result,
       vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def, vyperStateTheory.raise_def,
       exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def] >>
  gvs[vyperStateTheory.raise_def]
QED
Resume copied_array_memory_suffix_family[valid]:
  `?q. gas_marked_path F ctx func u 0 (OK q) /\
    (!H. P H ==> stmt_state_rel H ctx func ce cx ee q) /\
    (!x v. not_fresh_at si x /\ lookup_var x u = SOME v ==> lookup_var x q = SOME v) /\
    (!aid a. FLOOKUP u.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    q.vs_memory = u.vs_memory /\
    eval_operand dst q = SOME ((case bd of Fixed _ => w | Dynamic _ => w + n2w 32) + iw * n2w esz) /\
    q.vs_current_bb = sf.cs_current_bb /\ q.vs_inst_idx = LENGTH sf.cs_current_insts` by
    (Cases_on `bd`
     >- (gvs[Excl "valid_index_def"] >>
         `stmt_state_rel H ctx func ce cx ee u` by simp[] >>
         drule_all exprSimSubscriptArrayFramedTheory.fixed_array_subscript_counted_fields >> strip_tac >>
         goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
         irule exprLoweringPropsTheory.stmt_state_rel_fields_transport >>
         conj_tac >- (qexists_tac `H` >> simp[]) >>
         qexists_tac `u` >> simp[]) >>
     suspend "dynamic_path") >>
  drule vyperArrayTheory.array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv bd) av i = SOME child` >>
  `!H. P H ==> Q H child q` by (rpt strip_tac >> first_x_assum irule >> simp[]) >>
  irule exprSimSubscriptArraySuffixTheory.select_result_counted_summary >> simp[] >>
  qexistsl_tac [`OK q`, `INL (Value child)`] >> simp[] >>
  conj_tac
  >- (drule exprSimSubscriptArraySourceTheory.select_value_result >>
      disch_then (fn th => rewrite_tac[th]) >>
      simp[exprSimSubscriptArraySourceTheory.evaluate_array_subscript_result,
           vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def, vyperStateTheory.return_def] >>
      gvs[vyperStateTheory.return_def]) >>
  Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]
QED
Resume copied_array_memory_suffix_family[dynamic_path]:
  gvs[Excl "valid_index_def"] >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exprSimArrayIndexTheory.compile_array_subscript_split,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_ptr_load _ _ _ bop si = (lenop,sl)` >>
  drule targetSubscriptMemoryTheory.target_memory_header_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check iop lenop sgn)
      (array_elem_ptr bop iop T 32 esz))` by
    simp[exprSimArrayIndexTheory.straight_fresh_array_check_ptr] >>
  drule_all exprSimUnopPropsTheory.straight_fresh_cs_extends >> strip_tac >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
    eval_operand lenop t = SOME (mload (w2n w) u) /\
    (!H. P H ==> stmt_state_rel H ctx func ce cx ee t) /\
    (!x v. not_fresh_at si x /\ lookup_var x u = SOME v ==> lookup_var x t = SOME v) /\
    t.vs_allocas = u.vs_allocas /\ t.vs_memory = u.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = sl.cs_current_bb /\
    t.vs_inst_idx = LENGTH sl.cs_current_insts` by
    (qpat_assum `compile_ptr_load _ _ _ _ _ = _` mp_tac >>
     pure_rewrite_tac[contextTheory.compile_ptr_load_def] >> strip_tac >>
     qabbrev_tac `out = STRING #"%" (toString si.cs_next_var)` >>
     qexists_tac `update_var out (mload (w2n w) u) u
                    with vs_inst_idx := SUC u.vs_inst_idx` >>
     `!x. not_fresh_at si x ==> x <> out` by
       (simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     `not_local_ptr ce ee.scopes out` by
       (qunabbrev_tac `out` >> irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
        metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
     `lenop = Var out /\ sl.cs_current_bb = si.cs_current_bb /\
      LENGTH sl.cs_current_insts = SUC (LENGTH si.cs_current_insts)` by
       gvs[Abbr `out`, emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
           compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
           compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
           compileEnvTheory.emit_def] >>
     rpt conj_tac
     >- (pure_rewrite_tac[fragGasModeTheory.gas_marked_path_def, COND_CLAUSES] >>
         qunabbrev_tac `out` >> irule emitHelperPropsTheory.emit_op_zero_path >> simp[] >>
         qexistsl_tac [`[bop]`,`lenop`,`MLOAD`,`sl`] >>
         simp[venomInstTheory.is_terminator_def, emitHelperPropsTheory.step_MLOAD])
     >- simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
             venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
     >- (rpt strip_tac >> simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
         irule exprLoweringPropsTheory.stmt_state_rel_update_var >> simp[])
     >- (rpt strip_tac >> simp[venomStateTheory.lookup_var_def,
             venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
         metis_tac[venomStateTheory.lookup_var_def]) >>
     simp[venomStateTheory.update_var_def]) >>
  `local_ptrs_reserved ce sl` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x. bop = Var x ==> not_fresh_at sl x) /\
   (!x. iop = Var x ==> not_fresh_at sl x)` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand bop t = SOME w /\ eval_operand iop t = SOME iw` by
    (conj_tac >> irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`si`,`u`] >> simp[]) >>
  `stmt_state_rel H ctx func ce cx ee t` by simp[] >>
  drule_all targetSubscriptMemoryTheory.target_array_check_ptr_path_fields >> strip_tac >>
  qexists_tac `t'` >> conj_tac
  >- metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule exprLoweringPropsTheory.stmt_state_rel_fields_transport >>
      conj_tac >- (qexists_tac `H` >> simp[]) >> qexists_tac `t` >> simp[]) >>
  rpt strip_tac >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
Finalise copied_array_memory_suffix_family

Theorem compile_subscript_array_copied_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t s' v t'. eval_expr cx obj s = (INL tv, t) /\
       read_result cx tv s' = (INL v, t') ==>
       expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    subscript_reads_base cx obj idx /\ copies_subscript_base cenv obj idx ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
  `post_value_type cenv obj = expr_type obj` by
    (Cases_on `nocalls` >> fs[] >>
     `int_calls_expr obj = []` by fs[int_calls_expr_def] >>
     drule post_value_type_no_calls >> simp[]) >>
  drule_all_then assume_tac
    exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >>
  `expr_vv_sim ctx func cenv cx ty obj es` by
    (qpat_x_assum `expr_vv_case _ _ _ _ _ obj` mp_tac >>
     simp[expr_vv_case_def] >> disch_then irule >>
     conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  simp[exprSimDefsTheory.expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, lower_value_def,
       exprCallBoundsTheory.expr_child_callback_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       vyperASTTheory.expr_size_def, vyperASTTheory.expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  rename1 `compile_snapshot_vv cenv T bvv sm = (cvv, sc)` >>
  `cs_extends sa sm` by metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends sm sc` by
    (mp_tac exprLoweringPropsTheory.ci_mono_compile_snapshot_vv >>
     disch_then (qspecl_then [`cenv`,`T`,`bvv`,`sm`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  rename1 `unwrap_value cenv ivv si0 = (iop, si)` >>
  `lower_value compile_expr cenv ty idx sc = (iop,si)` by
    simp[lower_value_def, compileEnvTheory.comp_bind_def] >>
  `cs_extends sc si` by
    (mp_tac exprLoweringPropsTheory.ci_mono_lower_value_compile_expr >>
     disch_then (qspecl_then [`cenv`,`ty`,`idx`,`sc`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends si sb` by
    (mp_tac exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     disch_then (qspecl_then
       [`vv_operand cvv`,`iop`,
        `case bd of Fixed _ => F | Dynamic _ => T`,
        `case bd of Fixed n => n | Dynamic _ => 0`,
        `word_scale (case vv_location cvv of NONE => LocMemory | SOME l => l)`,
        `elem_size_in_location cenv (case vv_location cvv of NONE => LocMemory | SOME l => l) et`,
        `is_signed_type (expr_type idx)`,
        `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca (case vv_location cvv of NONE => LocMemory | SOME l => l)`,`si`] mp_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load,
          exprLoweringPropsTheory.ci_mono_def]) >>
  `cs_extends sm sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sa sm func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_vv_sim_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "base_bad"
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "base_normal"
      >> suspend "base_exit") >>
  suspend "base_exempt"
QED

Resume compile_subscript_array_copied_base_case[base_bad]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_assum `subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
  irule gasStorageTheory.gas_bad_storage_at_bind_left >>
  simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result,
       vyperStorageTraceTheory.storage_trace_frame_select]
QED
Resume compile_subscript_array_copied_base_case[base_exit]:
  qexists_tac `marks` >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (disj1_tac >>
      qpat_assum `subscript_reads_base _ _ _` (fn th =>
        pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperStorageTraceTheory.storage_trace_frame_select] >>
      metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  disj2_tac >> disj1_tac >>
  Cases_on `res`
  >- (gvs[] >> metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  rename1 `INR exc` >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  qpat_assum `subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >>
  fs[] >> disj2_tac >> first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_copied_base_case[base_exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  qpat_assum `subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_copied_base_case[base_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o BETA_RULE) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_assum `subscript_reads_base _ _ _` (fn th =>
        pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
           vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperStorageTraceTheory.storage_trace_frame_select] >>
      metis_tac[gasStorageTheory.gas_bad_storage_at_counted_prefix]) >>
  `?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `?tv. res = INL tv` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> ?tv. _` (qspec_then `H0` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `res = _` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    metis_tac[] >>
  gnvs[] >>
  `?base. read_result cx tv (es_end with gas_obs := []) =
          (INL base,es_end with gas_obs := [])` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H0` mp_tac) >> simp[] >>
     metis_tac[abi_args_vv_post_read]) >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx idx` by metis_tac[] >>
  `vv_type bvv = ArrayT et bd` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H0` (drule_then assume_tac)) >>
     metis_tac[compile_array_vv_type]) >>
  `lowered_value_type cenv obj = expr_type obj` by
    (Cases_on `obj` >>
     gvs[vyperASTTheory.expr_type_def, lowered_value_type_def]
     >~ [`Builtin _ bi _`] >-
       (Cases_on `bi` >>
        gvs[lowered_value_type_def, concat_buffer_type_def, vyperASTTheory.expr_type_def] >>
        gvs[expr_body_pre_def] >>
        qpat_x_assum `well_typed_expr env (Builtin _ _ _)` mp_tac >>
        simp[Once well_typed_expr_def, well_typed_builtin_app_def,
             vyperASTTheory.expr_type_def])
     >~ [`TypeBuiltin _ tb _ _`] >-
       (Cases_on `tb` >>
        gvs[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
        gvs[expr_body_pre_def] >>
        qpat_x_assum `well_typed_expr env (TypeBuiltin _ _ _ _)` mp_tac >>
        simp[Once well_typed_expr_def, type_builtin_result_ok_def,
             vyperASTTheory.expr_type_def]) >>
     Cases_on `c` >>
     gvs[lowered_value_type_def, loweringPostsTheory.post_value_type_def,
         compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def,
         vyperASTTheory.expr_type_def]) >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv obj) bvv sm` >>
  rename1 `compile_materialize_vv _ _ _ _ = (dst,scopy)` >>
  `cvv = LocatedValue (ArrayT et bd) (mk_ptr dst LocMemory) /\ sc = scopy` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     gvs[compile_snapshot_vv_def, compileEnvTheory.is_word_type_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]) >>
  gvs[] >>
  `expr_body_pre cenv cx env obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `vyperState$bind (eval_expr cx obj) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL base',es_end with gas_obs := [])` by
    simp[vyperStateTheory.bind_def] >>
  qpat_assum `vyperState$bind _ _ _ = _`
    (mp_then Any mp_tac (REWRITE_RULE [ETA_THM] abiEncodeArgsCaseTheory.abi_args_success_ready)) >>
  simp[compileEnvTheory.is_word_type_def] >> strip_tac >>
  qpat_x_assum `!env' ce. _` (qspecl_then [`env`,`cenv`] mp_tac) >>
  simp[] >> strip_tac >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     `storage_trace_frame (eval_expr cx obj)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     qpat_assum `eval_expr cx obj _ = _`
       (mp_then Any mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `local_ptrs_reserved cenv sm /\
   sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (`exprLoweringProps$ci_mono sa sm` by
       metis_tac[exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND] >>
     gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_compile_var] >>
  `~t.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  `fn_has_code sm sc func` by
    (`fn_has_code sm cs'⁴' func` by
       (irule (cj 2 fragExecTheory.fn_has_code_split) >>
        simp[] >> qexists_tac `sa` >> simp[]) >>
     `cs_extends sc cs'⁴'` by metis_tac[compileEnvTheory.cs_extends_trans] >>
     irule (cj 1 fragExecTheory.fn_has_code_split) >>
     simp[] >> qexists_tac `cs'⁴'` >> simp[]) >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type cenv obj) = SOME tvt /\
          ~is_word_type (post_value_type cenv obj) ==>
       type_memory_bytes cenv (post_value_type cenv obj) = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64` by gvs[] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac
      (Q.INST [`HP` |-> `\H. valid_horizon cx st0 H es_end.storage_trace`]
        compile_materialize_vv_owned_path |> BETA_RULE)) >>
  simp[] >>
  disch_then (qspecl_then [`es`, `env`, `H0`] mp_tac) >>
  simp[compileEnvTheory.is_word_type_def] >> strip_tac >>
  rename1 `gas_marked_path F ctx func t 0 (OK tc)` >>
  `expr_body_pre cenv cx env idx (es_end with gas_obs := [])` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (`exprLoweringProps$ci_mono sm sc` by
       metis_tac[exprLoweringPropsTheory.ci_mono_compile_materialize_vv, pairTheory.SND] >>
     gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `fn_has_code sc si func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >> simp[] >>
     qexists_tac `sm` >> simp[] >>
     irule (cj 1 fragExecTheory.fn_has_code_split) >> simp[] >>
     conj_tac >- metis_tac[compileEnvTheory.cs_extends_trans] >>
     qexists_tac `cs'⁴'` >> simp[] >>
     irule (cj 2 fragExecTheory.fn_has_code_split) >> simp[] >>
     qexists_tac `sa` >> simp[]) >>
  `gas_admissible (vyperState$bind (eval_expr cx idx) (read_result cx))
      expr_res_ok (es_end with gas_obs := [])` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     `expr_body_pre cenv cx env idx (es_end with gas_obs := gs)` by fs[] >>
     drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
       stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) tc /\
       storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!H. _ ==> materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
           (qspec_then `H` (drule_then
             (mp_tac o CONJUNCT1 o REWRITE_RULE [materialize_owned_post_def]))) >>
         simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs]) >>
     qpat_assum `!H. _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` (drule_then
         (ACCEPT_TAC o cj 2 o REWRITE_RULE [loweringPostsTheory.vv_post_def])))) >>
  qpat_assum `expr_sim_case _ _ _ _ _ idx`
    (mp_tac o REWRITE_RULE [expr_sim_case_def]) >>
  disch_then (qspecl_then [`env`, `ty`, `es_end with gas_obs := []`] mp_tac) >>
  `nocalls ==> int_calls_expr idx = []` by fs[int_calls_expr_def] >>
  simp[] >>
  pure_rewrite_tac[exprSimDefsTheory.expr_sim_def] >>
  disch_then (qspecl_then [`st0`, `sc`, `si`, `iop`, `tc`] mp_tac) >>
  simp[] >>
  strip_tac >>
  `gas_marked_exec F (ctx,func)
     (vyperState$bind (vyperState$bind (eval_expr cx obj) (read_result cx))
       (\v. vyperState$return (Value v)))
     (es,s0) marks (INL (Value base')) es_end (OK tc)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[] >> strip_tac >>
     fs[gasSummaryTheory.gas_marked_exec_def] >> conj_tac
     >- (gen_tac >> simp[vyperStateTheory.bind_def, vyperStateTheory.return_def]) >>
     drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `eval_expr cx (Subscript ann obj idx) =
     vyperState$bind
       (vyperState$bind (vyperState$bind (eval_expr cx obj) (read_result cx))
         (\v. vyperState$return (Value v)))
       (\r. vyperState$bind (vyperState$bind (eval_expr cx idx) (read_result cx))
         (\v. select_result cx (expr_type obj) r (ValueSubscript v)))` by
    (simp[eval_expr_subscript_copied_bind, vyperStateTheory.bind_assoc] >>
     simp[FUN_EQ_THM, vyperStateTheory.bind_def, vyperStateTheory.return_def]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `!res out. expr_exit (res : value + exception) out =
    (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) out)` by
    (map_every qx_gen_tac [`res`, `out`] >>
     Cases_on `res` >- simp[] >>
     simp[] >> rename1 `expr_exit (INR exc) out` >>
     mp_tac (Q.ISPECL [`Value`, `INR exc : value + exception`] exprSimDefsTheory.expr_exit_success_map) >>
     simp[] >> metis_tac[]) >>
  pop_assum (fn eq => qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (assume_tac o PURE_REWRITE_RULE [eq])) >>
  qpat_assum `gas_marked_exec _ _ (vyperState$bind _ _) _ _ (INL (Value _)) _ _`
    (mp_then (Pos hd) mp_tac (BETA_RULE
      (framed_array_index_outcome_compose
       |> Q.GEN `k`
       |> Q.ISPEC `\r v. select_result cx (expr_type obj) r (ValueSubscript v)`
       |> Q.GEN `V`
       |> Q.SPEC `\H v ee u.
         expr_post H ctx func cenv cx idx (es_end with gas_obs := []) sc si tc ee v iop u /\
         u.vs_current_bb = si.cs_current_bb /\ u.vs_inst_idx = LENGTH si.cs_current_insts`
       |> Q.GEN `R`
       |> Q.SPEC `\H (res : eval_result + exception) ee out. expr_exit res out`))) >>
  disch_then (fn th => qpat_assum `gas_outcome _ _ _ _ _ _ _ _ _`
    (mp_then (Pos hd) mp_tac th)) >>
  qmatch_goalsub_rename_tac `vv_post _ _ _ _ _ _ _ _ sf _ _ _ _` >>
  qmatch_goalsub_abbrev_tac `LocatedValue ann resultptr` >>
  disch_then (qspec_then `obj` mp_tac) >>
  disch_then (qspec_then `\H res ee u. ?tv. res = INL tv /\
    vv_post H ctx func cenv cx (Subscript ann obj idx) es sa sf s0 ee tv
      (LocatedValue ann resultptr) u /\
    u.vs_current_bb = sf.cs_current_bb /\ u.vs_inst_idx = LENGTH sf.cs_current_insts`
    (irule o BETA_RULE o REWRITE_RULE [gasOutcomeTheory.gas_outcome_def])) >>
  BETA_TAC >>
  reverse conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_select] >>
  suspend "copied_index_suffix"
QED
Resume compile_subscript_array_copied_base_case[copied_index_suffix]:
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 raw.storage_trace`)
  >- (qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[vyperStorageTraceTheory.storage_trace_frame_select]) >>
  `?HI. valid_horizon cx st0 HI raw.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `expr_post HI ctx func cenv cx idx (es_end with gas_obs := []) sc si tc
     (raw with gas_obs := []) v iop u /\
   u.vs_current_bb = si.cs_current_bb /\ u.vs_inst_idx = LENGTH si.cs_current_insts` by
    (qpat_x_assum `!H. valid_horizon _ _ H raw.storage_trace ==> _`
      (qspec_then `HI` mp_tac) >> simp[]) >>
  `vyperState$bind (eval_expr cx idx) (read_result cx)
     (es_end with gas_obs := gas_explicit imarks tc.vs_gas_readings) =
     (INL v,raw with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     pure_rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `!H. valid_horizon cx st0 H raw.storage_trace ==>
       valid_horizon cx st0 H es_end.storage_trace` by
    (rpt strip_tac >> qpat_assum `vyperState$bind _ _ _ = _`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[vyperStorageTraceTheory.storage_trace_frame_bind_all,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  `expr_body_pre cenv cx env idx
      (es_end with gas_obs := gas_explicit imarks tc.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `?ir. eval_expr cx idx (es_end with gas_obs := gas_explicit imarks tc.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
    read_result cx ir (raw with gas_obs := []) = (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >> metis_tac[]) >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt v` by metis_tac[] >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `?etv. tv' = ArrayTV etv bd /\ evaluate_type (get_tenv cx) et = SOME etv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_ArrayT_cases] >>
  gvs[] >>
  `?av. base' = ArrayV av` by
    (Cases_on `base'` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `!x. dst = Var x ==> not_fresh_at sc x` by
    metis_tac[exprOperandVarTheory.compiler_materialize_vv_var] >>
  `materialize_owned_post HI ctx func cenv cx obj es sa sm sc s0
     (es_end with gas_obs := []) (ArrayV av) dst (ArrayTV etv bd) tc` by metis_tac[] >>
  `!l. dst <> Label l` by
    metis_tac[abiEncodeArgsSimTheory.abi_args_materialize_not_label] >>
  `MAP FDOM (raw with gas_obs := []).scopes =
   MAP FDOM (es_end with gas_obs := []).scopes` by
    (qpat_assum `eval_expr cx idx _ = _`
      (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_post HI ctx func cenv cx idx (es_end with gas_obs := []) sc si tc
     (raw with gas_obs := [])
     (IntV (if is_signed_type (expr_type idx) then w2i iw else &w2n iw)) iop u` by metis_tac[] >>
  drule copied_array_snapshot_after_index >>
  simp[] >> disch_then drule >> simp[] >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt _` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                          compileEnvTheory.is_word_type_def]) >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  `!x. dst = Var x ==> not_fresh_at si x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, compileEnvTheory.cs_extends_def] >>
  `local_ptrs_reserved cenv si` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var, compileEnvTheory.cs_extends_def] >>
  `cs_extends sa si` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code si sf func` by
    (irule (cj 2 fragExecTheory.fn_has_code_split) >> simp[] >>
     qexists_tac `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H raw.storage_trace ==>
    stmt_state_rel H ctx func cenv cx (raw with gas_obs := []) u` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H raw.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     simp[loweringPostsTheory.expr_post_def,
          exprLoweringPropsTheory.stmt_state_rel_start_gas_obs]) >>
  `~u.vs_halted` by
    (drule exprSimSliceOrdinaryContinueTheory.slice_marked_read_ok_not_halted >> simp[]) >>
  `gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (Value (ArrayV av))
       (ValueSubscript (IntV (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)))))
    (raw with gas_obs := [],u)
    (\res ef q. ?child. res = INL (Value child) /\ ef = (raw with gas_obs := []) /\
       (!H. valid_horizon cx st0 H raw.storage_trace ==>
         vv_post H ctx func cenv cx (Subscript ann obj idx) es sa sf s0
           (raw with gas_obs := []) (Value child) (LocatedValue ann resultptr) q) /\
       q.vs_current_bb = sf.cs_current_bb /\ q.vs_inst_idx = LENGTH sf.cs_current_insts)
    (\res ef r. expr_exit res r)` by
    (irule (BETA_RULE (copied_array_memory_suffix_family
       |> Q.GEN `P` |> Q.ISPEC `(\H. valid_horizon cx st0 H raw.storage_trace)`
       |> Q.GEN `Q` |> Q.SPEC `(\H child q. vv_post H ctx func cenv cx
         (Subscript ann obj idx) es sa sf s0 (raw with gas_obs := [])
         (Value child) (LocatedValue ann resultptr) q)`)) >>
     conj_tac >- metis_tac[] >>
     simp[] >>
     qexistsl_tac [`dst`,`cenv`,`elem_ptr`,`type_memory_bytes cenv et`,
       `iop`,`iw`,`is_signed_type (expr_type idx)`,`si`,`w`] >>
     fs[contextTheory.vv_operand_def, contextTheory.vv_location_def,
        contextTheory.mk_ptr_def, compileEnvTheory.word_scale_def,
        compileEnvTheory.elem_size_in_location_def,
        compileEnvTheory.is_slot_addressed_def] >>
     rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
     `ann = et` by
       (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
        simp[exprSimHypsDefsTheory.expr_body_pre_def,
             Once vyperTypeSystemTheory.well_typed_expr_def] >>
        strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
        drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >>
        strip_tac >> Cases_on `vt` >>
        gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
        gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
     gvs[Abbr `resultptr`, GSYM contextTheory.mk_ptr_def] >>
     `well_formed_type_value etv` by
       metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
     `value_has_type etv child` by
       metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
     `val_wf etv child` by
       metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     `type_memory_bytes cenv ann = type_memory_size etv` by
       (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
        goal_assum (drule_at Any) >>
        qexistsl_tac [`env`,`es_end`] >> simp[]) >>
     `valid_horizon cx st0 H es_end.storage_trace /\
      valid_horizon cx st0 H es.storage_trace` by metis_tac[] >>
     `materialize_owned_post H ctx func cenv cx obj es sa sm sc s0
       (es_end with gas_obs := []) (ArrayV av) dst (ArrayTV etv bd) tc` by metis_tac[] >>
     `expr_post H ctx func cenv cx idx (es_end with gas_obs := []) sc si tc
       (raw with gas_obs := [])
       (IntV (if is_signed_type (expr_type idx) then w2i iw else &w2n iw)) iop u` by metis_tac[] >>
     `sub_layout (ArrayTV etv bd) (ArrayV av)
       ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
         Num (if is_signed_type (expr_type idx) then w2i iw else &w2n iw) * type_memory_size etv)
       etv child` by
       (irule (SRULE [] (Q.INST [`k` |-> `0`] sub_layout_array_element)) >>
        simp[loweringPostsTheory.sub_layout_def] >> goal_assum (drule_at Any) >> simp[]) >>
     `w2n w + type_memory_size (ArrayTV etv bd) < dimword (:256)` by
       (`stmt_state_rel H ctx func cenv cx raw u` by simp[] >>
        drule exprSimPropsTheory.stmt_state_rel_region_lt >> metis_tac[]) >>
     `!n b len. local_region cenv raw.scopes q n b len ==>
       type_memory_size (ArrayTV etv bd) + w2n w <= b \/ b + len <= w2n w` by
       (rpt strip_tac >>
        `local_region cenv raw.scopes u n b len` by
          (irule exprSimPropsTheory.local_region_frame >>
           conj_tac >- (qexists_tac `func` >>
             metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
                       loweringStateRelDefsTheory.state_rel_def]) >>
           qexistsl_tac [`si`,`raw.scopes`,`q`] >> simp[] >> metis_tac[]) >>
        metis_tac[]) >>
     irule copied_array_owned_child_endpoint >>
     simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
     goal_assum (drule_at (Pat `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >>
     qexists_tac `if is_signed_type (expr_type idx) then w2i iw else &w2n iw` >>
     simp[] >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     conj_tac >-
       (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
        mp_tac (Q.SPECL [`dst`,`iop`,`case bd of Fixed _ => F | Dynamic _ => T`,
          `case bd of Fixed n => n | Dynamic _ => 0`,`32`,`type_memory_bytes cenv ann`,
          `is_signed_type (expr_type idx)`,
          `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory`,`si`]
          exprLoweringPropsTheory.ci_mono_compile_array_subscript) >>
        simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load] >>
        simp[exprLoweringPropsTheory.ci_mono_def] >> rpt strip_tac >> gvs[] >> decide_tac) >>
     conj_tac >-
       (mp_tac (Q.SPECL [`cenv`,`ArrayT ann bd`,`bvv`,`sm`]
          exprLoweringPropsTheory.ci_mono_compile_materialize_vv) >>
        simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
     conj_tac >- (fs[loweringPostsTheory.sub_layout_def] >>
       mp_tac (Q.SPEC `child` (Q.SPEC `etv` exprSimPropsTheory.val_footprint_le)) >> simp[] >> decide_tac) >>
     conj_tac >- (fs[loweringPostsTheory.sub_layout_def] >>
       mp_tac (Q.SPEC `child` (Q.SPEC `etv` exprSimPropsTheory.val_footprint_le)) >> simp[] >> decide_tac) >>
     `valid_index (ArrayTV etv bd) av
        (if is_signed_type (expr_type idx) then w2i iw else &w2n iw)` by
       (irule vyperArrayTheory.array_index_bounds >>
        reverse conj_tac >- metis_tac[] >>
        Cases_on `av` >> Cases_on `bd` >>
        gvs[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_wf_def]) >>
     fs[vyperArrayTheory.valid_index_def] >>
     `iw = n2w (Num (if is_signed_type (expr_type idx) then w2i iw else &w2n iw))` by
       (Cases_on `is_signed_type (expr_type idx)` >> gvs[integer_wordTheory.w2i_def] >>
        Cases_on `word_msb iw` >> gvs[]) >>
     qmatch_goalsub_abbrev_tac `Num ii` >>
     `iw * n2w (type_memory_size etv) = n2w (Num ii * type_memory_size etv)` by
       (qpat_x_assum `iw = _` (fn th => once_rewrite_tac [th]) >>
        simp[Abbr `ii`, wordsTheory.word_mul_n2w]) >>
     asm_rewrite_tac[] >>
     Cases_on `bd` >>
     fs[loweringPostsTheory.sub_layout_def] >>
     simp[GSYM wordsTheory.WORD_ADD_ASSOC, GSYM wordsTheory.word_add_n2w] >>
     qmatch_goalsub_abbrev_tac `n2w k` >>
     `k < dimword (:256) /\ w2n w + k < dimword (:256)` by
       (unabbrev_all_tac >> decide_tac) >>
     `w2n (n2w k : bytes32) = k` by simp[wordsTheory.w2n_n2w] >>
     simp[wordsTheory.w2n_add_2]) >>
  qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[gasSummaryTheory.gas_summary_at_def] >> rpt strip_tac >>
  qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
  disj1_tac >>
  `es_end.storage_trace = raw.storage_trace` by
    (qpat_x_assum `_ with gas_obs := [] = _` (mp_tac o Q.AP_TERM `\s. s.storage_trace`) >> simp[]) >>
  metis_tac[]
QED
Finalise compile_subscript_array_copied_base_case

Theorem compile_subscript_array_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t s' tv' t'. eval_expr cx obj s = (INL tv, t) /\
       (if subscript_reads_base cx obj idx
        then do v <- read_result cx tv; return (Value v) od
        else return tv) s' = (INL tv', t') ==>
       expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  Cases_on `~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
            (!t r t'. eval_expr cx idx t = (INL r, t') ==>
                      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
            (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
            ((~cenv.ce_is_ctor /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
             ((?n. bd = Fixed n) /\
              (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))`
  >- (`!s tv t. eval_expr cx obj s = (INL tv, t) ==>
                expr_sim_case nocalls ctx func cenv cx idx` by
        (rpt strip_tac >>
         qpat_x_assum `!s tv t s' tv' t'. _`
           (qspecl_then [`s`, `tv`, `t`, `t`, `tv`, `t`] mp_tac) >>
         fs[vyperStateTheory.return_def]) >>
      qpat_x_assum `!s tv t s' tv' t'. _` kall_tac >>
      irule compile_subscript_array_framed_base_case >> asm_rewrite_tac[] >>
      metis_tac[]) >>
  Cases_on `subscript_reads_base cx obj idx /\ copies_subscript_base cenv obj idx`
  >- (irule compile_subscript_array_copied_base_case >> rpt conj_tac
      >~ [`read_result`]
      >- (rpt strip_tac >>
          qpat_x_assum `!s tv t s' tv' t'. _`
            (qspecl_then [`s`, `tv`, `t`, `s'`, `Value v`, `t'`] mp_tac) >>
          fs[vyperStateTheory.bind_def, vyperStateTheory.return_def])
      >~ [`ValPT`] >- (qexistsl [`bd`, `et`] >> fs[]) >>
      fs[]) >>
  irule compile_subscript_array_place_base_case >> asm_rewrite_tac[] >>
  qexistsl [`bd`, `et`] >> asm_rewrite_tac[]
QED
