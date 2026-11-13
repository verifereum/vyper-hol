(*
 * Expression simulation: compile_subscript_array_case, a case of exprSimPlaces on its
 * own so it can be proved apart.
 *
 * TOP-LEVEL:
 *   compile_subscript_array_case — an element of a static or dynamic array,
 *     with the bounds-check abort, by two subcases:
 *     compile_subscript_array_framed_base_case for a base the index's frame
 *     keeps (a runtime immutable, or a static array of no dynamic array in
 *     memory), and compile_subscript_array_place_base_case for the rest,
 *     split on subscript_overlap into
 *     compile_subscript_array_copied_base_case (the base read and copied
 *     before the index) and compile_subscript_array_unframed_base_case,
 *     itself split on subscript_base_live_after into
 *     compile_subscript_array_live_base_case and the admitted leaf
 *     compile_subscript_array_stale_base_case.
 *)

Theory exprSimSubscriptArray
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimSubscriptArrayFramed exprSimSubscriptArrayCompose
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph
  exprSimCopiedPrefix exprSimCopiedCompile exprSimCopiedCompose
  exprSimCopiedAlloc exprSimCopiedSnapshot exprSimCopiedFrame exprSimCopiedSuffix
  exprSimCopiedBuiltinAnnotation bodyPtrAttributeSource exprOperandVar
  aggregateCountedPureFramePrep exprSimCopiedHistory
  exprSimSubscriptArrayLiveMemory exprSimSubscriptArrayLiveMemoryValue
  exprSimSubscriptArrayLiveImmutable exprSimSubscriptArrayLiveStorageSuffix exprReasonOperand

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
   contain no length word, so the index's expr_post keeps them (its
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
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "base_normal"
      >> suspend "base_exit") >>
  suspend "base_exempt"
QED

Resume compile_subscript_array_framed_base_case[base_exit]:
  Cases_on `res` >- fs[] >> rename1 `INR exc` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >> fs[]
QED
Resume compile_subscript_array_framed_base_case[base_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_framed_base_case[base_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
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
  pure_rewrite_tac[GSYM gasOutcomeTheory.gas_outcome_def] >>
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
  >- metis_tac[gasSummaryTheory.gas_marked_exec_def,
               fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac
  >- (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
      `expr_body_pre cenv cx env idx (es_end with gas_obs := gs)` by fs[] >>
      drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_gas_obs,
           exprLoweringPropsTheory.immutable_alloca_sep_def] >>
      metis_tac[]) >>
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
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                          gas_explicit imarks t.vs_gas_readings) =
      (INL tv,es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit imarks t.vs_gas_readings` mp_tac o CONJUNCT1) >>
     simp[]) >>
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
      qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o CONJUNCT1 o CONJUNCT2 o
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
     drule type_place_expr_vtype_annotation >> simp[] >> strip_tac >>
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
      exprSimSubscriptArraySuffixTheory.framed_array_suffix_summary) >>
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

(* An array subscript whose index may write a variable its base reads
   (subscript_overlap; vyperlang/vyper's _lower_array_subscript).  The
   source reads the base's value before the index (subscript_reads_base),
   and the lowering copies the base into a fresh memory buffer before
   lowering the index (copies_subscript_base, compile_snapshot_vv cenv T),
   so the element is selected from that copy, which the index's fragment
   leaves as it is. *)
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
     conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  simp[exprSimDefsTheory.expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript_copied_base_prefix >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [exprSimDefsTheory.expr_vv_sim_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "copied_normal"
      >> suspend "copied_exit") >>
  suspend "copied_exempt"
QED
Resume compile_subscript_array_copied_base_case[copied_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `vv_type bvv = ArrayT et bd` by
    metis_tac[compile_expr_array_result_type] >>
  `vv_type (FST (compile_expr cenv ty obj sa)) = ArrayT et bd` by simp[] >>
  drule_all compile_expr_array_subscript_copied >> strip_tac >> gvs[] >>
  `?tvt. evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tvt` by
    metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
  `type_memory_bytes cenv (ArrayT et bd) = type_memory_size tvt /\
   type_memory_size tvt < 2 ** 64` by
    metis_tac[expr_body_pre_copy_ok, compileEnvTheory.is_word_type_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sm x` by
    metis_tac[CONJUNCT1 exprOperandVarTheory.compiler_compile_var] >>
  `?v a. read_result cx tv (es_end with gas_obs := []) =
           (INL v, es_end with gas_obs := []) /\
         eval_operand (vv_operand bvv) t = SOME a` by
    metis_tac[loweringPostsTheory.vv_post_def, bodyPtrAttributeSourceTheory.attribute_vv_holds_read_operand] >>
  `ci_mono sa1 su /\ ci_mono su sn /\ ci_mono sn si /\ ci_mono si sb` by
    (rpt conj_tac
     >- metis_tac[exprLoweringPropsTheory.ci_mono_unwrap_value, pairTheory.SND]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_compile_store_memory, pairTheory.SND]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_compile_expr, pairTheory.SND] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     pure_rewrite_tac [pairTheory.SND] >>
     disch_then (SUBST1_TAC o SYM) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `cs_extends sa1 sb` by
    metis_tac[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sm sa1 func` by
    metis_tac[fragExecTheory.fn_has_code_split,
              loweringHaltTheory.compile_alloc_buffer_extends] >>
  `type_memory_bytes cenv (ArrayT et bd) < dimword (:256)` by
    (qpat_x_assum `type_memory_size tvt < _` mp_tac >>
     simp[wordsTheory.dimword_def]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    fs[loweringPostsTheory.vv_post_def] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimIfExpWidenedCountedTheory.literal_alloc_buffer_counted >>
  disch_then (qx_choose_then `u` (qx_choose_then `w` strip_assume_tac)) >>
  `eval_operand (vv_operand bvv) u = eval_operand (vv_operand bvv) t` by
    (Cases_on `vv_operand bvv` >> gvs[venomStateTheory.eval_operand_def]) >>
  `!n b k. local_region cenv (es_end with gas_obs := []).scopes u n b k <=>
            local_region cenv (es_end with gas_obs := []).scopes t n b k` by
    (rpt gen_tac >> irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `sm` >> simp[]) >>
  `vv_post ctx func cenv cx obj es sa sa1 s0 (es_end with gas_obs := []) tv bvv u` by
    (irule exprSimIfExpWidenedAdapterTheory.vv_post_alloc_mono_frame >> simp[] >>
     qexistsl [`t`, `sm`] >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> irule freshWritesTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all aggregateCountedPureFramePrepTheory.aggregate_body_tuple_marked_child_source >>
  strip_tac >> gvs[] >>
  `value_has_type tvt v` by metis_tac[] >>
  `ci_mono sm sa1` by
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `sa.cs_next_var <= sa1.cs_next_var /\ sa.cs_next_id <= sa1.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x. vv_operand bvv = Var x ==> not_fresh_at sa1 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,
              exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa1 su func /\ fn_has_code su sn func` by
    metis_tac[fragExecTheory.fn_has_code_split,
              exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_trans] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>

  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ai (fn_insts func)` >>
  `ai.inst_opcode = ALLOCA /\ ai.inst_id = sm.cs_next_id` by
    simp[Abbr `ai`, venomInstTheory.mk_inst_def] >>
  `!name b len. local_region cenv (es_end with gas_obs := []).scopes u name b len ==>
     w2n w + type_memory_size tvt <= b \/ b + len <= w2n w` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `sa.cs_next_id <= ai.inst_id` by simp[] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) copied_array_snapshot_tail >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  impl_tac >- (simp[] >> gvs[arithmeticTheory.ADD_COMM]) >>
  disch_then (qx_choose_then `uw` (qx_choose_then `cap` strip_assume_tac)) >>
  `gas_marked_exec F (ctx,func) (read_result cx tv)
     (es_end with gas_obs := [],t) [] (INL v) (es_end with gas_obs := []) (OK cap)` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  `gas_marked_exec F (ctx,func)
     (bind (eval_expr cx obj) (\r. bind (read_result cx r) (\v. return (Value v))))
     (es,s0) marks (INL (Value v)) (es_end with gas_obs := []) (OK cap)` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> conj_tac
     >- simp[vyperStateTheory.bind_def, vyperStateTheory.return_def] >>
     metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD_0]) >>
  pure_rewrite_tac[GSYM gasOutcomeTheory.gas_outcome_def] >>
  irule copied_array_after_capture >>
  simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  conj_tac >- suspend "copied_suffix" >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr cx obj) _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre cenv cx env idx (es_end with gas_obs := [])` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `expr_sim_case nocalls ctx func cenv cx idx` by metis_tac[] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                        exprLoweringPropsTheory.ci_mono_def] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split,
                        exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_trans] >>
  conj_tac
  >- (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
      `expr_body_pre cenv cx env idx (es_end with gas_obs := gs)` by fs[] >>
      drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]) >>
  conj_tac >- (gvs[exprLoweringPropsTheory.stmt_state_rel_def,
                  loweringStateRelDefsTheory.state_rel_gas_obs,
                  loweringPostsTheory.expr_post_def,
                  typedMemoryCopyTheory.typed_copy_state_frame_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ idx` mp_tac >>
  simp[expr_sim_case_def] >> disch_then irule >>
  conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
  qexists_tac `env` >> simp[]

QED
Resume compile_subscript_array_copied_base_case[copied_exit]:
  Cases_on `res` >- fs[] >> rename1 `INR exc` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  drule eval_expr_subscript_copied_bind >>
  disch_then (qspec_then `ann` SUBST1_TAC) >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >> fs[]
QED
Resume compile_subscript_array_copied_base_case[copied_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  drule eval_expr_subscript_copied_bind >>
  disch_then (qspec_then `ann` SUBST1_TAC) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_copied_base_case[copied_suffix]:
  rpt gen_tac >> strip_tac >>
  `vyperState$bind (eval_expr cx idx) (read_result cx)
     (es_end with gas_obs := gas_explicit imarks cap.vs_gas_readings) =
     (INL v', raw with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                         gas_explicit imarks cap.vs_gas_readings) =
     (INL tv, es_end with gas_obs := gas_explicit imarks cap.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr cx obj) _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit imarks cap.vs_gas_readings` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre cenv cx env idx
     (es_end with gas_obs := gas_explicit imarks cap.vs_gas_readings)` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `?ir. eval_expr cx idx
      (es_end with gas_obs := gas_explicit imarks cap.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
      read_result cx ir (raw with gas_obs := []) = (INL v',raw with gas_obs := [])` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >> metis_tac[]) >>
  drule_at (Pat `eval_expr cx idx _ = _`) expr_body_pre_runtime_typed >>
  disch_then drule >> strip_tac >>
  `value_has_type tvt' v'` by metis_tac[] >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `?etv. tvt = ArrayTV etv bd /\ evaluate_type (get_tenv cx) et = SOME etv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_ArrayT_cases] >>
  gvs[] >>
  `?av. v = ArrayV av` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >> gvs[] >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt' (IntV _)` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def,
                         compileEnvTheory.is_word_type_def]) >>
  `local_ptrs_reserved cenv sn /\ local_ptrs_reserved cenv si` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
              exprLoweringPropsTheory.ci_mono_def] >>
  `!x. iop = Var x ==> not_fresh_at si x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >> impl_tac
     >- (conj_tac >- fs[expr_body_pre_def] >>
         metis_tac[expr_body_pre_var_types_well_formed]) >> simp[]) >>
  `not_fresh_at sn p` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, exprLoweringPropsTheory.ci_mono_def] >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by
    metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `memory_value_rel (ArrayTV etv bd) (ArrayV av) (w2n w) cap.vs_memory` by
    metis_tac[memoryValueEncodingTheory.memory_layout_bridges,
              memoryValueEncodingTheory.memory_layout_bridge_def] >>
  drule_at (Pat `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _`) copied_array_index_frame >>
  disch_then (drule_at (Pat `FLOOKUP cap.vs_allocas _ = _`)) >>
  disch_then (qspecl_then [`ArrayV av`,`ArrayTV etv bd`,`p`] mp_tac) >>
  impl_tac >-
    (conj_tac
     >- (qpat_x_assum `sm.cs_next_id < sa1.cs_next_id` mp_tac >>
         qpat_x_assum `ci_mono sa1 su` mp_tac >>
         qpat_x_assum `ci_mono su sn` mp_tac >>
         rpt (pop_assum kall_tac) >>
         simp[exprLoweringPropsTheory.ci_mono_def]) >>
     conj_tac
     >- (qpat_x_assum `!name base len. local_region _ _ cap _ _ _ ==> _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[]) >>
     simp[]) >>
  strip_tac >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     qpat_x_assum `expr_type obj = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
     rpt strip_tac >>
     gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def] >>
     strip_tac >>
     qpat_x_assum `ArrayT _ _ = _`
       (fn th => fs[SYM th, vyperTypeSystemTheory.subscript_vtype_def])) >>
  gvs[] >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`es`] >> fs[expr_body_pre_def]) >>
  `elem_size_in_location cenv LocMemory ann = type_memory_size etv /\
   word_scale LocMemory = 32` by
    simp[compileEnvTheory.elem_size_in_location_def,
         compileEnvTheory.is_slot_addressed_def, compileEnvTheory.word_scale_def] >>
  gs[] >>
  `ci_mono sm sa1` by
    (qspec_then `type_memory_size (ArrayTV etv bd)`
       (qspec_then `sm` mp_tac) exprLoweringPropsTheory.ci_mono_compile_alloc_buffer >> simp[]) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by
    (qpat_x_assum `sa.cs_next_var <= sm.cs_next_var` mp_tac >>
     qpat_x_assum `ci_mono sm sa1` mp_tac >>
     qpat_x_assum `ci_mono sa1 su` mp_tac >>
     qpat_x_assum `ci_mono su sn` mp_tac >>
     qpat_assum `sa.cs_next_id <= sm.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  drule_at (Pat `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _`)
    copied_array_history_after_index >>
  disch_then (drule_at (Pat `locals_kept _ es _ s0 cap`)) >>
  disch_then (qspecl_then [`sa`,`obj`,`ann`] mp_tac) >>
  impl_tac >-
    (simp[] >>
     qpat_x_assum `!aid off len. _ ==> mem_bytes_at off len cap.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  `gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT ann bd) (Value (ArrayV av))
      (ValueSubscript (IntV (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)))))
    (raw with gas_obs := [],u')
    (\res ee q. ?v. res = INL (Value v) /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee (Value v)
        (LocatedValue ann (mk_ptr dst LocMemory)) q /\
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee out. expr_exit res out)` by
    (irule copied_array_suffix_summary >> simp[] >>
     conj_tac >-
       (qpat_x_assum `!aid off len. _ ==> mem_bytes_at off len u'.vs_memory = _` mp_tac >>
        rpt (pop_assum kall_tac) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
     conj_tac >-
       (qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[gasSummaryTheory.gas_marked_exec_def,
             fragGasModeTheory.gas_marked_path_def] >>
        metis_tac[fragGasPathTheory.gas_path_normal]) >>
     conj_tac >-
       (qpat_x_assum `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[loweringPostsTheory.expr_post_def,
             exprLoweringPropsTheory.stmt_state_rel_def,
             loweringStateRelDefsTheory.state_rel_def]) >>
     reverse conj_tac >-
       (qpat_x_assum `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _` mp_tac >>
        simp[loweringPostsTheory.expr_post_def]) >>
     qexistsl_tac [`sm.cs_next_id`,`w`,`Var p`,`iop`,`iw`,`si`,
                   `is_signed_type (expr_type idx)`] >> simp[] >>
     conj_tac >-
       (qpat_x_assum `sm.cs_next_id < sa1.cs_next_id` mp_tac >>
        qpat_x_assum `ci_mono sa1 su` mp_tac >>
        qpat_x_assum `ci_mono su sn` mp_tac >>
        qpat_x_assum `ci_mono sn si` mp_tac >>
        qpat_x_assum `ci_mono si sb` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
     conj_tac >-
       (qpat_x_assum `!name b len. local_region _ _ cap _ _ _ ==> _` mp_tac >>
        qpat_x_assum `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _` mp_tac >>
        qpat_x_assum `stmt_state_rel _ _ _ _ es_end cap` mp_tac >>
        qpat_x_assum `local_ptrs_reserved cenv sn` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[loweringPostsTheory.expr_post_def,
             exprLoweringPropsTheory.stmt_state_rel_def,
             loweringStateRelDefsTheory.state_rel_def] >>
        rpt strip_tac >>
        `local_region cenv es_end.scopes cap n lb lsz` by
          (irule exprSimPropsTheory.local_region_frame >>
           conj_tac >- metis_tac[] >>
           qexistsl_tac [`sn`,`raw.scopes`,`u'`] >>
           fs[loweringPostsTheory.locals_kept_def]) >> metis_tac[]) >>
     conj_tac >- (irule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >>
                   goal_assum (drule_at Any)) >>
     conj_tac >-
       (qpat_x_assum `not_fresh_at sn p` mp_tac >>
        qpat_x_assum `ci_mono sn si` mp_tac >>
        rpt (pop_assum kall_tac) >>
        metis_tac[freshWritesTheory.not_fresh_at_mono,
                  exprLoweringPropsTheory.ci_mono_def]) >>
     conj_tac >-
       (qpat_x_assum `sa.cs_next_var <= sn.cs_next_var` mp_tac >>
        qpat_x_assum `ci_mono sn si` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
     conj_tac >-
       (qpat_x_assum `fn_has_code sm sb func` mp_tac >>
        qpat_x_assum `ci_mono sm sa1` mp_tac >>
        qpat_x_assum `ci_mono sa1 su` mp_tac >>
        qpat_x_assum `ci_mono su sn` mp_tac >>
        qpat_x_assum `ci_mono sn si` mp_tac >>
        qpat_x_assum `ci_mono si sb` mp_tac >>
        rpt (pop_assum kall_tac) >>
        simp[exprLoweringPropsTheory.ci_mono_def] >>
        metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans]) >>
     qpat_x_assum `memory_value_rel _ _ _ u'.vs_memory` mp_tac >>
     qpat_x_assum `value_has_type (ArrayTV _ _) _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[memoryValueEncodingTheory.memory_encoding_bridges,
               memoryValueEncodingTheory.memory_encoding_bridge_def]) >>
  qpat_x_assum `gas_summary_at _ _ [] _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  metis_tac[]
QED
Finalise compile_subscript_array_copied_base_case

(* The base's source result still reads at the index's end: a local's
   path, a storage place's slots (live and in range), or a runtime
   immutable's path still evaluate there; a value needs its pointer in
   memory (a constructor immutable's popped value points into the staged
   buffer, LocCode) and the locals kept, or a static array with no
   dynamic array inside it. *)
Definition subscript_base_live_after_def:
  (subscript_base_live_after cenv cx (obj:expr) (et:type) (bd:bound) (PlaceR (MemoryPlace id path)) t t' <=>
     !entry. lookup_scopes id t'.scopes = SOME entry ==>
             ?v. evaluate_subscripts entry.type entry.value path = INL v) /\
  (subscript_base_live_after cenv cx obj et bd (PlaceR (StoragePlace tr slot vt)) t t' <=>
     storage_read_live cx tr (get_storage cx t' tr) slot vt /\
     slots_in_range (get_storage cx t' tr) (w2n slot) vt) /\
  (subscript_base_live_after cenv cx obj et bd (PlaceR (ImmutablePlace src id path)) t t' <=>
     !itv iv.
       FLOOKUP (case ALOOKUP t'.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) id = SOME (itv, iv) ==>
       ?v. evaluate_subscripts itv iv path = INL v) /\
  (subscript_base_live_after cenv cx obj et bd (HashMapRef _ _ _ _) t t' <=> T) /\
  (subscript_base_live_after cenv cx obj et bd (Value _) t t' <=>
     (!ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory) /\
     (t'.scopes = t.scopes \/
      (?n. bd = Fixed n /\
           !etv. evaluate_type (get_tenv cx) et = SOME etv ==> dynarray_free etv)))
End

(* compile_subscript_array_unframed_base_case with the base live at the
   index's end (subscript_base_live_after): vv_place_ptr ties the base's
   pointer to its source place; the live place's current value supplies
   the array representation after the index's fragment. *)
Theorem compile_subscript_array_live_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    ~((!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) /\
    (!s env tv t gs ir t'.
       expr_body_pre cenv cx env (Subscript ann obj idx) s /\
       eval_expr cx obj s = (INL tv, t) /\
       eval_expr cx idx (t with gas_obs := gs) = (INL ir, t') ==>
       subscript_base_live_after cenv cx obj et bd tv t t') ==>
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
     conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
     qexists_tac `env` >> simp[]) >>
  simp[exprSimDefsTheory.expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb /\ st2.cs_next_id <= sb.cs_next_id` by
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
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gasSummaryTheory.gas_summary_at_def])
      >- suspend "base_normal"
      >> suspend "base_exit") >>
  suspend "base_exempt"
QED
Resume compile_subscript_array_live_base_case[base_exit]:
  Cases_on `res` >- fs[] >> rename1 `INR exc` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >> fs[]
QED
Resume compile_subscript_array_live_base_case[base_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume compile_subscript_array_live_base_case[base_normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
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
  pure_rewrite_tac[GSYM gasOutcomeTheory.gas_outcome_def] >>
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
  >- metis_tac[gasSummaryTheory.gas_marked_exec_def,
               fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac
  >- (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
      `expr_body_pre cenv cx env idx (es_end with gas_obs := gs)` by fs[] >>
      drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_gas_obs,
           exprLoweringPropsTheory.immutable_alloca_sep_def] >>
      metis_tac[]) >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ idx` mp_tac >>
  simp[expr_sim_case_def] >> disch_then irule >>
  conj_tac >- (strip_tac >> fs[int_calls_expr_def]) >>
  qexists_tac `env` >> simp[]
QED
Resume compile_subscript_array_live_base_case[base_suffix]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s tv t. eval_expr _ _ _ = _ ==> expr_sim_case _ _ _ _ _ _` kall_tac >>
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
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                          gas_explicit imarks t.vs_gas_readings) =
      (INL tv,es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit imarks t.vs_gas_readings` mp_tac o CONJUNCT1) >>
     simp[]) >>
  `subscript_base_live_after cenv cx obj et bd tv
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)
     (raw with gas_obs := [])` by
    (qpat_x_assum `!s env tv t gs ir t'. _` irule >>
     conj_tac >- (simp[] >> metis_tac[]) >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >>
     qexists_tac `env` >> simp[]) >>
  `~u.vs_halted` by
    metis_tac[gasSummaryTheory.gas_marked_exec_def,
              fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  qpat_x_assum `!s env tv t gs ir t'. _` kall_tac >>
  qpat_x_assum `_ \/ _` kall_tac >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ loc = p.ptr_location` by
    (Cases_on `bvv`
     >- (Cases_on `tv`
         >- (fs[subscript_base_live_after_def] >>
             qpat_x_assum `!ty st. vv_location _ = _` (qspecl_then [`ty`,`sa`] mp_tac) >>
             simp[contextTheory.vv_location_def])
         >- gvs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_at_def,
                compileEnvTheory.is_word_type_def] >>
         fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def,
            vyperStateTheory.read_result_def, vyperStateTheory.raise_def]) >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [loweringPostsTheory.vv_post_def]) >>
     simp[loweringPostsTheory.vv_holds_def, compileEnvTheory.is_bytestring_type_def] >>
     rpt strip_tac >> gvs[Abbr `loc`, contextTheory.vv_location_def]) >>
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
  `expr_sim_inv cenv cx env es_end` by fs[expr_body_pre_def] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `eval_expr cx obj _ = _`
      (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base] >>
  `!l. p.ptr_operand <> Label l` by
    (`reason_uniform_shape compile_expr cenv ty obj` by
       (irule compile_expr_reason_uniform >> qexists_tac `env` >>
        fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
     fs[reason_uniform_shape_def] >>
     qpat_x_assum `!sa vv sb. compile_expr _ _ _ _ = _ ==> _` drule >>
     simp[reason_result_shape_def]) >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once well_typed_expr_def] >>
     strip_tac >> gvs[subscript_type_ok_def]
     >>~- ([`is_int_type (expr_type idx)`], Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
         rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[vyperTypeSystemTheory.is_int_type_def, compileEnvTheory.is_word_type_def]) >>
     drule type_place_expr_vtype_annotation >> simp[] >> strip_tac >>
     Cases_on `vt` >> gvs[vtype_annotation_ok_def, subscript_vtype_def] >>
     Cases_on `expr_type idx` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
         rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
         gvs[vyperTypeSystemTheory.is_int_type_def, compileEnvTheory.is_word_type_def]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >>
     impl_tac
     >- (conj_tac >- fs[expr_body_pre_def] >>
         metis_tac[expr_body_pre_var_types_well_formed]) >> simp[]) >>
  `fn_has_code st2 sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  Cases_on `tv` >- suspend "value_suffix" >- suspend "place_suffix" >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac exprSimSourceTheory.expr_body_pre_runtime_typed) >>
  simp[vyperTypeInvariantsTheory.eval_result_typed_def] >> metis_tac[]
QED
Resume compile_subscript_array_live_base_case[value_suffix]:
  rename1 `Value a` >>
  `p.ptr_location = LocMemory` by
    (fs[subscript_base_live_after_def] >>
     qpat_x_assum `!ty st. vv_location _ = _` (qspecl_then [`ty`,`sa`] mp_tac) >>
     simp[contextTheory.vv_location_def]) >>
  gvs[contextTheory.vv_operand_def, vv_post_final_gas, expr_post_initial_gas] >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac live_memory_value_array_suffix_summary) >>
  simp[NoAsms, exprSimPropsTheory.vv_post_initial_gas, vv_post_final_gas,
       expr_post_initial_gas, contextTheory.vv_operand_def] >>
  disch_then irule >>
  simp[SF SFY_ss, vv_post_final_gas, expr_post_initial_gas] >>
  conj_tac >- gvs[subscript_base_live_after_def] >>
  qexistsl_tac [`iop`,`p`,`sm`,`st2`,`t`] >>
  simp[vv_post_final_gas, expr_post_initial_gas]
QED
Resume compile_subscript_array_live_base_case[place_suffix]:
  rename1 `PlaceR pl` >> Cases_on `pl`
  >- suspend "storage_suffix"
  >- suspend "memory_suffix" >>
  suspend "immutable_suffix"
QED
Resume compile_subscript_array_live_base_case[memory_suffix]:
  gvs[contextTheory.vv_operand_def, vv_post_final_gas, expr_post_initial_gas] >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac live_memory_array_suffix_summary) >>
  simp[NoAsms, exprSimPropsTheory.vv_post_initial_gas, vv_post_final_gas,
       expr_post_initial_gas, contextTheory.vv_operand_def] >>
  disch_then irule >>
  simp[SF SFY_ss, vv_post_final_gas, expr_post_initial_gas, contextTheory.vv_operand_def] >>
  conj_tac >- gvs[subscript_base_live_after_def] >>
  qexistsl_tac [`iop`,`sm`,`st2`,`t`] >>
  simp[vv_post_final_gas, expr_post_initial_gas]
QED
Resume compile_subscript_array_live_base_case[immutable_suffix]:
  gvs[contextTheory.vv_operand_def, vv_post_final_gas, expr_post_initial_gas] >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac live_immutable_array_suffix_summary) >>
  simp[NoAsms, exprSimPropsTheory.vv_post_initial_gas, vv_post_final_gas,
       expr_post_initial_gas, contextTheory.vv_operand_def] >>
  disch_then irule >>
  simp[SF SFY_ss, vv_post_final_gas, expr_post_initial_gas, contextTheory.vv_operand_def] >>
  conj_tac >- gvs[subscript_base_live_after_def] >>
  qexistsl_tac [`iop`,`sm`,`st2`,`t`] >>
  simp[vv_post_final_gas, expr_post_initial_gas]
QED
Resume compile_subscript_array_live_base_case[storage_suffix]:
  rename1 `StoragePlace tr slot vt` >>
  qpat_assum `eval_expr cx obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac exprSimSourceTheory.expr_body_pre_runtime_typed) >>
  simp[vyperTypeInvariantsTheory.eval_result_typed_def,
       vyperTypeInvariantsTheory.runtime_place_typed_def,
       vyperStateTheory.place_type_value_def, vyperStateTheory.return_def] >>
  disch_then drule >> strip_tac >>
  `env.type_defs = get_tenv cx` by fs[expr_body_pre_def, expr_sim_inv_def,
      vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[contextTheory.vv_location_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  qpat_assum `eval_expr cx idx _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac exprSimSourceTheory.expr_body_pre_runtime_typed) >>
  simp[NoAsms] >> disch_then drule >> strip_tac >>
  `?itv. evaluate_type (get_tenv cx) (expr_type idx) = SOME itv /\
         value_has_type itv v` by metis_tac[] >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `ann = et` by
    (fs[expr_body_pre_def] >>
     qpat_x_assum `well_typed_expr env (Subscript ann obj idx)` mp_tac >>
     qpat_x_assum `expr_type obj = ArrayT et bd` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[vyperTypeSystemTheory.well_typed_expr_def, vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def] >>
     strip_tac >>
     qpat_x_assum `ArrayT _ _ = _` (SUBST_ALL_TAC o SYM) >>
     fs[vyperTypeSystemTheory.subscript_vtype_def]) >>
  `p.ptr_location = slot_loc tr` by fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_place_ptr_def] >>
  gvs[subscript_base_live_after_def, contextTheory.vv_operand_def,
      vv_post_final_gas, expr_post_initial_gas] >>
  `type_memory_bytes cenv ann = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `elem_size_in_location cenv (slot_loc tr) ann = type_slot_size tv /\
   word_scale (slot_loc tr) = 1` by
    (Cases_on `tr` >> simp[loweringPostsTheory.slot_loc_def, compileEnvTheory.elem_size_in_location_def,
       compileEnvTheory.word_scale_def, compileEnvTheory.is_slot_addressed_def,
       exprSimFieldLayoutTheory.slot_count_of_memory_size]) >>
  irule live_storage_array_suffix_summary >>
  simp[SF SFY_ss, vyperValueTheory.evaluate_type_def] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule exprSimPopStorageTheory.pop_array_length_bound >> simp[]) >>
  conj_tac >- fs[vyperTypingTheory.well_formed_type_value_def] >>
  qexistsl_tac [`env`,`iop`,`p`,`sm`,`st2`,`es_end`,`t`] >>
  gvs[] >>
  Cases_on `is_signed_type (expr_type idx)` >>
  simp[integer_wordTheory.i2w_w2i, integer_wordTheory.i2w_w2n]
QED
Finalise compile_subscript_array_live_base_case

(* compile_subscript_array_unframed_base_case with the base not live at
   the index's end: a popped local's snapshot, a dead storage slot, a
   popped constructor immutable (a value outside memory), or a value in a local's region holding a
   dynamic array when the index pops a local.
   An array subscript whose index does not overlap its base, outside
   compile_subscript_array_framed_base_case: a base in storage or
   transient storage, an immutable in the constructor, a dynamic array or one with a dynamic
   array inside it in memory, a base whose source result is a storage
   place, or an index that changes the locals or the immutables.  ADMITTED (cheat).  NOT DERIVABLE from these hypotheses,
   though no miscompile is known: vv_post does not tie the base's pointer
   to its source place.  vv_at and local_val_at pick the local's path by
   its type alone, immutable_holds' constructor form takes any offset of
   the staged buffer that holds the value, and storage_holds pins the slot
   only by what it reads; so the base's pointer may lie in dead bytes that
   hold an equal value (past a dynamic array's length, in the staged
   buffer, in dead slots), which nothing keeps across the index's
   fragment: state_rel and immutables_rel relate only the live parts,
   locals_kept exempts every dynamic array's length word, and expr_post
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
   The vv_place_ptr conjunct of vv_post (loweringPosts) replaces most of
   this lemma.
   Its producers are the expressions whose source result can be a place:
   Name, TopLevelName, Subscript (array, tuple, mapping), Attribute, Pop,
   and IfExp (conditional_result keeps a memory aggregate's place, and the
   PHI carries the arm's pointer).  With it, and the base live at the
   index's end, the rest goes through but for popped snapshots, dead
   storage slots and the constructor immutable above. *)
Theorem compile_subscript_array_stale_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    ~((!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) /\
    ~(!s env tv t gs ir t'.
       expr_body_pre cenv cx env (Subscript ann obj idx) s /\
       eval_expr cx obj s = (INL tv, t) /\
       eval_expr cx idx (t with gas_obs := gs) = (INL ir, t') ==>
       subscript_base_live_after cenv cx obj et bd tv t t') ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An array subscript whose index does not overlap its base, outside
   compile_subscript_array_framed_base_case, by whether the base is still
   live at the index's end. *)
Theorem compile_subscript_array_unframed_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (~nocalls ==> post_value_type cenv obj = expr_type obj) /\
    ~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
    ~((!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  Cases_on `(!s env tv t gs ir t'.
               expr_body_pre cenv cx env (Subscript ann obj idx) s /\
               eval_expr cx obj s = (INL tv, t) /\
               eval_expr cx idx (t with gas_obs := gs) = (INL ir, t') ==>
               subscript_base_live_after cenv cx obj et bd tv t t')`
  >- (qspecl_then [`nocalls`, `ctx`, `func`, `cenv`, `cx`, `ann`, `obj`, `idx`,
                   `et`, `bd`] match_mp_tac compile_subscript_array_live_base_case >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`nocalls`, `ctx`, `func`, `cenv`, `cx`, `ann`, `obj`, `idx`,
               `et`, `bd`] match_mp_tac compile_subscript_array_stale_base_case >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Every other array subscript, by whether its index overlaps its base:
   compile_subscript_array_copied_base_case if it does,
   compile_subscript_array_unframed_base_case if not. *)
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
  rpt strip_tac >>
  Cases_on `subscript_reads_base cx obj idx <=> copies_subscript_base cenv obj idx`
  >- suspend "agree" >>
  simp[expr_vv_case_def] >> rpt strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_then (qspecl_then [`obj`, `idx`] assume_tac)
    expr_sim_inv_reads_base_copies >>
  fs[]
QED
Resume compile_subscript_array_place_base_case[agree]:
  Cases_on `copies_subscript_base cenv obj idx`
  >- (irule compile_subscript_array_copied_base_case >> rpt conj_tac
      >~ [`read_result`]
      >- (rpt strip_tac >>
          qpat_x_assum `!s tv t s' tv' t'. _`
            (qspecl_then [`s`, `tv`, `t`, `s'`, `Value v`, `t'`] mp_tac) >>
          fs[vyperStateTheory.bind_def, vyperStateTheory.return_def])
      >~ [`ValPT`] >- (qexistsl [`bd`, `et`] >> fs[]) >>
      fs[]) >>
  `~subscript_reads_base cx obj idx` by fs[] >>
  `!s tv t. eval_expr cx obj s = (INL tv, t) ==>
            expr_sim_case nocalls ctx func cenv cx idx` by
    (rpt strip_tac >>
     qpat_x_assum `!s tv t s' tv' t'. _`
       (qspecl_then [`s`, `tv`, `t`, `t`, `tv`, `t`] mp_tac) >>
     fs[vyperStateTheory.return_def]) >>
  qpat_x_assum `!s tv t s' tv' t'. _` kall_tac >>
  irule compile_subscript_array_unframed_base_case >> asm_rewrite_tac[] >>
  qexistsl [`bd`, `et`] >> qpat_x_assum `~(_ /\ _)` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[]
QED
Finalise compile_subscript_array_place_base_case

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
  irule compile_subscript_array_place_base_case >> asm_rewrite_tac[] >>
  qexistsl [`bd`, `et`] >> asm_rewrite_tac[]
QED
