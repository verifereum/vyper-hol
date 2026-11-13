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
 *     itself split on subscript_base_live_after into two admitted leaves:
 *     compile_subscript_array_live_base_case and
 *     compile_subscript_array_stale_base_case.
 *)

Theory exprSimSubscriptArray
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimSubscriptArrayFramed exprSimSubscriptArrayCompose
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph
  exprSimCopiedPrefix exprSimCopiedCompile exprSimCopiedCompose
  exprSimCopiedAlloc exprSimCopiedSnapshot exprSimCopiedFrame exprSimCopiedSuffix

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
   leaves as it is.  ADMITTED (cheat). *)
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
  cheat
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
Finalise compile_subscript_array_copied_base_case

(* The base's source result still reads at the index's end: a local's
   path, a storage place's slots (live and in range), or a runtime
   immutable's path still evaluate there; a value needs the locals kept,
   or a static array with no dynamic array inside it. *)
Definition subscript_base_live_after_def:
  (subscript_base_live_after cx (et:type) (bd:bound) (PlaceR (MemoryPlace id path)) t t' <=>
     !entry. lookup_scopes id t'.scopes = SOME entry ==>
             ?v. evaluate_subscripts entry.type entry.value path = INL v) /\
  (subscript_base_live_after cx et bd (PlaceR (StoragePlace tr slot vt)) t t' <=>
     storage_read_live cx tr (get_storage cx t' tr) slot vt /\
     slots_in_range (get_storage cx t' tr) (w2n slot) vt) /\
  (subscript_base_live_after cx et bd (PlaceR (ImmutablePlace src id path)) t t' <=>
     !itv iv.
       FLOOKUP (case ALOOKUP t'.immutables cx.txn.target of
                  NONE => FEMPTY
                | SOME imms => get_source_immutables src imms) id = SOME (itv, iv) ==>
       ?v. evaluate_subscripts itv iv path = INL v) /\
  (subscript_base_live_after cx et bd (HashMapRef _ _ _ _) t t' <=> T) /\
  (subscript_base_live_after cx et bd (Value _) t t' <=>
     t'.scopes = t.scopes \/
     (?n. bd = Fixed n /\
          !etv. evaluate_type (get_tenv cx) et = SOME etv ==> dynarray_free etv))
End

(* compile_subscript_array_unframed_base_case with the base live at the
   index's end (subscript_base_live_after): vv_place_ptr ties the base's
   pointer to its source place, and the live place reads the same value
   after the index's fragment.  ADMITTED (cheat). *)
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
       subscript_base_live_after cx et bd tv t t') ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* compile_subscript_array_unframed_base_case with the base not live at
   the index's end: a popped local's snapshot, a dead storage slot, a
   popped constructor immutable, or a value in a local's region holding a
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
       subscript_base_live_after cx et bd tv t t') ==>
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
               subscript_base_live_after cx et bd tv t t')`
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
