(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: an element of a
 * runtime immutable array whose index frames the base.
 *
 * TOP-LEVEL:
 *   subscript_array_framed_code_ptr
 *)
Theory bodyPtrSubscriptSeamArrayCode
Ancestors
  bodyPtrSubscriptSeamArrayCodeGas
  bodyPtrSubscriptSeamArrayCodeCompose bodyPtrSubscriptSeamArrayCodeSummary
  bodyPtrSubscriptSeamArrayCodeFrame exprSimSubscriptArrayEndpoint
  exprSimSubscriptArrayOrigin exprSimSubscriptArrayCompose
  gasSummaryComposePtr exprOperandVar exprSimSubscriptArraySource
  exprSimSubscriptArrayFramed exprSimHyps fragGasPathPtr exprSimSource
  bodyPtrSubscriptRejectedSelector bodyPtrSubscriptSignedBounds
  bodyPtrSubscriptCountedAdd
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts context
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* The code half of the pointer twin of S1's
   compile_subscript_array_framed_base_case (exprSimSubscriptArray): an
   array lowered to a code pointer outside the constructor (a runtime
   immutable, in the data section), laid out at its own type, whose source
   result is no storage place, and whose index leaves the source locals and
   immutables as they were.  compile_subscript lowers the base, then the
   index (lower_value at ty), then compile_array_subscript: for a dynamic
   array the length through compile_ptr_load's compile_imm_load_word (DLOAD
   at runtime), the bounds check, and the element address.  immutables_rel
   relates the data section to the unchanged source immutables, so the
   base's place reads at the index's end what it read before.  ptr_vv_ok
   asks of a code pointer an untainted operand with no provenance
   (op_prov G p.ptr_operand = NONE), which the base's ptr_vv_ok gives for
   the base's operand and ghost_kept keeps across the index; out_prov of
   ADD takes its first operand's provenance and MUL's is none.  For a
   dynamic array the bounds check compares the index with a freshly loaded
   length variable (LT [idx; len]), so access_ok's two-variable comparison
   clause needs the index's provenance to be none, which a word index's
   ptr_val_ok gives.
   Hints: the S1 proof is exprSimSubscriptArrayFramed and the
   exprSimSubscriptArray{Compose,Suffix,Source,Frame,Endpoint,Origin}
   theories in this tree; the lane helpers bodyPtrSubscriptBoundsRun,
   bodyPtrSubscriptSignedBounds, bodyPtrSubscriptRejectedSelector and
   bodyPtrSubscriptCountedAdd have the counted bounds check, its abort and
   the address arithmetic. *)
Theorem subscript_array_framed_code_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es et bd.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
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
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty e1 es` by
    (fs[body_expr_ptr_ok_def] >> metis_tac[]) >>
  simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty e1 sa = (bvv,sm)` >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  `gas_admissible (eval_expr cx e1) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[exprLoweringPropsTheory.ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by
    (irule compileEnvTheory.cs_extends_trans >> qexists `st2` >> simp[]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_ptr_at_marked])
      >- suspend "base_normal"
      >> suspend "base_exit") >>
  suspend "base_exempt"
QED

Resume subscript_array_framed_code_ptr[base_exit]:
  Cases_on `res` >- fs[] >> rename1 `INR exc` >>
  qexists `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl [`INR exc`,`es_end`,`G`,`tn`,`r`] >> simp[] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> first_assum ACCEPT_TAC) >> fs[]
QED

Resume subscript_array_framed_code_ptr[base_exempt]:
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >> first_assum ACCEPT_TAC
QED

Resume subscript_array_framed_code_ptr[base_normal]:
  qpat_x_assum `(\res ee G tn t. _) _ _ _ _ _`
    (strip_assume_tac o BETA_RULE) >> gnvs[] >>
  pure_rewrite_tac[GSYM gas_outcome_ptr_def] >>
  irule code_array_after_base_ptr >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL tv,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre cenv cx env e2 (es_end with gas_obs := [])` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists `ann` >> simp[]) >>
  `body_expr_ptr_ok cx e2` by metis_tac[] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e2 (es_end with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok cx e2` mp_tac >>
     simp[body_expr_ptr_ok_def] >> strip_tac >>
     first_x_assum (irule o cj 1) >> metis_tac[]) >>
  qexists `d` >> conj_tac >- suspend "base_suffix" >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_ptr_exec, gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `fn_has_code sm st2 func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `stmt_state_rel ctx func cenv cx es_end t` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_post_def]) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_gas_obs, exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- gvs[loweringStateRelDefsTheory.not_fresh_at_def]
  >- gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
  simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e2 (es_end with gas_obs := gs)` by fs[] >>
  drule_all (REWRITE_RULE [ETA_THM] expr_body_pre_res_ok) >> simp[]
QED

Resume subscript_array_framed_code_ptr[base_suffix]:
  rpt gen_tac >> strip_tac >>
  `vyperState$bind (eval_expr cx e2) (read_result cx)
    (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
    (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ imarks _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `?ir. eval_expr cx e2
      (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
    read_result cx ir (raw with gas_obs := []) = (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >> metis_tac[]) >>
  `eval_expr cx e1
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
      gas_explicit imarks t.vs_gas_readings) =
    (INL tv,es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ marks _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_ptr_def] >>
     disch_then (qspec_then `gas_explicit imarks t.vs_gas_readings` mp_tac o CONJUNCT1) >> simp[]) >>
  `raw.scopes = es_end.scopes /\ raw.immutables = es_end.immutables` by
    (qpat_x_assum `!t r t'. eval_expr cx e2 t = _ ==> _` drule >> simp[]) >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_ptr_exec, gasSummaryTheory.gas_marked_exec_def,
      fragGasModeTheory.gas_marked_path_exec, fragGasPathTheory.gas_path_normal] >>
  `vv_location bvv = SOME LocCode` by metis_tac[pairTheory.FST] >>
  `?p. bvv = LocatedValue (ArrayT et bd) p /\ p.ptr_location = LocCode` by
    (Cases_on `bvv` >> gvs[contextTheory.vv_location_def] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [vv_post_def]) >>
     simp[vv_holds_def, compileEnvTheory.is_bytestring_type_def]) >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  suspend "suffix_frame"
QED

Resume subscript_array_framed_code_ptr[suffix_frame]:
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `expr_body_pre cenv cx env e2
    (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by simp[] >>
  `expr_sim_inv cenv cx env es_end` by fs[expr_body_pre_def] >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `eval_expr cx e1 _ = _`
       (mp_then Any mp_tac
         vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule compile_array_pointer_not_label >> disch_then irule >> simp[] >>
     qexists `env` >> fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` by metis_tac[] >>
  suspend "suffix_typed"
QED

Resume subscript_array_framed_code_ptr[suffix_typed]:
  `?itv. evaluate_type (get_tenv cx) (expr_type e2) = SOME itv /\
    value_has_type itv v` by
    (drule_all expr_body_pre_runtime_typed >> strip_tac >> metis_tac[]) >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type e2)` by
    (qpat_x_assum `value_has_type itv v` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type e2) = _` mp_tac >>
     qpat_x_assum `v = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type e2` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
       vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >>
     impl_tac >- (conj_tac >- fs[expr_body_pre_def] >>
       metis_tac[expr_body_pre_var_types_well_formed]) >> simp[]) >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
       vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  gvs[] >> suspend "suffix_endpoint"
QED

Resume subscript_array_framed_code_ptr[suffix_endpoint]:
  `stmt_state_rel ctx func cenv cx (raw with gas_obs := []) u` by fs[expr_post_def] >>
  `vv_post ctx func cenv cx e1 es sa st2 s0 (raw with gas_obs := []) tv
    (LocatedValue (ArrayT ann bd) p) u` by
    (irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists `env` >> simp[]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ sa st2 _ _ _ _ _`)
    code_array_marked_post_view >>
  disch_then (qspecl_then [`es_end with gas_obs := []`,
    `gas_explicit marks s0.vs_gas_readings`,`env`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "suffix_ghost"
QED

Resume subscript_array_framed_code_ptr[suffix_ghost]:
  `op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE` by
    gvs[ptr_vv_ok_def] >>
  `op_taint tni p.ptr_operand = op_taint tn p.ptr_operand` by
    (qpat_assum `ghost_kept _ _ sm G tn t Gi tni`
      (mp_then Any mp_tac bodyPtrPrecompileBuiltinsGhostTheory.ghost_kept_operand_taint) >>
     disch_then (qspec_then `p.ptr_operand` mp_tac) >> simp[]) >>
  `op_prov Gi p.ptr_operand = op_prov G p.ptr_operand` by
    (qpat_assum `ghost_kept _ _ sm G tn t Gi tni`
      (mp_then Any mp_tac bodyPtrBopInWordBoundaryTheory.ghost_kept_operand_prov) >>
     disch_then (qspec_then `p.ptr_operand` mp_tac) >> simp[]) >>
  `op_taint tni iop = {} /\ op_prov Gi iop = NONE` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >> simp[ptr_val_ok_def]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gi tni` by
    (irule wordOperandsPtrTheory.ghost_kept_trans >> simp[] >>
     conj_tac
     >- (qexists `func` >>
         fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
     qexistsl [`G`,`es_end with gas_obs := []`,`t`,`sm`,`tn`] >> simp[] >>
     fs[vv_post_def, loweringPostsTheory.wb_frame_def] >> metis_tac[]) >>
  suspend "suffix_finish"
QED

Resume subscript_array_framed_code_ptr[suffix_finish]:
  `cs_extends st2 sb /\ st2.cs_next_var <= sb.cs_next_var /\ st2.cs_next_id <= sb.cs_next_id` by
    (`ci_mono st2 sb` suffices_by simp[exprLoweringPropsTheory.ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `!q. (!x. not_fresh_at st2 x ==> lookup_var x q = lookup_var x u) /\
    q.vs_allocas = u.vs_allocas /\ q.vs_memory = u.vs_memory /\
    stmt_state_rel ctx func cenv cx (raw with gas_obs := []) q ==>
    vv_post ctx func cenv cx e1 es sa sb s0 (raw with gas_obs := []) tv
      (LocatedValue (ArrayT ann bd) p) q` by
    (rpt strip_tac >>
     qpat_x_assum `vv_post _ _ _ _ _ _ sa st2 _ _ _ _ _` kall_tac >>
     irule framed_array_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists `env` >> simp[]) >>
  `type_memory_bytes cenv ann = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >> qexistsl [`env`,`es`] >> fs[expr_body_pre_def]) >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  simp[contextTheory.mk_ptr_def] >>
  irule (SIMP_RULE (srw_ss()) [contextTheory.mk_ptr_def]
    code_array_marked_suffix_ptr_summary) >> simp[] >>
  conj_tac
  >- (qexistsl [`gas_explicit marks s0.vs_gas_readings`,`es_end with gas_obs := []`] >> simp[]) >>
  conj_tac >- (qexists `env` >> simp[]) >>
  qexistsl [`iop`,`p`,`st2`,`w`] >>
  simp[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
    compileEnvTheory.is_slot_addressed_def] >>
  rpt conj_tac
  >- gvs[loweringStateRelDefsTheory.not_fresh_at_def]
  >- gvs[loweringStateRelDefsTheory.not_fresh_at_def]
  >- (rpt strip_tac >> gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) 
  >- (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      simp[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
        compileEnvTheory.is_slot_addressed_def]) >>
  metis_tac[fragExecTheory.fn_has_code_split]
QED
Finalise subscript_array_framed_code_ptr
