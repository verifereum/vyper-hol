(* Counted sequencing for framed array bases, conditional on the represented tail. *)
Theory bodyMemSubscriptArrayFramedCompose
Ancestors
  exprSimMemDefs exprSimSubscriptArray exprSimSubscriptMap exprSimHypsDefs exprSimSource
  exprSimSubscriptArraySuffix exprSimSubscriptArrayEndpoint
  exprSimSubscriptArraySource exprSimHyps exprSimUnwrap exprOperandVar
  exprWordOperand exprLoweringProps gasOutcome gasSummary gasContext
  gasSummaryCompose fragGasMode fragGasPath gasExemptCert
  loweringPosts context compileEnv vyperState vyperAST vyperTypeSystem
  vyperEvalExprPreservesScopesDom exprSimSubscriptArrayFramed fragExec exprSimDefs

Theorem compile_subscript_array_framed_base_mem_case_from_suffix:
  (!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0
    etv av w iw i lt eb tb.
  ((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  local_ptrs_reserved cenv sc /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee s /\
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee r
    (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee r
         (LocatedValue (ArrayT et bd) p) q) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  vv_store_bound cx (ArrayT et bd) lt eb r (LocatedValue (ArrayT et bd) p) tb /\
  read_result cx r eb = (INL (ArrayV av),eb) /\
  eval_operand p.ptr_operand tb = SOME w /\ tb.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      vv_store_bound cx ann ann ee' child (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next)
    (\res ee' out. expr_exit res out)) ==>
  !ctx func cenv cx ann obj idx et bd.
    (!env ty es. expr_body_pre cenv cx env obj es ==>
                 expr_vv_sim_mem ctx func cenv cx ty obj es) /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              !env ty es. expr_body_pre cenv cx env idx es ==>
                          expr_sim_mem ctx func cenv cx ty idx es) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    post_value_type cenv obj = expr_type obj /\
    (~subscript_reads_base cx obj idx /\ ~copies_subscript_base cenv obj idx /\
      (!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) ==>
    !env ty es. expr_body_pre cenv cx env (Subscript ann obj idx) es ==>
                expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  `expr_vv_sim_mem ctx func cenv cx ty obj es` by metis_tac[] >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule compile_expr_extends >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `ci_mono st2 sb` by
    (mp_tac ci_mono_compile_array_subscript >>
     disch_then (qspecl_then
       [`vv_operand bvv`,`iop`,
        `case bd of Fixed _ => F | Dynamic _ => T`,
        `case bd of Fixed n => n | Dynamic _ => 0`,
        `word_scale loc`,`elem_size_in_location cenv loc et`,
        `is_signed_type (expr_type idx)`,
        `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc`,`st2`] mp_tac) >>
     simp[ci_mono_compile_ptr_load, ci_mono_def]) >>
  qpat_x_assum `ci_mono st2 sb`
    (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `cs_extends sm sb` by
    (irule cs_extends_trans >> qexists_tac `st2` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`sm`,`bvv`,`s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `expr_exit res r` mp_tac >>
      Cases_on `res` >> simp[expr_exit_def]) >>
  reverse conj_tac >- (rpt gen_tac >> strip_tac >> simp[]) >>
  suspend "base_normal"
QED

Resume compile_subscript_array_framed_base_mem_case_from_suffix[base_normal]:
  rpt gen_tac >> strip_tac >>
  `eval_expr cx obj (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre cenv cx env idx (mid with gas_obs := [])` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty idx (mid with gas_obs := [])` by metis_tac[] >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code sm st2 func /\ fn_has_code st2 sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok
     (mid with gas_obs := [])` by
    (qpat_assum `~subscript_reads_base _ _ _`
       (irule o MATCH_MP subscript_result_index_admissible) >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     qexists_tac `expr_vv_res_ok` >> simp[subscript_result_predicates_exceptions] >>
     qexists_tac `ann` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ idx _` (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sm`,`st2`,`iop`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule forced_then_outcome_exec >>
  (conj_tac >-
    (rpt gen_tac >> Cases_on `ex` >> Cases_on `r` >> simp[expr_exit_def] >>
     rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def])) >>
  qexists_tac `\iv ee u.
    expr_post ctx func cenv cx idx (mid with gas_obs := []) sm st2 t ee iv iop u /\
    expr_store_bound cx (expr_type idx) iv iop u /\
    u.vs_current_bb = st2.cs_current_bb /\ u.vs_inst_idx = LENGTH st2.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next` >>
  simp[] >> suspend "index_normal"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[index_normal]:
  rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx idx) (read_result cx)
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL v', mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `?ir. eval_expr cx idx
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings) =
     (INL ir, mid' with gas_obs := []) /\
     read_result cx ir (mid' with gas_obs := []) = (INL v',mid' with gas_obs := [])` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac read_result_state >> simp[]) >>
  `eval_expr cx obj
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                         gas_explicit marks' t.vs_gas_readings) =
     (INL v, mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit marks' t.vs_gas_readings` mp_tac o CONJUNCT1) >> simp[]) >>
  `mid'.scopes = mid.scopes /\ mid'.immutables = mid.immutables` by
    (qpat_x_assum `!t r t'. eval_expr cx idx t = _ ==> _` drule >> simp[]) >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` kall_tac >>
  qpat_x_assum `bind _ _ _ = _` kall_tac >>
  `?p. bvv = LocatedValue (ArrayT et bd) p` by
    (`vv_location bvv = SOME LocCode \/ vv_location bvv = SOME LocMemory` by
       metis_tac[pairTheory.FST] >>
     Cases_on `bvv` >> fs[vv_location_def] >>
     qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def, is_bytestring_type_def] >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `bvv = _` SUBST_ALL_TAC >>
  suspend "pointer_setup"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[pointer_setup]:
  qpat_x_assum `loc = _` (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) [vv_location_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_expr cenv ty obj sa = _`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[vv_operand_def]) >>
  `local_ptrs_reserved cenv st2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (drule compile_lower_value_var >> simp[]) >>
  Q.SUBGOAL_THEN
  `((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
    ?n. bd = Fixed n) /\
   ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
    ((?n. bd = Fixed n) /\
     (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
     p.ptr_location = LocMemory))` assume_tac
  >-
    (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` kall_tac >>
     qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `!ty st. vv_location _ = _`
       (qspecl_then [`ty`,`sa`] assume_tac) >>
     gvs[vv_location_def] >> disj1_tac >> qexists_tac `ty` >> simp[vv_location_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule exprSimSubscriptArrayOriginTheory.compile_array_pointer_not_label >>
     disch_then irule >> simp[] >>
     (conj_tac >- (qpat_assum `(_ \/ _) /\ _` (mp_tac o CONJUNCT2) >>
                    rpt (pop_assum kall_tac) >> metis_tac[])) >> qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env idx
     (mid with gas_obs := gas_explicit marks' t.vs_gas_readings)` by fs[] >>
  qpat_assum `eval_expr cx idx _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac expr_body_pre_runtime_typed) >>
  disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `value_has_type tvt v'` by simp[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt v'` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_x_assum `v' = IntV i` SUBST1_TAC >>
     rpt (pop_assum kall_tac) >> Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, is_word_type_def]) >>
  `!l. iop <> Label l` by
    (drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >> simp[] >>
     (impl_tac >- (conj_tac >- fs[expr_body_pre_def] >>
                    drule expr_body_pre_var_types_well_formed >> simp[])) >> simp[]) >>
  suspend "endpoint"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[endpoint]:
  markerLib.RESUME_TAC >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by fs[expr_body_pre_def] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = (INL v, mid with gas_obs := [])`
      (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by fs[expr_post_def] >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa st2 s0
     (mid' with gas_obs := []) v (LocatedValue (ArrayT et bd) p) t'` by
    (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` kall_tac >>
     irule framed_array_base_endpoint >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     qexistsl_tac [`env`,`iop`,`v'`,`sm`,`st2`,`mid with gas_obs := []`,`t`,`t'`] >>
     simp[] >> metis_tac[]) >>
  suspend "represented_view"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[represented_view]:
  markerLib.RESUME_TAC >>
  `!tr slot vt. v <> PlaceR (StoragePlace tr slot vt)` by
    (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` kall_tac >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `eval_expr cx obj e0 = (INL v,em)` >>
  `expr_body_pre cenv cx env obj e0 /\
   expr_body_pre cenv cx env (Subscript ann obj idx) e0` by simp[Abbr `e0`] >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) e0 sa st2 s0
     (mid' with gas_obs := []) v (LocatedValue (ArrayT et bd) p) t'` by
    simp[Abbr `e0`, exprSimPropsTheory.vv_post_initial_gas] >>
  qpat_assum `vv_post _ _ _ _ (Subscript _ _ _) e0 _ _ _ _ _ _ _`
    (mp_then Any (qspecl_then [`em`,`env`] mp_tac) framed_array_post_view) >>
  (impl_tac >- (simp[Abbr `em`] >>
     qpat_assum `(_ \/ _) /\ _` (mp_tac o CONJUNCT2) >>
     rpt (pop_assum kall_tac) >> metis_tac[])) >> strip_tac >>
  suspend "suffix_preparation"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[suffix_preparation]:
  markerLib.RESUME_TAC >>
  `!q. (!x z. not_fresh_at st2 x /\ lookup_var x t' = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP t'.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = t'.vs_memory /\
       stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) q ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) e0 sa sb s0
         (mid' with gas_obs := []) v (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >> simp[Abbr `e0`, exprSimPropsTheory.vv_post_initial_gas] >>
     irule framed_array_base_endpoint >> simp[] >>
     qexistsl_tac [`env`,`iop`,`v'`,`sm`,`st2`,`mid with gas_obs := []`,`t`,`t'`] >>
     simp[] >> metis_tac[]) >>
  `read_result cx v (mid with gas_obs := []) =
     (INL (ArrayV av),mid with gas_obs := [])` by
    (`FST (read_result cx v (mid' with gas_obs := [])) =
      FST (read_result cx v (mid with gas_obs := []))` by
       (irule read_result_nonstorage_frame >> simp[]) >>
     Cases_on `read_result cx v (mid with gas_obs := [])` >>
     qpat_assum `read_result cx v (mid with gas_obs := []) = _`
       (mp_then Any mp_tac read_result_state) >>
     qpat_x_assum `FST (read_result cx v _) = _` mp_tac >> simp[] >>
     rpt strip_tac >> simp[]) >>
  `?w0. eval_operand p.ptr_operand t = SOME w0` by
    (qpat_x_assum `vv_post _ _ _ _ obj _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def, vyperASTTheory.expr_type_def] >>
     rpt strip_tac >> metis_tac[]) >>
  `eval_operand p.ptr_operand t' = SOME w0` by
    (irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`sm`,`t`] >> simp[] >>
     qpat_x_assum `expr_post _ _ _ _ idx _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `w0 = w` by metis_tac[optionTheory.SOME_11] >>
  suspend "suffix_application"
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[suffix_application]:
  markerLib.RESUME_TAC >> (
  `!x. p.ptr_operand = Var x ==> not_fresh_at st2 x` by
    (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` kall_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  SUBGOAL_THEN
    ``?en. expr_body_pre cenv cx en obj e0 /\
           expr_body_pre cenv cx en (Subscript ann obj idx) e0`` (mk_asm "suffix_env")
  >- (qexists_tac `env` >> simp[]) >>
  SUBGOAL_THEN
    ``?eb lt tb. tb.vs_alloca_next <= t'.vs_alloca_next /\
       eval_operand p.ptr_operand tb = SOME w /\
       array_length (ArrayTV etv bd) av < dimword (:256) /\
       read_result cx v eb = (INL (ArrayV av),eb) /\
       val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
       vv_store_bound cx (ArrayT et bd) lt eb v (LocatedValue (ArrayT et bd) p) tb`` (mk_asm "suffix_old")
  >- (qexistsl_tac [`mid with gas_obs := []`,`lowered_value_type cenv obj`,`t`] >> simp[]) >>
  suspend "suffix_ready")
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[suffix_ready]:
  markerLib.RESUME_TAC >> (
  SUBGOAL_THEN
    ``?op iw' sc.
       i = (if is_signed_type (expr_type idx) then w2i iw' else &w2n iw') /\
       (!l. op <> Label l) /\ (!x. op = Var x ==> not_fresh_at sc x) /\
       (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
       (!q. (!x z. not_fresh_at sc x /\ lookup_var x t' = SOME z ==> lookup_var x q = SOME z) /\
            (!aid a. FLOOKUP t'.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
            q.vs_memory = t'.vs_memory /\ stmt_state_rel ctx func cenv cx mid' q ==>
            vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) e0 sa sb s0
              (mid' with gas_obs := []) v (LocatedValue (ArrayT et bd) p) q) /\
       st2.cs_current_bb = sc.cs_current_bb /\
       LENGTH st2.cs_current_insts = LENGTH sc.cs_current_insts /\ eval_operand op t' = SOME iw' /\
       compile_array_subscript p.ptr_operand op
         (case bd of Fixed n => F | Dynamic n => T) (case bd of Fixed n => n | Dynamic n => 0)
         (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
         (is_signed_type (expr_type idx))
         (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sb) /\
       local_ptrs_reserved cenv sc /\ fn_has_code sc sb func /\
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) e0 sa sc s0
         (mid' with gas_obs := []) v (LocatedValue (ArrayT et bd) p) t'`` (mk_asm "suffix_comp")
  >- (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` kall_tac >>
      qexistsl_tac [`iop`,`iw`,`st2`] >> gvs[vv_operand_def]) >>
  suspend "suffix_summary")
QED
Resume compile_subscript_array_framed_base_mem_case_from_suffix[suffix_summary]:
  markerLib.RESUME_TAC >>
  `gas_summary_at T (ctx,func) []
    (select_result cx (ArrayT et bd) v (ValueSubscript (IntV i)))
    (mid' with gas_obs := [],t')
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) e0 sa sb s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      vv_store_bound cx ann ann ee' child (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func q /\ t'.vs_alloca_next <= q.vs_alloca_next)
    (\res ee' out. expr_exit res out)` by
    (qpat_x_assum `!cenv ty obj sa bd cx env ann idx es et r t ee p sc iop dst sd func s ctx s0 etv av w iw i lt eb tb. _` irule >>
     asm_x "suffix_env" mp_tac >>
     asm_x "suffix_old" mp_tac >>
     asm_x "suffix_comp" mp_tac >>
     simp[Abbr `em`, vv_operand_def] >> rpt strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `gas_summary_at T _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  qexistsl_tac [`res`,`es_end`,`out`] >>
  simp[vv_location_def, vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def,
      Abbr `e0`, exprSimPropsTheory.vv_post_initial_gas] >>
  qpat_x_assum `vv_post _ _ _ _ (Subscript ann obj idx) _ _ _ _ _ child _ _` mp_tac >>
  simp[exprSimPropsTheory.vv_post_initial_gas]
QED
Finalise compile_subscript_array_framed_base_mem_case_from_suffix
