(* Ordinary (non-code) slice operand composition. *)
Theory exprSimSliceOrdinary
Ancestors
  exprSimSliceSource exprSimSliceMemory exprSimSliceDataPost
  exprSimHyps exprSimHypsDefs exprSimSource exprSimVVFrame
  exprSimSliceCompose exprSimSliceOrdinaryFrame exprSimSliceOrdinaryContext
  exprSimSliceDynamicAdapter exprSimSliceFixedAdapter exprSimSliceOrdinaryContinue
  exprSimSliceOrdinaryEntry compileEnv
  exprSimDefs exprLowering exprLoweringProps exprBopLowering exprSimWordArgs vyperState pair

Theorem names_builtin_slice[local]:
  !args. ~names_builtin (Slice n) args
Proof
  `!bt args. names_builtin bt args ==> bt <> Slice n` suffices_by metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem slice_nonextcode_source[local]:
  ~is_extcode src ==> code_slice_source (Slice n) [src; start; len] = NONE
Proof
  strip_tac >> Cases_on `code_slice_source (Slice n) [src; start; len]` >> simp[] >>
  rename1 `_ = SOME p` >> PairCases_on `p` >>
  fs[vyperInterpreterTheory.code_slice_source_SOME, is_extcode_def]
QED

Theorem slice_ordinary_actions[local]:
  ~is_extcode src ==>
  eval_expr cx (Builtin ann (Slice n) [src; start; len]) =
  do v <- bind (eval_expr cx src) (read_result cx);
     st <- bind (eval_expr cx start) (read_result cx);
     ln <- bind (eval_expr cx len) (read_result cx);
     acc <- get_accounts;
     out <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                       (MAP expr_type [src; start; len]) [v; st; ln]);
     return (Value out)
  od
Proof
  strip_tac >>
  `code_slice_source (Slice n) [src; start; len] = NONE` by
    (irule slice_nonextcode_source >> simp[]) >>
  drule slice_eval_ordinary >>
  disch_then (qspecl_then [`cx`, `ann`] SUBST1_TAC) >>
  simp[eval_exprs_cons_action, bind_assoc] >>
  `eval_exprs cx [] = return []` by simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[bind_return, bind_assoc]
QED

Theorem compile_slice_ordinary_case:
 exprs_case nocalls ctx func cenv cx args /\
 ~is_self_code (HD args) /\ ~is_extcode (HD args) ==>
 expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
 strip_tac >> rewrite_tac[expr_vv_case_def] >> rpt gen_tac >> strip_tac >>
 `well_typed_expr env (Builtin ann (Slice n) args)` by fs[expr_body_pre_def] >>
 drule slice_typed_args >>
 disch_then (qx_choose_then `src` (qx_choose_then `start` (qx_choose_then `len`
   (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
 gvs[] >>
 `expr_sim_case nocalls ctx func cenv cx src` by fs[exprs_case_def] >>
 `expr_body_pre cenv cx env src es` by
   (irule expr_body_pre_builtin_arg >> conj_tac
    >- fs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[]) >>
 `nocalls ==> int_calls_expr src = []` by
   (gvs[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
 drule_all expr_sim_case_apply >>
 disch_then (qspec_then `expr_type src` mp_tac) >>
 strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
 `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
   (drule slice_ordinary_actions >>
    strip_tac >>
    fs[] >> drule slice_gas_admissible_expr_head >> simp[]) >>
 `!e. MEM e [start; len] ==> ~is_extcode e` by
   (gvs[vyperTypeSystemTheory.well_typed_expr_def] >> rpt strip_tac >>
    imp_res_tac exprSimSourceTheory.well_typed_extcode_type >> gvs[]) >>
 `~names_builtin (Slice n) [src; start; len]` by simp[names_builtin_slice] >>
 qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
 simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
      lower_value_child_call] >>
 Cases_on `is_bytestring_type (expr_type src)` >> gvs[] >>
 rpt (pairarg_tac >> simp[]) >> strip_tac >>
 (qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty start sc = (start_op,sd)` >>
  `ci_mono st1 sc` by
    metis_tac[ci_mono_compile_bytestring_src, slice_fixed_capture_ci_mono, SND] >>
  drule_all slice_ordinary_pipeline_context >> strip_tac)
 >~ [`compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`]
 >- suspend "dynamic"
 >~ [`compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`]
 >- suspend "dynamic"
 >> suspend "fixed"
QED

Resume compile_slice_ordinary_case[dynamic]:
 markerLib.RESUME_TAC >> (
 `!z. src_op = Var z ==> not_fresh_at st1 z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ src _ = _` (irule_at Any) >> simp[]) >>
 `!z. start_op = Var z ==> not_fresh_at sd z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >> simp[]) >>
 `!z. len_op = Var z ==> not_fresh_at st4 z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >> simp[]) >>
 `(!z. src_op = Var z ==> not_fresh_at sc z) /\
  (!op z. MEM op [src_len;src_data] /\ op = Var z ==>
     not_fresh_at sc z /\ not_fresh_at sd z /\ not_fresh_at st4 z)` by
   (drule slice_bytestring_src_shape >> strip_tac >>
    fs[exprLoweringPropsTheory.ci_mono_def] >>
    simp[] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
    metis_tac[]) >>
 `!l. src_op <> Label l` by
   (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
 `expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es` by
   (conj_tac >> (irule expr_body_pre_builtin_arg >> conj_tac
    >- fs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[])) >>
 `!l. start_op <> Label l` by
   (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
    qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
    goal_assum (drule_at Any)) >>
 `!op l. MEM op [src_len;src_data;start_op] ==> op <> Label l` by
   (drule slice_bytestring_src_shape >> strip_tac >> simp[] >> metis_tac[]) >>
 `!z. start_op = Var z ==> not_fresh_at st4 z` by
   (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `sd` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
 qpat_abbrev_tac `whole = Builtin _ (Slice n) [src;start;len]` >>
 `type_memory_bytes cenv (expr_type whole) < dimword (:256)` by
   (fs[Abbr `whole`, expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def, is_word_type_def, vyperASTTheory.expr_type_def] >>
    simp[wordsTheory.dimword_def] >> decide_tac) >>
 `32+n <= type_memory_bytes cenv (expr_type whole)` by
   (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
    simp[Abbr `whole`, vyperASTTheory.expr_type_def, type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
 gvs[Abbr `whole`, vyperASTTheory.expr_type_def] >>
 qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
 rewrite_tac[expr_sim_def] >> disch_then drule_all >> strip_tac >>
 qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ spost _` >>
 drule slice_ordinary_actions >> strip_tac >> asm_rewrite_tac[] >>
 irule slice_gas_outcome_bind_value >>
 qexists_tac `\v ee t. spost (INL v) ee t` >>
 reverse conj_tac
 >- (irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
     simp[Abbr `spost`] >> rpt strip_tac >>
     Cases_on `res` >> gvs[] >> rename1 `expr_exit (INR ex) r` >>
     qspec_then `Value` (qspec_then `INR ex` mp_tac) expr_exit_success_map >>
     simp[]) >>
 rpt gen_tac >> simp[Abbr `spost`] >> strip_tac >>
 qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `!a b c d e. eval_expr _ _ = _` kall_tac >>
 qpat_x_assum `expr_sim_case _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `nocalls ==> int_calls_expr src = []` kall_tac >>
 qpat_x_assum `gas_admissible (bind (eval_expr cx src) _) _ _` kall_tac >>
 qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ outpost _` >>
 `?gs. bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) =
       (INL v, mid with gas_obs := [])` by
   (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
 `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
 `~t.vs_halted` by
   (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    simp[gasSummaryTheory.gas_marked_exec_def,
         fragGasModeTheory.gas_marked_path_def] >>
    strip_tac >> drule fragGasPathTheory.gas_path_normal >> simp[]) >>
 drule_all (INST_TYPE [alpha |-> ``:eval_result``] slice_source_dynamic_capture_entry) >>
 simp[] >> strip_tac >>
 first_x_assum ho_match_mp_tac >>
 qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ (_,uc) _ _` >>
 gvs[] >>
 suspend "dynamic_kind")
QED

Resume compile_slice_ordinary_case[dynamic_kind]:
 markerLib.RESUME_TAC >~ [`expr_type src = BaseT (StringT cap)`]
 >- suspend "dynamic_string"
 >> suspend "dynamic_bytes"
QED

Resume compile_slice_ordinary_case[dynamic_bytes]:
 `expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
       read_result cx tv s1 = (INL v,t1)) ==>
   expr_sim_case nocalls ctx func cenv cx len)` by
   (qpat_x_assum `exprs_case _ _ _ _ _ _` mp_tac >>
    simp[exprs_case_def] >>
    qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
    simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
 `expr_body_pre cenv cx env start mid /\ expr_body_pre cenv cx env len mid` by
   (conj_tac >> (irule expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> simp[])) >>
 `LENGTH bs <= cap` by
   (qpat_x_assum `bind _ _ _ = (INL (BytesV bs),_)` mp_tac >>
    qpat_x_assum `expr_body_pre _ _ _ src es` mp_tac >>
    qpat_x_assum `expr_type src = _` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
    drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypingTheory.value_has_type_def, vyperValueTheory.evaluate_type_def]) >>
 Cases_on `compile_slice_data src_len src_data start_op len_op
   (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st4` >>
 gvs[as_ptr_val_def] >>
 irule slice_gas_outcome_conseq >>
 irule_at Any slice_bytes_continue_entry_seq >>
 qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
 qexistsl_tac [`w2n p + 32`, `src`, `nocalls`, `env`] >>
 suspend "bytes_entry"
QED

Resume compile_slice_ordinary_case[bytes_entry]:
 simp[Abbr `uc`, vyperTypeSystemTheory.bytelike_type_bound_def] >>
 conj_tac >- first_x_assum ACCEPT_TAC >>
 conj_tac >- (qpat_x_assum `nocalls ==> _` mp_tac >>
   simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
 `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= st4.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= st4.cs_next_id` by
   (qpat_x_assum `ci_mono sc sd` mp_tac >>
    qpat_x_assum `ci_mono sd st4` mp_tac >>
    simp[ci_mono_def]) >>
 simp[] >>
 conj_tac >- suspend "bytes_nonhalt" >>
 conj_tac >- metis_tac[] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- suspend "bytes_persist" >>
 suspend "bytes_rebase"
QED

Resume compile_slice_ordinary_case[dynamic_string]:
 `expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
       read_result cx tv s1 = (INL v,t1)) ==>
   expr_sim_case nocalls ctx func cenv cx len)` by
   (qpat_x_assum `exprs_case _ _ _ _ _ _` mp_tac >>
    simp[exprs_case_def] >>
    qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
    simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
 `expr_body_pre cenv cx env start mid /\ expr_body_pre cenv cx env len mid` by
   (conj_tac >> (irule expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> simp[])) >>
 `LENGTH str <= cap` by
   (qpat_x_assum `bind _ _ _ = (INL (StringV str),_)` mp_tac >>
    qpat_x_assum `expr_body_pre _ _ _ src es` mp_tac >>
    qpat_x_assum `expr_type src = _` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
    drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypingTheory.value_has_type_def, vyperValueTheory.evaluate_type_def]) >>
 Cases_on `compile_slice_data src_len src_data start_op len_op
   (type_memory_bytes cenv (BaseT (StringT n))) st4` >>
 gvs[as_ptr_val_def] >>
 irule slice_gas_outcome_conseq >>
 irule_at Any slice_string_continue_entry_seq >>
 qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
 qexistsl_tac [`w2n p + 32`, `src`, `nocalls`, `env`] >>
 suspend "string_entry"
QED

Resume compile_slice_ordinary_case[string_entry]:
 simp[Abbr `uc`, vyperTypeSystemTheory.bytelike_type_bound_def] >>
 conj_tac >- first_x_assum ACCEPT_TAC >>
 conj_tac >- (qpat_x_assum `nocalls ==> _` mp_tac >>
   simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
 `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= st4.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= st4.cs_next_id` by
   (qpat_x_assum `ci_mono sc sd` mp_tac >>
    qpat_x_assum `ci_mono sd st4` mp_tac >>
    simp[ci_mono_def]) >>
 simp[] >>
 conj_tac >- suspend "string_nonhalt" >>
 conj_tac >- metis_tac[] >>
 conj_tac >- metis_tac[] >>
 conj_tac >- suspend "string_persist" >>
 suspend "string_rebase"
QED

Resume compile_slice_ordinary_case[bytes_nonhalt]:
 markerLib.RESUME_TAC >> (
 `?w. eval_operand src_op t = SOME w` by
   (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
 drule_all slice_bytestring_src_run >> strip_tac >> gvs[] >>
 qpat_x_assum `_ = t with vs_vars := _` SUBST1_TAC >> simp[])
QED

Resume compile_slice_ordinary_case[bytes_persist]:
 markerLib.RESUME_TAC >> (
 rpt strip_tac >> first_x_assum irule >>
 goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Resume compile_slice_ordinary_case[bytes_rebase]:
 markerLib.RESUME_TAC >> (
 simp[Abbr `outpost`] >> rpt strip_tac >>
 qexists_tac `tv` >> simp[] >>
 irule slice_bytestring_source_post_rebase >>
 goal_assum (drule_at Any) >> simp[] >>
 goal_assum (drule_at Any) >> simp[] >>
 qpat_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` (irule_at Any) >>
 simp[] >>
 `?w. eval_operand src_op t = SOME w` by
   (qpat_x_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` mp_tac >>
    simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
      is_word_type_def, vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
 qexists_tac `w` >> simp[] >>
 `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
   (qpat_assum `bind _ _ _ = (INL _,_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
 gvs[ci_mono_def])
QED

Resume compile_slice_ordinary_case[string_nonhalt]:
 markerLib.RESUME_TAC >> (
 `?w. eval_operand src_op t = SOME w` by
   (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def, is_word_type_def,
      vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
 drule_all slice_bytestring_src_run >> strip_tac >> gvs[] >>
 qpat_x_assum `_ = t with vs_vars := _` SUBST1_TAC >> simp[])
QED

Resume compile_slice_ordinary_case[string_persist]:
 markerLib.RESUME_TAC >> (
 rpt strip_tac >> first_x_assum irule >>
 goal_assum (drule_at Any) >> simp[] >> metis_tac[])
QED

Resume compile_slice_ordinary_case[string_rebase]:
 markerLib.RESUME_TAC >> (
 simp[Abbr `outpost`] >> rpt strip_tac >>
 qexists_tac `tv` >> simp[] >>
 irule slice_bytestring_source_post_rebase >>
 goal_assum (drule_at Any) >> simp[] >>
 goal_assum (drule_at Any) >> simp[] >>
 qpat_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` (irule_at Any) >>
 simp[] >>
 `?w. eval_operand src_op t = SOME w` by
   (qpat_x_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` mp_tac >>
    simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
      is_word_type_def, vyperValueTheory.evaluate_type_def] >> metis_tac[]) >>
 qexists_tac `w` >> simp[] >>
 `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
   (qpat_assum `bind _ _ _ = (INL _,_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
 gvs[ci_mono_def])
QED

Resume compile_slice_ordinary_case[fixed]:
 markerLib.RESUME_TAC >> gvs[is_bytestring_type_def] >>
 Cases_on `bd` >> gvs[is_bytestring_type_def] >>
 rename1 `expr_type src = BaseT (BytesT (Fixed m))` >>
 qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty len sd = (len_op,se)` >>
 suspend "fixed_prepare"
QED

Resume compile_slice_ordinary_case[fixed_prepare]:
 `!z. src_op = Var z ==> not_fresh_at st1 z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ src _ = _` (irule_at Any) >> simp[]) >>
 `!z. start_op = Var z ==> not_fresh_at sd z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >> simp[]) >>
 `!z. len_op = Var z ==> not_fresh_at se z` by
   (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
    qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >> simp[]) >>
 `expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es` by
   (conj_tac >> (irule expr_body_pre_builtin_arg >> conj_tac
    >- fs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[])) >>
 `!l. start_op <> Label l` by
   (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
    qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
    goal_assum (drule_at Any)) >>
 `!z. start_op = Var z ==> not_fresh_at se z` by
   (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `sd` >> fs[ci_mono_def]) >>
 `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
   (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def, is_word_type_def] >>
    simp[wordsTheory.dimword_def] >> decide_tac) >>
 `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
   (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
    simp[type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
 suspend "fixed_source"
QED

Resume compile_slice_ordinary_case[fixed_source]:
 qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
 rewrite_tac[expr_sim_def] >> disch_then drule_all >> strip_tac >>
 qmatch_asmsub_abbrev_tac `gas_outcome _ _ _ _ _ spost _` >>
 drule slice_ordinary_actions >> strip_tac >> asm_rewrite_tac[] >>
 irule slice_gas_outcome_bind_value >>
 qexists_tac `\v ee t. spost (INL v) ee t` >>
 reverse conj_tac
 >- (irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
     simp[Abbr `spost`] >> rpt strip_tac >>
     Cases_on `res` >> gvs[] >> rename1 `expr_exit (INR ex) r` >>
     qspec_then `Value` (qspec_then `INR ex` mp_tac) expr_exit_success_map >>
     simp[]) >>
 rpt gen_tac >> simp[Abbr `spost`] >> strip_tac >>
 qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `!a b c d e. eval_expr _ _ = _` kall_tac >>
 qpat_x_assum `expr_sim_case _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `nocalls ==> int_calls_expr src = []` kall_tac >>
 qpat_x_assum `gas_admissible (bind (eval_expr cx src) _) _ _` kall_tac >>
 qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ outpost _` >>
 `?gs. bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) =
       (INL v, mid with gas_obs := [])` by
   (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
 `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
 `~t.vs_halted` by
   (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    simp[gasSummaryTheory.gas_marked_exec_def,
         fragGasModeTheory.gas_marked_path_def] >>
    strip_tac >> drule fragGasPathTheory.gas_path_normal >> simp[]) >>
 suspend "fixed_capture"
QED

Resume compile_slice_ordinary_case[fixed_capture]:
 `m <= 32` by
   (qpat_x_assum `bind _ _ _ = (INL v,_)` mp_tac >>
    qpat_x_assum `expr_body_pre _ _ _ src (es with gas_obs := gs)` mp_tac >>
    qpat_x_assum `expr_type src = _` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
    gvs[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def,
      vyperTypingTheory.value_has_type_def, vyperValueTheory.evaluate_type_def]) >>
 drule_all (INST_TYPE [alpha |-> ``:eval_result``] slice_source_fixed_capture_entry) >>
 simp[] >> strip_tac >>
 first_x_assum ho_match_mp_tac >>
 qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ (_,uc) _ _` >>
 gvs[] >>
 suspend "fixed_continue"
QED

Resume compile_slice_ordinary_case[fixed_continue]:
 `expr_sim_case nocalls ctx func cenv cx start /\
  ((?s tv t s1 v t1. eval_expr cx start s = (INL tv,t) /\
       read_result cx tv s1 = (INL v,t1)) ==>
   expr_sim_case nocalls ctx func cenv cx len)` by
   (qpat_x_assum `exprs_case _ _ _ _ _ _` mp_tac >>
    simp[exprs_case_def] >>
    qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
    simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
 `expr_body_pre cenv cx env start mid /\ expr_body_pre cenv cx env len mid` by
   (conj_tac >> (irule expr_body_pre_builtin_arg >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> simp[])) >>
 Cases_on `compile_slice_data (Lit (n2w (LENGTH bs))) (Var x) start_op len_op
   (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) se` >>
 gvs[as_ptr_val_def, fixed_bytes_size_def] >>
 irule slice_gas_outcome_conseq >>
 irule_at Any slice_bytes_continue_entry_seq >>
 qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
 qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
 qexistsl_tac [`w2n p`, `src`, `nocalls`, `env`] >>
 suspend "fixed_entry"
QED

Resume compile_slice_ordinary_case[fixed_entry]:
 simp[Abbr `uc`, vyperTypeSystemTheory.bytelike_type_bound_def] >>
 conj_tac >- first_x_assum ACCEPT_TAC >>
 conj_tac >- (qpat_x_assum `nocalls ==> _` mp_tac >>
   simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
 `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= se.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= se.cs_next_id` by
   (qpat_x_assum `ci_mono sc sd` mp_tac >>
    qpat_x_assum `ci_mono sd se` mp_tac >> simp[ci_mono_def]) >>
 `not_fresh_at sd x /\ not_fresh_at se x` by
   (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
    qexists_tac `sc` >> fs[ci_mono_def] >> decide_tac) >>
 simp[] >>
 conj_tac >- suspend "fixed_nonhalt" >>
 conj_tac >- metis_tac[] >>
 conj_tac >- metis_tac[] >>
 suspend "fixed_rebase"
QED

Resume compile_slice_ordinary_case[fixed_nonhalt]:
 `u.vs_halted = t.vs_halted` by
   (irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_halted`
      exprLoweringPropsTheory.run_inst_seq_preserves_field)) >>
    goal_assum (drule_at Any) >> rpt strip_tac >>
    drule_all venomExecPropsTheory.step_inst_base_OK_preserves_halted >> simp[]) >>
 simp[]
QED

Resume compile_slice_ordinary_case[fixed_rebase]:
 rpt gen_tac >> strip_tac >> gvs[Abbr `outpost`] >>
 irule slice_fixed_source_post_rebase >>
 goal_assum (drule_at Any) >> simp[] >>
 qpat_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` (irule_at Any) >>
 qpat_assum `compile_alloc_buffer 32 st1 = _` (irule_at Any) >>
 simp[] >>
 `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
   (qpat_assum `bind _ _ _ = (INL _,_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
 `vyperTyping$value_has_type (BaseTV (BytesT (Fixed (LENGTH bs)))) (BytesV bs)` by
   simp[vyperTypingTheory.value_has_type_def] >>
 drule_all exprSimHashTheory.hash_fixed_post_view >> strip_tac >>
 qexistsl_tac [`w`, `u`] >> simp[] >>
 `emit_void MSTORE [tmp_alloc.buf_operand; src_op] st2 = ((),sc)` by simp[] >>
 drule_all slice_fixed_scratch_code >> strip_tac >>
 drule_all slice_fixed_scratch_embedding >> strip_tac >>
 `emitted_insts st1 sc = emitted_insts st1 st2 ++ emitted_insts st2 sc` by
   (qpat_assum `sc.cs_current_insts = st1.cs_current_insts ++ _` mp_tac >>
    rpt (pop_assum kall_tac) >>
    rewrite_tac[emitted_insts_def] >> strip_tac >>
    qpat_x_assum `sc.cs_current_insts = _` (fn th =>
      CONV_TAC (LAND_CONV (RAND_CONV (REWR_CONV th)))) >>
    simp[rich_listTheory.DROP_APPEND1]) >>
 simp[] >>
 qpat_x_assum `ci_mono sa st1` mp_tac >>
 qpat_x_assum `ci_mono st1 sc` mp_tac >>
 simp[ci_mono_def] >> strip_tac >> strip_tac >> simp[] >>
 qpat_assum `expr_post _ _ _ _ src es sa st1 _ _ _ _ _` mp_tac >>
 simp[loweringPostsTheory.expr_post_def] >>
 conj_tac >- (qpat_x_assum `run_inst_seq (_ ++ _) t = OK u` mp_tac >> simp[]) >>
 fs[loweringPostsTheory.expr_post_def]
QED

Finalise compile_slice_ordinary_case
