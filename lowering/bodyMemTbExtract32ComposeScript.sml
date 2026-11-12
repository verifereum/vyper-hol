(* Counted memory composition for dynamic extract32 operands. *)
Theory bodyMemTbExtract32Compose
Ancestors
  exprSimExtract32Counted exprSimExtract32Post exprSimExtract32Source exprBopSimProps
  vyperStorageTrace vyperStorageFootprint
  bodyMemTbExtract32Encoding bodyMemTbExtract32WordSuffix bodyDeclMemoryCompose bodyMemTbExtract32Bind bodyMemTbExtract32Action bodyMemTbExtract32TypedSuffix bodyMemoryPreds exprSimDefs
  exprSimMemoryStack exprSimSource exprSimProps exprSimMemDefs bodyMemTbExtract32Source
  exprSimDefs exprSimHypsDefs gasNormalPrefix fragGasMode fragGasPath context
  exprOperandVar fragExec rich_list bodyMemTbExtract32SnapshotEntry bodyMemTbExtract32SuffixPost
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  exprLoweringProps exprLowering compileEnv loweringPosts bodyMemTbExtract32Cuts
  exprOpenFirstOperand exprSimHypsDefs emitHelper vyperValue
  vyperInterpreter vyperState vyperTypeSystem vyperAST list
  vyperTyping vyperTypeExprResult vyperTypeInvariants vyperTypeExprSoundness
  valueEncoding integer_word venomExecSemantics venomState builtinBytes emitHelperProps


Theorem extract32_read_action[local]:
  bind (eval_expr cx (TypeBuiltin ann Extract32 ret [src;off])) (read_result cx) =
  bind (bind (eval_expr cx src) (read_result cx)) (\v.
    bind (bind (eval_expr cx off) (read_result cx)) (\n.
      bind (lift_sum (evaluate_type_builtin cx Extract32 ret
        [expr_type src;expr_type off] [v;n])) (\r. return r)))
Proof
  rewrite_tac[extract32_eval_action] >>
  simp[bind_assoc, bind_return, read_result_def]
QED

Theorem extract32_off_operand[local]:
  expr_post H ctx func cenv cx off es sa sb s0 es' (IntV i) off_op t /\
  expr_type off = BaseT (UintT k) /\ 0 <= i ==>
  eval_operand off_op t = SOME (n2w (Num i))
Proof
  strip_tac >>
  `post_value_type cenv off = expr_type off` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  `expr_val_rel cx (expr_type off) (IntV i) off_op t` by gvs[expr_post_def] >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule_all expr_val_rel_typed >>
  simp[is_word_type_def, typed_val_to_w256_def, val_to_w256_def,
       integer_wordTheory.i2w_def, integerTheory.INT_NOT_LT]
QED


Theorem compile_extract32_sim_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 ret [src;off]) es /\
  body_exprs_mem_ok cx [src;off] /\
  expr_type src = BaseT (BytesT (Dynamic cap)) /\
  expr_type off = BaseT (UintT k) ==>
  expr_sim_mem ctx func cenv cx ty (TypeBuiltin ann Extract32 ret [src;off]) es
Proof
  strip_tac >> drule extract32_body_result_type >> strip_tac >> gvs[] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule expr_sim_mem_word_outcome >>
  conj_tac >- (Cases_on `bt` >> gvs[extract32_result_base_ok_def, expr_type_def, is_word_type_def] >>
    rename1 `BytesT bd` >> Cases_on `bd` >> gvs[extract32_result_base_ok_def, is_word_type_def] >>
    fs[expr_body_pre_def, well_typed_expr_def, well_formed_type_def, evaluate_type_def]) >>
  Cases_on `compile_expr cenv ty (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) sa` >>
  rename1 `_ = (vv,sc)` >>
  drule extract32_compile_equations >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  qpat_assum `expr_type src = _` (fn th =>
    drule_all (REWRITE_RULE [th] extract32_compile_cuts)) >> strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_head >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type src) src es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (irule extract32_source_admissible >> goal_assum (drule_at Any)) >>

  `?ln dn. len = Var ln /\ data = Var dn` by
    (qpat_x_assum `compile_bytestring_src _ _ = _` mp_tac >>
     Cases_on `emit_op MLOAD [src_op] s1` >>
     rename1 `_ = (lp, sl)` >>
     Cases_on `emit_op ADD [src_op; Lit 32w] sl` >>
     simp[compile_bytestring_src_def, comp_bind_def, comp_return_def] >>
     rpt strip_tac >> imp_res_tac emitted_insts_emit_op >> gvs[]) >>
  `(!l. len <> Label l) /\ (!l. data <> Label l)` by
    (qpat_assum `len = Var _` mp_tac >> qpat_assum `data = Var _` mp_tac >>
     rpt strip_tac >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `src_op`, `s0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >>
  rewrite_tac[extract32_read_action] >>
  match_mp_tac extract32_outcome_bind_marked >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx src es sa s1 s0 ee v src_op t /\
    expr_store_bound cx (expr_type src) v src_op t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac
  >- (`!(res:value + exception) r.
         (?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r) <=>
         expr_exit res r` by
        (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
      qpat_x_assum `gas_outcome _ _ _ _ _ (bind (eval_expr cx src) _) _ _ _` mp_tac >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      pop_assum (fn th => rewrite_tac[th, ETA_AX])) >>
  reverse conj_tac
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_lifts,
           storage_trace_frame_return]) >>
  suspend "stage1"
QED

(* The source is done: snapshot its bytes, then run the offset. *)
Resume compile_extract32_sim_mem[stage1]:
  qx_genl_tac [`marks1`, `v1`, `ee1`, `t1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!H. valid_horizon cx st0 H ee1.storage_trace ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee1.storage_trace`
    (qx_choose_then `H0` assume_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  `ee1 with gas_obs := [] = ee1` by simp[evaluation_state_component_equality] >>
  `t1.vs_current_bb = s1.cs_current_bb` by
    (qpat_x_assum `!H. _ ==> t1.vs_current_bb = _` (drule_then ACCEPT_TAC)) >>
  `t1.vs_inst_idx = LENGTH s1.cs_current_insts` by
    (qpat_x_assum `!H. _ ==> t1.vs_inst_idx = _` (drule_then ACCEPT_TAC)) >>
  `alloca_history func t1` by
    (qpat_x_assum `!H. _ ==> alloca_history func t1` (drule_then ACCEPT_TAC)) >>
  `s0.vs_alloca_next <= t1.vs_alloca_next` by
    (qpat_x_assum `!H. _ ==> s0.vs_alloca_next <= t1.vs_alloca_next`
       (drule_then ACCEPT_TAC)) >>
  `expr_store_bound cx (expr_type src) v1 src_op t1` by
    (qpat_x_assum `!H. _ ==> expr_store_bound _ _ _ _ _` (drule_then ACCEPT_TAC)) >>
  `~t1.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
    exprSimExtract32SourceTheory.extract32_marked_source_typed) >>
  strip_tac >>
  TRY (qpat_x_assum `v1 = BytesV _` SUBST_ALL_TAC) >>
  `bind (eval_expr cx src) (read_result cx)
     (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings) =
     (INL (BytesV bs), ee1)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H ee1.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `bind (eval_expr cx src) (read_result cx) _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result] >>
     strip_tac >>
     qpat_x_assum `valid_horizon _ _ H ee1.storage_trace` mp_tac >>
     simp[valid_horizon_def]) >>
  `MAP FDOM es.scopes = MAP FDOM ee1.scopes` by
    (qpat_assum `bind (eval_expr cx src) (read_result cx) _ = _`
       (mp_tac o MATCH_MP (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by simp[evaluate_type_def] >>
  `evaluate_type (get_tenv cx) (expr_type src) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by simp[] >>
  `!x. src_op = Var x ==> not_fresh_at s1 x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv s1` by
    (irule compiler_ci_mono_reserved >> qexists_tac `sa` >> simp[]) >>
  drule_all extract32_source_snapshot_entry >> strip_tac >>
  `expr_body_pre cenv cx env off ee1` by
    (qpat_x_assum `expr_body_pre _ _ _ off (ee1 with gas_obs := [])` mp_tac >>
     simp[]) >>
  `expr_sim_inv cenv cx env ee1` by
    (qpat_x_assum `expr_sim_inv _ _ _ (ee1 with gas_obs := [])` mp_tac >>
     simp[]) >>
  `body_expr_mem_ok cx off` by
    (fs[body_exprs_mem_ok_def] >>
     first_x_assum irule >>
     qpat_x_assum `bind (eval_expr cx src) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx ty off ee1` by
    metis_tac[body_expr_mem_ok_def] >>
  `gas_admissible (bind (eval_expr cx off) (read_result cx)) expr_res_ok ee1` by
    (qpat_x_assum `gas_admissible (bind (eval_expr cx (TypeBuiltin _ _ _ _)) _) _ _`
       mp_tac >> rewrite_tac[extract32_eval_action] >>
     once_rewrite_tac[bind_assoc] >>
     qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     first_x_assum (qspec_then `gas_explicit marks1 s0.vs_gas_readings ++ gs` mp_tac) >>
     simp[Once bind_def] >> simp[Once bind_def] >> simp[Once bind_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ off _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `off_op`, `u`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  strip_tac >>
  irule gas_outcome_zero_prefix_mem >> qexists_tac `u` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  match_mp_tac extract32_outcome_bind_marked >>
  qexists_tac `\H n ee t.
    expr_post H ctx func cenv cx off ee1 s2 s3 u ee n off_op t /\
    expr_store_bound cx (expr_type off) n off_op t /\
    t.vs_current_bb = s3.cs_current_bb /\
    t.vs_inst_idx = LENGTH s3.cs_current_insts /\
    alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next` >>
  conj_tac
  >- (`!(res:value + exception) r.
         (?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r) <=>
         expr_exit res r` by
        (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
      qpat_x_assum `gas_outcome _ _ _ _ _ (bind (eval_expr cx off) _) _ _ _` mp_tac >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      pop_assum (fn th => rewrite_tac[th, ETA_AX])) >>
  reverse conj_tac
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_lifts,
           storage_trace_frame_return]) >>
  suspend "stage2"
QED

(* Both operands are done: the suffix's Venom path decides the outcome. *)
Resume compile_extract32_sim_mem[stage2]:
  qx_genl_tac [`marks2`, `n2`, `ee2`, `t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `!H. valid_horizon cx st0 H ee2.storage_trace ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee2.storage_trace`
    (qx_choose_then `H1` assume_tac) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  `ee2 with gas_obs := [] = ee2` by simp[evaluation_state_component_equality] >>
  `t2.vs_current_bb = s3.cs_current_bb` by
    (qpat_x_assum `!H. _ ==> t2.vs_current_bb = _` (drule_then ACCEPT_TAC)) >>
  `t2.vs_inst_idx = LENGTH s3.cs_current_insts` by
    (qpat_x_assum `!H. _ ==> t2.vs_inst_idx = _` (drule_then ACCEPT_TAC)) >>
  `alloca_history func t2` by
    (qpat_x_assum `!H. _ ==> alloca_history func t2` (drule_then ACCEPT_TAC)) >>
  `u.vs_alloca_next <= t2.vs_alloca_next` by
    (qpat_x_assum `!H. _ ==> u.vs_alloca_next <= t2.vs_alloca_next`
       (drule_then ACCEPT_TAC)) >>
  `~t2.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ (ee1,u) _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     drule gas_marked_path_exec >> metis_tac[gas_path_normal]) >>
  `bind (eval_expr cx off) (read_result cx)
     (ee1 with gas_obs := gas_explicit marks2 u.vs_gas_readings) = (INL n2, ee2)` by
    (qpat_assum `gas_marked_exec _ _ _ (ee1,u) _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env off
     (ee1 with gas_obs := gas_explicit marks2 u.vs_gas_readings)` by simp[] >>
  `?i. n2 = IntV i /\ 0 <= i` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimExtract32SourceTheory.extract32_offset_value) >>
     goal_assum (drule_at Any) >> simp[is_uint_type_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  TRY (qpat_x_assum `n2 = IntV _` SUBST_ALL_TAC) >>
  `0 <= i /\ Num i < dimword (:256)` by
    (irule (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimExtract32PostTheory.extract32_offset_bounds) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `valid_horizon cx st0 H1 ee1.storage_trace` by
    (qpat_assum `bind (eval_expr cx off) (read_result cx) _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result] >>
     strip_tac >>
     qpat_x_assum `valid_horizon _ _ H1 ee2.storage_trace` mp_tac >>
     simp[valid_horizon_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H ee1.storage_trace ==>
                  valid_horizon cx st0 H es.storage_trace`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==>
                  stmt_state_rel H ctx func cenv cx es s0 /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee1.storage_trace ==>
                  expr_post H ctx func cenv cx src es sa s1 s0 ee1 (BytesV bs) src_op t1`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee2.storage_trace ==>
                  expr_post _ ctx func cenv cx off _ _ _ _ _ _ _ _`
    (drule_then assume_tac) >>
  `!H. valid_horizon cx st0 H ee2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee2 t2 /\
       storage_well_formed_on cx ee2 (FST H)` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_x_assum `!H. valid_horizon cx st0 H ee2.storage_trace ==>
                       expr_post _ ctx func cenv cx off _ _ _ _ _ _ _ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     rewrite_tac[expr_post_def] >> strip_tac >> conj_tac >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel H1 ctx func cenv cx ee2 t2` by
    (qpat_assum `!H. valid_horizon cx st0 H ee2.storage_trace ==>
                     stmt_state_rel H ctx func cenv cx ee2 t2 /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `eval_operand off_op t2 = SOME (n2w (Num i))` by
    (drule_all extract32_off_operand >> simp[]) >>
  `b < dimword (:256)` by decide_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) b t2.vs_memory` by
    (`val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs)
        (w2n (n2w b:bytes32)) u.vs_memory` by simp[wordsTheory.w2n_n2w] >>
     drule_all extract32_source_bytes_kept >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `eval_operand len t2 = SOME (n2w (LENGTH bs))` by
    (qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ t2`
       (mp_then (Pos hd) mp_tac
          exprSimExtract32PostTheory.extract32_post_operand_kept) >>
     disch_then (qspec_then `len` mp_tac) >>
     (impl_tac >-
        (conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!x. len = Var x \/ data = Var x ==> not_fresh_at s2 x`
               irule >> simp[])
         >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `n2w (LENGTH bs)` mp_tac) >> simp[]) >>
  `eval_operand data t2 = SOME (n2w (b + 32))` by
    (qpat_assum `expr_post _ _ _ _ _ off _ _ _ _ _ _ _ t2`
       (mp_then (Pos hd) mp_tac
          exprSimExtract32PostTheory.extract32_post_operand_kept) >>
     disch_then (qspec_then `data` mp_tac) >>
     (impl_tac >-
        (conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!x. len = Var x \/ data = Var x ==> not_fresh_at s2 x`
               irule >> simp[])
         >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `n2w (b + 32)` mp_tac) >> simp[]) >>
  `b + 32 + LENGTH bs <= t2.vs_alloca_next` by
    (qpat_x_assum `w2n _ + w2n _ <= u.vs_alloca_next` mp_tac >>
     simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
  `local_ptrs_reserved cenv s3` by
    (irule compiler_ci_mono_reserved >> qexists_tac `s2` >> simp[]) >>
  `!x. len = Var x \/ data = Var x \/ off_op = Var x ==> not_fresh_at s3 x` by
    (`!x. off_op = Var x ==> not_fresh_at s3 x` by
       metis_tac[compile_lower_value_var] >>
     rpt strip_tac >> gvs[] >>
     irule compiler_ci_mono_not_fresh >> qexists_tac `s2` >> simp[]) >>
  `wb_frame cenv es ee2 sa s0 t2` by
    (drule_all extract32_operands_frame >> simp[]) >>
  `~expr_has_effect (TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]) ==>
   pure_frame cenv func es sa s0 t2` by
    (simp[expr_has_effect_thm] >> rpt strip_tac >>
     drule_all extract32_operands_pure_frame >> simp[]) >>
  `well_formed_type (get_tenv cx) (BaseT bt)` by
    (qpat_assum `expr_body_pre cenv cx env (TypeBuiltin _ _ _ _) es` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def]) >>
  `alloca_room ctx func t2` by
    (qpat_x_assum `stmt_state_rel H1 ctx func cenv cx ee2 t2` mp_tac >>
     simp[stmt_state_rel_def]) >>
  `t2.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt] >>
  `Num i + 32 <= LENGTH bs ==> b + 32 + Num i < dimword (:256)` by decide_tac >>
  Cases_on `evaluate_extract32 bs (Num i) bt`
  >- suspend "suffix_success"
  >> suspend "suffix_revert"
QED

Resume compile_extract32_sim_mem[suffix_success]:
  `Num i + 32 <= LENGTH bs` by
    (qpat_x_assum `evaluate_extract32 _ _ _ = INL _` mp_tac >>
     rewrite_tac[vyperContextTheory.evaluate_extract32_def] >>
     IF_CASES_TAC >> simp_tac (srw_ss()) []) >>
  `is_word_type (BaseT bt)` by
    (Cases_on `bt` >> gvs[extract32_result_base_ok_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[extract32_result_base_ok_def, is_word_type_def] >>
     fs[well_formed_type_def, evaluate_type_def]) >>
  `sa.cs_next_var <= s3.cs_next_var` by fs[ci_mono_def] >>
  `b + 32 + Num i < dimword (:256)` by simp[] >>
  `?H. valid_horizon cx st0 H ee2.storage_trace` by metis_tac[] >>
  drule_all extract32_word_suffix_success >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func t2 ng (OK u')` >>
  `u.vs_alloca_next = t1.vs_alloca_next` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = t1`
       (mp_tac o Q.AP_TERM `vs_alloca_next`) >> simp[]) >>
  `s0.vs_alloca_next <= u'.vs_alloca_next` by decide_tac >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE ng F` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL x`, `ee2`, `OK u'`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def,
          vyperContextTheory.evaluate_type_builtin_def,
          lift_sum_def, bind_def, return_def, raise_def]
  >- (disj1_tac >> qexists_tac `u'` >> simp[] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_x_assum `!H. valid_horizon cx st0 H ee2.storage_trace ==>
                        expr_post H ctx func cenv cx (TypeBuiltin _ _ _ _) _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      simp[])
QED

Resume compile_extract32_sim_mem[suffix_revert]:
  `?msg. y = RuntimeError msg` by
    (qpat_x_assum `evaluate_extract32 _ _ _ = INR y` mp_tac >>
     Cases_on `Num i + 32 <= LENGTH bs`
     >- (drule extract32_inbounds_slice >> strip_tac >> simp[] >>
         Cases_on `bt` >> fs[extract32_result_base_ok_def] >>
         simp[extract32_slice_guards, AllCaseEqs()] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         fs[extract32_result_base_ok_def] >>
         simp[extract32_slice_guards, AllCaseEqs()]) >>
     simp[vyperContextTheory.evaluate_extract32_def]) >>
  qpat_x_assum `y = RuntimeError _` SUBST_ALL_TAC >>
  drule_all extract32_word_suffix_revert >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `REPLICATE k' F` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `ee2`,
    `Abort Revert_abort (t'' with vs_inst_idx := j)`] >>
  conj_tac
  >- simp[gas_marked_exec_def, gas_marked_path_def,
          vyperContextTheory.evaluate_type_builtin_def,
          lift_sum_def, bind_def, return_def, raise_def]
  >- (disj2_tac >> simp[expr_exit_def, exit_result_def])
QED
Finalise compile_extract32_sim_mem
