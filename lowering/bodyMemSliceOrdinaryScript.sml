(* Ordinary slice assembly using counted operand and capture outcomes. *)
Theory bodyMemSliceOrdinary
Ancestors
  bodyMemSliceDynamicCapture bodyMemSliceScratch bodyMemSliceTypedContinue
  bodyMemoryPreds rawCallArgumentMemory exprSimSliceOrdinary
  exprSimSliceOrdinaryContext exprSimSliceOrdinaryEntry
  exprSimHyps exprSimHypsDefs exprSimSource exprSimMemDefs exprSimSliceCompose
  exprSimSliceSource exprSimSliceMemory exprLowering exprLoweringProps exprBopLowering pair
  bodyDeclMemoryCompose bodyMemBiSha256Compose emitHelper venomInst compileEnv

Theorem slice_ordinary_vv_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Slice n) args) es /\
  body_exprs_mem_ok cx args /\
  ~is_self_code (HD args) /\ ~is_extcode (HD args) ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Slice n) args) es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (Slice n) args)` by fs[expr_body_pre_def] >>
  drule slice_typed_args >>
  disch_then (qx_choose_then `src` (qx_choose_then `start` (qx_choose_then `len`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >> gvs[] >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_builtin_arg >> conj_tac
     >- fs[expr_body_pre_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type src) src es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `gas_admissible (bind (eval_expr cx src) (read_result cx)) expr_res_ok es` by
    (drule slice_ordinary_actions >> strip_tac >> fs[] >>
     drule slice_gas_admissible_expr_head >> simp[]) >>
  `~names_builtin (Slice n) [src;start;len]` by simp[names_builtin_slice] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call] >>
  Cases_on `is_bytestring_type (expr_type src)` >> gvs[] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  (qmatch_asmsub_rename_tac `lower_value compile_expr cenv ty start sc = (start_op,sd)` >>
   `ci_mono st1 sc` by
     metis_tac[ci_mono_compile_bytestring_src, slice_fixed_capture_ci_mono, SND] >>
   drule_all slice_ordinary_pipeline_context >> strip_tac) >>
  (drule slice_ordinary_actions >> strip_tac >> asm_rewrite_tac[] >>
   irule raw_call_mem_value_bind >>
   qpat_assum `lower_value _ _ _ src _ = _` (irule_at Any) >> simp[] >>
   conj_tac >- (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
      simp[exprSimDefsTheory.expr_exit_def] >> rename1 `Error err` >>
      Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]) >>
   rpt gen_tac >> strip_tac >>
   `body_exprs_mem_ok cx [start;len]` by
     (qpat_x_assum `body_exprs_mem_ok _ _` mp_tac >>
      simp[body_exprs_mem_ok_def] >>
      qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
      simp[vyperStateTheory.bind_def, AllCaseEqs()] >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
   `!e st. MEM e [start;len] /\ expr_sim_inv cenv cx env st ==>
       expr_body_pre cenv cx env e st` by
     (rpt strip_tac >> gvs[] >> irule expr_body_pre_builtin_typed_arg >>
      conj_tac >- simp[] >> simp[] >> goal_assum (drule_at Any) >> simp[])) >>
  all_tac
  >~ [`compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`]
  >- suspend "dynamic"
  >~ [`compile_bytestring_src src_op st1 = ((src_len,src_data),sc)`]
  >- suspend "dynamic"
  >> suspend "fixed"
QED

Resume slice_ordinary_vv_mem[dynamic]:
  markerLib.RESUME_TAC >>
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
    (drule slice_bytestring_src_shape >> strip_tac >> fs[ci_mono_def] >>
     simp[] >> rpt strip_tac >> gvs[compileEnvTheory.not_fresh_at_def] >> metis_tac[]) >>
  `!l. src_op <> Label l` by
    (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_body_pre cenv cx env start es` by
    (irule expr_body_pre_builtin_typed_arg >> conj_tac >- simp[] >>
     simp[] >> conj_tac >- fs[expr_body_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!l. start_op <> Label l` by
    (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
     qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
     goal_assum (drule_at Any)) >>
  `!op l. MEM op [src_len;src_data;start_op] ==> op <> Label l` by
    (drule slice_bytestring_src_shape >> strip_tac >> simp[] >> metis_tac[]) >>
  `!z. start_op = Var z ==> not_fresh_at st4 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sd` >> fs[ci_mono_def]) >>
  drule_all slice_source_dynamic_capture_entry_mem >> simp[] >> strip_tac >>
  (irule gas_outcome_zero_prefix_mem >> goal_assum (drule_at Any))
  >~ [`v = BytesV bs`]
  >- suspend "dynamic_bytes"
  >> suspend "dynamic_string"
QED

Resume slice_ordinary_vv_mem[dynamic_bytes]:
  gvs[] >>
  `expr_body_pre cenv cx env start ee /\ expr_body_pre cenv cx env len ee` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty start ee` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `!gs' v' ee'. bind (eval_expr cx start) (read_result cx) (ee with gas_obs := gs') =
      (INL v',ee') /\ ee'.gas_obs = [] ==>
      expr_sim_mem ctx func cenv cx ty len ee' /\
      gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee'` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env start (ee with gas_obs := gs')` by simp[] >>
     drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
     `expr_body_pre cenv cx env len ee'` by
       (first_x_assum irule >> simp[]) >>
     conj_tac >- (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  Cases_on `compile_slice_data src_len src_data start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st4` >>
  gvs[exprLoweringTheory.as_ptr_val_def] >>
  irule gas_outcome_post_mono >>
  qpat_assum `expr_type src = _` (fn tsrc =>
    qpat_assum `expr_type start = _` (fn tstart =>
      qpat_assum `expr_type len = _` (fn tlen =>
        irule_at Any (SIMP_RULE (srw_ss())
          [tsrc,tstart,tlen,vyperASTTheory.expr_type_def]
          (slice_bytes_continue_seq_mem |> Q.INST
            [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]`]))))) >>
  qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
  qexistsl_tac [`w2n p + 32`, `env`] >>
  `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= st4.cs_next_var /\
   sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= st4.cs_next_id` by
    (fs[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac >- first_x_assum ACCEPT_TAC >>
  suspend "bytes_finish"
QED

Resume slice_ordinary_vv_mem[bytes_finish]:
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `n + 32 <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  conj_tac >- (
    `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
    drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
    simp[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def,
      vyperValueTheory.evaluate_type_def, vyperTypeSystemTheory.bytelike_type_bound_def,
      vyperTypingTheory.value_has_type_def]) >>
  suspend "bytes_rebase"
QED

Resume slice_ordinary_vv_mem[bytes_rebase]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  irule slice_bytestring_source_post_rebase >>
  qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `bind _ _ _ = (INL (BytesV bs),_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  simp[] >>
  qpat_x_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
    compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def] >> metis_tac[]
QED

Resume slice_ordinary_vv_mem[dynamic_string]:
  gvs[] >>
  `expr_body_pre cenv cx env start ee /\ expr_body_pre cenv cx env len ee` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty start ee` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `!gs' v' ee'. bind (eval_expr cx start) (read_result cx) (ee with gas_obs := gs') =
      (INL v',ee') /\ ee'.gas_obs = [] ==>
      expr_sim_mem ctx func cenv cx ty len ee' /\
      gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee'` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env start (ee with gas_obs := gs')` by simp[] >>
     drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
     `expr_body_pre cenv cx env len ee'` by
       (first_x_assum irule >> simp[]) >>
     conj_tac >- (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  Cases_on `compile_slice_data src_len src_data start_op len_op
    (type_memory_bytes cenv (BaseT (StringT n))) st4` >>
  gvs[exprLoweringTheory.as_ptr_val_def] >>
  irule gas_outcome_post_mono >>
  qpat_assum `expr_type src = _` (fn tsrc =>
    qpat_assum `expr_type start = _` (fn tstart =>
      qpat_assum `expr_type len = _` (fn tlen =>
        irule_at Any (SIMP_RULE (srw_ss())
          [tsrc,tstart,tlen,vyperASTTheory.expr_type_def]
          (slice_string_continue_seq_mem |> Q.INST
            [`result` |-> `Builtin (BaseT (StringT n)) (Slice n) [src;start;len]`]))))) >>
  qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
  qexistsl_tac [`w2n p + 32`, `env`] >>
  `sc.cs_next_var <= sd.cs_next_var /\ sd.cs_next_var <= st4.cs_next_var /\
   sc.cs_next_id <= sd.cs_next_id /\ sd.cs_next_id <= st4.cs_next_id` by
    (fs[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac >- first_x_assum ACCEPT_TAC >>
  suspend "string_finish"
QED

Resume slice_ordinary_vv_mem[string_finish]:
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `n + 32 <= type_memory_bytes cenv (BaseT (StringT n))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  `type_memory_bytes cenv (BaseT (StringT n)) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  conj_tac >- (
    `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
    drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >>
    simp[vyperTypeExprResultTheory.expr_result_typed_def,
      vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
      vyperTypeInvariantsTheory.value_result_typed_def,
      vyperValueTheory.evaluate_type_def, vyperTypeSystemTheory.bytelike_type_bound_def,
      vyperTypingTheory.value_has_type_def]) >>
  suspend "string_rebase"
QED

Resume slice_ordinary_vv_mem[string_rebase]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  irule slice_bytestring_source_post_rebase >>
  qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> fs[ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `bind _ _ _ = (INL (StringV str),_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  simp[] >>
  qpat_x_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
    compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def] >> metis_tac[]
QED

Resume slice_ordinary_vv_mem[fixed]:
  markerLib.RESUME_TAC >> gvs[compileEnvTheory.is_bytestring_type_def] >>
  Cases_on `bd` >> gvs[compileEnvTheory.is_bytestring_type_def] >>
  rename1 `expr_type src = BaseT (BytesT (Fixed m))` >>
  `m <= 32` by
    (`expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
     drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
     gvs[vyperTypeExprResultTheory.expr_result_typed_def,
       vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
       vyperTypeInvariantsTheory.value_result_typed_def,
       vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       vyperTypingTheory.value_has_type_def, vyperValueTheory.evaluate_type_def]) >>
  drule_all slice_source_fixed_capture_entry_mem >> simp[] >> strip_tac >>
  suspend "fixed_captured"
QED

Resume slice_ordinary_vv_mem[fixed_captured]:
  markerLib.RESUME_TAC >> gvs[] >>
  (irule gas_outcome_zero_prefix_mem >> goal_assum (drule_at Any)) >>
  suspend "fixed_continue"
QED

Resume slice_ordinary_vv_mem[fixed_continue]:
  `expr_body_pre cenv cx env start ee /\ expr_body_pre cenv cx env len ee` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty start ee` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `!gs' v' ee'. bind (eval_expr cx start) (read_result cx) (ee with gas_obs := gs') =
      (INL v',ee') /\ ee'.gas_obs = [] ==>
      expr_sim_mem ctx func cenv cx ty len ee' /\
      gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee'` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env start (ee with gas_obs := gs')` by simp[] >>
     drule_all (SRULE [SF ETA_ss] exprSimSourceTheory.expr_body_pre_eval) >> strip_tac >>
     `expr_body_pre cenv cx env len ee'` by
       (first_x_assum irule >> simp[]) >>
     conj_tac >- (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  gvs[exprLoweringTheory.fixed_bytes_size_def] >>
  Cases_on `compile_slice_data (Lit (n2w (LENGTH bs))) (Var x) start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st5` >>
  gvs[exprLoweringTheory.as_ptr_val_def] >>
  irule gas_outcome_post_mono >>
  qpat_assum `expr_type src = _` (fn tsrc =>
    qpat_assum `expr_type start = _` (fn tstart =>
      qpat_assum `expr_type len = _` (fn tlen =>
        irule_at Any (SIMP_RULE (srw_ss())
          [tsrc,tstart,tlen,vyperASTTheory.expr_type_def]
          (slice_bytes_continue_seq_mem |> Q.INST
            [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [src;start;len]`]))))) >>
  qpat_assum `compile_slice_data _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >>
  qexistsl_tac [`w2n p`, `env`] >>
  simp[vyperASTTheory.expr_type_def] >>
  suspend "fixed_finish"
QED

Resume slice_ordinary_vv_mem[fixed_finish]:
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!z. start_op = Var z ==> not_fresh_at sd z` by
    (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
     qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >> simp[]) >>
  `!z. len_op = Var z ==> not_fresh_at st5 z` by
    (rpt strip_tac >> irule exprOperandVarTheory.compile_lower_value_var >>
     qpat_assum `lower_value _ _ _ len _ = _` (irule_at Any) >> simp[]) >>
  `!l. start_op <> Label l` by
    (irule exprSimSliceCaptureTheory.slice_source_operand_not_label >>
     qpat_assum `lower_value _ _ _ start _ = _` (irule_at Any) >>
     metis_tac[]) >>
  fs[ci_mono_def] >>
  simp[venomStateTheory.eval_operand_def] >>
  conj_tac >- first_x_assum ACCEPT_TAC >>
  conj_tac >- (fs[compileEnvTheory.not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[compileEnvTheory.not_fresh_at_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `n + 32 <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def, vyperASTTheory.expr_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
    vyperTypeSystemTheory.bytelike_type_bound_def] >>
  suspend "fixed_rebase"
QED

Resume slice_ordinary_vv_mem[fixed_rebase]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `emitted_insts st1 sc = emitted_insts st1 st2 ++ emitted_insts st2 sc` by
    (irule exprLoweringPropsTheory.emitted_insts_append >> simp[]) >>
  reverse conj_tac >-
    (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts st1 st2 ++ emitted_insts st2 sc)` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all bodyMemBiSha256ComposeTheory.sha256_run_inst_seq_alloca_next_mono >>
     decide_tac) >>
  irule slice_fixed_source_post_rebase >>
  qpat_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_alloc_buffer _ _ = _` (irule_at Any) >>
  simp[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_assum `bind _ _ _ = (INL (BytesV bs),_)`
      (mp_tac o MATCH_MP (SRULE [SF ETA_ss] exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `!z. src_op = Var z ==> not_fresh_at st1 z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `run_inst_seq (emitted_insts st1 sc) t = OK u` by metis_tac[] >>
  `cs_extends st1 st2 /\ cs_extends st2 sc` by
    (conj_tac >- metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
     qspecl_then [`MSTORE`, `[Var x; src_op]`, `st2`] mp_tac ci_mono_emit_void >>
     simp[ci_mono_def]) >>
  `fn_has_code st1 st2 func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all actualAllocExecTheory.actual_alloc_buffer_site >> strip_tac >>
  `x = STRING #"%" (toString st1.cs_next_var)` by
    (qpat_x_assum `tmp_alloc.buf_operand = Var x` mp_tac >> simp[]) >>
  `run_inst_seq
     [mk_inst st1.cs_next_id ALLOCA [Lit 32w] [x];
      mk_inst (st1.cs_next_id + 1) MSTORE [Var x; src_op] []] t = OK u` by
    gvs[] >>
  qpat_x_assum `expr_post _ _ _ _ src _ _ _ _ _ _ _ _` mp_tac >>
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
    compileEnvTheory.is_word_type_def] >> metis_tac[]
QED

Finalise slice_ordinary_vv_mem
