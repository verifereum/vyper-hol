(* Typed memory entry for external-code slice, retaining operand replay. *)
Theory bodyMemSliceExtcodeTyped
Ancestors
  bodyMemSliceExtcodeContinue bodyMemoryPreds exprSimSliceExtcodeTyped
  exprSimSliceExtcodeContext exprSimSliceExtcode exprSimSliceOrdinaryContinue exprSimSliceSource
  exprSimSliceCompose exprSimSliceCapacityRead exprSimSliceOrdinaryFrame
  exprSimMemDefs exprSimSource exprSimHyps exprSimHypsDefs exprSimWordArgs
  exprSimRawCall gasSummaryCompose exprLoweringProps exprBopLowering
  exprSimDefs exprLowering vyperState vyperAST pair

Theorem slice_read_marked_outcome_mem[local]:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!marks v mid t.
    gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s) marks (INL v) mid (OK t) /\
    expr_post ctx func cenv cx e es sa sb s (mid with gas_obs := []) v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (tail v : evaluation_state -> eval_result evaluation_result)
      (mid with gas_obs := [],t) Q (\res ee r. expr_exit res r)) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) tail) (es,s)
    Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >> disch_then drule_all >> strip_tac >>
  drule raw_call_outcome_normal >> strip_tac >>
  irule slice_gas_outcome_bind_value >>
  qexists_tac `\v ee t. expr_post ctx func cenv cx e es sa sb s ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule slice_gas_outcome_conseq >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >> gvs[] >>
      rename1 `expr_exit (INR ex) r` >>
      qspec_then `Value` (qspec_then `INR ex` mp_tac)
        exprSimDefsTheory.expr_exit_success_map >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> fs[] >> metis_tac[]
QED

Theorem slice_extcode_typed_entry_mem:
  body_inv tops ctx cenv cx /\
  ~is_self_code (Builtin ct (Acc Code) [a]) /\
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]) es /\
  expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es /\
  expr_body_pre cenv cx env a es /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_type a = BaseT AddressT /\
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a];start;len] /\
  body_exprs_mem_ok cx [start;len] /\
  ((?s vs t. eval_exprs cx [start;len] s = (INL vs,t)) ==>
    body_exprs_mem_ok cx [a]) ==>
  expr_vv_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by metis_tac[] >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call, is_self_code_def, is_extcode_def, extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all slice_extcode_pipeline_context >> strip_tac >>
  suspend "reads"
QED

Resume slice_extcode_typed_entry_mem[reads]:
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  qpat_x_assum `gas_admissible _ _ _` kall_tac >>
  qpat_x_assum `!xs. ~names_builtin _ xs` kall_tac >>
  qpat_x_assum `~is_self_code _` kall_tac >>
  `expr_sim_mem ctx func cenv cx ty start es` by
    (fs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[slice_extcode_actions] >>
  irule slice_read_marked_outcome_mem >> simp[] >>
  qexistsl_tac [`cenv`, `start_op`, `sa`, `st1`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "length"
QED

Resume slice_extcode_typed_entry_mem[length]:
  `?gs. bind (eval_expr cx start) (read_result cx) (es with gas_obs := gs) =
    (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `body_exprs_mem_ok cx [len]` by
    (fs[body_exprs_mem_ok_def] >>
     qpat_x_assum `(_ ==> body_expr_mem_ok _ len)` mp_tac >>
     impl_tac >- (qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
       simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >> simp[]) >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env len (mid with gas_obs := [])` by
    gvs[expr_body_pre_def] >>
  `expr_sim_mem ctx func cenv cx ty len (mid with gas_obs := [])` by
    (qpat_assum `body_exprs_mem_ok cx [len]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_mem_ok_def, body_expr_mem_ok_def]) >>
     first_x_assum (drule_at Any) >>
     metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  irule slice_read_marked_outcome_mem >> simp[] >>
  qexistsl_tac [`cenv`, `len_op`, `st1`, `st2`, `ty`] >> gvs[] >>
  rpt gen_tac >> strip_tac >> suspend "address"
QED

Resume slice_extcode_typed_entry_mem[address]:
  `?s vs t. eval_exprs cx [start;len] s = (INL vs,t)` by
    (imp_res_tac (gasSummaryTheory.gas_marked_exec_from_mem |> Q.INST [`memory` |-> `F`]) >>
     irule slice_two_marked_reads_success >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `body_exprs_mem_ok cx [a]` by metis_tac[] >>
  `?gs2. bind (eval_expr cx len) (read_result cx)
     ((mid with gas_obs := []) with gas_obs := gs2) =
     (INL v,mid' with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env (mid' with gas_obs := []) /\
   MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM (mid' with gas_obs := []).scopes /\
   ?k. v = IntV (&k) /\ k < dimword (:256) /\ eval_operand len_op t' = SOME (n2w k)` by
    (irule slice_uint_read_post >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `k <= n` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >> drule slice_literal_read_length >> intLib.ARITH_TAC) >>
  `expr_body_pre cenv cx env a (mid' with gas_obs := [])` by
    gvs[expr_body_pre_def] >>
  `expr_sim_mem ctx func cenv cx ty a (mid' with gas_obs := [])` by
    (qpat_assum `body_exprs_mem_ok cx [a]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_mem_ok_def, body_expr_mem_ok_def]) >>
     first_x_assum (drule_at Any) >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    metis_tac[expr_post_state] >>
  suspend "shape"
QED

Resume slice_extcode_typed_entry_mem[shape]:
  `(!z. start_op = Var z ==> not_fresh_at st1 z) /\ (!l. start_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ start _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `(!z. len_op = Var z ==> not_fresh_at st2 z) /\ (!l. len_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ len _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `(!z. addr_op = Var z ==> not_fresh_at st4 z)` by
    (qpat_assum `lower_value _ _ _ a _ = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  `eval_operand start_op t' = SOME (n2w i)` by
    (qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac slice_post_operands) >>
     disch_then irule >> fs[] >> metis_tac[]) >>
  `!op. MEM op [start_op;len_op] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at st2 x)` by
    (Cases_on `start_op` >> Cases_on `len_op` >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def]) >>
  Cases_on `compile_slice_extcode addr_op start_op len_op out_buf out_data st4` >>
  gvs[as_ptr_val_def] >> suspend "finish"
QED

Resume slice_extcode_typed_entry_mem[finish]:
  `q = out_buf` by metis_tac[slice_extcode_shape] >> gvs[] >>
  `fn_has_code st2 r func` by
    (irule fragExecTheory.fn_has_code_mid >>
     fs[ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, compileEnvTheory.cs_extends_refl]) >>
  irule gas_outcome_post_mono >>
  irule_at Any (slice_extcode_continue_entry_seq_mem |> SPEC_ALL |> Q.INST
    [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]`,
     `a` |-> `a`] |> SRULE [expr_type_def]) >>
  qpat_assum `compile_slice_out_buf _ _ = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ a _ = _` (irule_at Any) >>
  qpat_assum `compile_slice_extcode _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`start`, `len`, `BaseTV (BytesT (Dynamic n))`, `env`] >>
  simp[] >> suspend "finish_premises"
QED

Resume slice_extcode_typed_entry_mem[finish_premises]:
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (simp[vyperValueTheory.evaluate_type_def,
          vyperValueTheory.type_slot_size_def] >>
     qpat_x_assum `type_memory_bytes _ _ < _` mp_tac >>
     simp[compileEnvTheory.type_memory_bytes_def,
          vfmConstantsTheory.word_size_def] >> decide_tac) >>
  conj_tac >-
    (simp[NoAsms, valueEncodingTheory.type_memory_size_def,
      compileEnvTheory.type_memory_bytes_def,
      vfmConstantsTheory.word_size_def]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[exprLoweringTheory.lowered_value_type_def, expr_type_def] >>
  rename1 `vv_post _ _ _ _ _ _ _ _ _ _ _ _ final_state` >>
  `s0.vs_alloca_next <= final_state.vs_alloca_next` by decide_tac >>
  simp[] >>
  irule (slice_two_operand_post_rebase |> SPEC_ALL |> Q.INST
    [`sd` |-> `st1`, `se` |-> `st2`,
     `e1` |-> `mid with gas_obs := []`, `e2` |-> `mid' with gas_obs := []`]) >>
  qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
  fs[ci_mono_def] >> metis_tac[]
QED

Finalise slice_extcode_typed_entry_mem
