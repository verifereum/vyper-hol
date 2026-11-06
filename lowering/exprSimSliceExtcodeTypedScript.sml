(* Typed entry for the external-code slice, preserving source gas replay. *)
Theory exprSimSliceExtcodeTyped
Ancestors
  exprSimSliceExtcodeContinue exprSimSliceExtcodeContext
  exprSimSliceOrdinaryContinue exprSimSliceSource exprSimSliceCompose
  exprSimSliceCapacityRead exprSimSliceOrdinaryFrame exprSimSliceExtcode
  exprSimSource exprSimHyps exprSimHypsDefs exprSimWordArgs gasSummaryCompose
  exprLoweringProps exprBopLowering exprSimDefs exprLowering vyperState vyperAST pair

Theorem slice_two_reads_replay_success[local]:
  (!tail. bind (eval_expr cx start) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL sv,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx len) (read_result cx)
    ((mid with gas_obs := []) with gas_obs := ys ++ tail) =
      (INL lv,fin with gas_obs := tail)) ==>
  ?s vs t. eval_exprs cx [start;len] s = (INL vs,t)
Proof
  strip_tac >> gvs[] >>
  qexistsl_tac [`es with gas_obs := xs ++ ys`, `[sv;lv]`, `fin with gas_obs := []`] >>
  rewrite_tac[eval_exprs_cons_action] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
    (qspec_then `[]` assume_tac) >> fs[] >>
  gvs[bind_def, return_def]
QED

Theorem slice_two_marked_reads_success:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx start) (read_result cx))
    (es,s) marks (INL sv) mid (OK t) /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx len) (read_result cx))
    (mid with gas_obs := [],t) marks2 (INL lv) fin (OK r) ==>
  ?s vs t. eval_exprs cx [start;len] s = (INL vs,t)
Proof
  simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
  irule slice_two_reads_replay_success >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any)
QED

Theorem slice_extcode_actions:
  eval_expr cx (Builtin ann (Slice n) [Builtin ct (Acc Code) [a]; start; len]) =
  do st <- bind (eval_expr cx start) (read_result cx);
     ln <- bind (eval_expr cx len) (read_result cx);
     av <- bind (eval_expr cx a) (read_result cx);
     code_acc <- get_accounts;
     code_v <- lift_sum (evaluate_builtin cx code_acc ct (Acc Code) [expr_type a] [av]);
     acc <- get_accounts;
     v <- lift_sum (evaluate_builtin cx acc ann (Slice n)
             (MAP expr_type [Builtin ct (Acc Code) [a]; start; len]) [code_v;st;ln]);
     return (Value v)
  od
Proof
  rewrite_tac[slice_eval_extcode] >>
  simp[eval_exprs_cons_action, bind_assoc] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM, eval_exprs_nil, return_def] >>
  simp[bind_return, bind_assoc]
QED

Theorem slice_extcode_typed_entry:
  ~is_self_code (Builtin ct (Acc Code) [a]) /\
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]) es /\
  expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es /\
  expr_body_pre cenv cx env a es /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  expr_type a = BaseT AddressT /\
  slice_operands_ok (Slice n) [Builtin ct (Acc Code) [a];start;len] /\
  exprs_case nocalls ctx func cenv cx [start;len] /\
  ((?s vs t. eval_exprs cx [start;len] s = (INL vs,t)) ==>
    expr_sim_case nocalls ctx func cenv cx a) /\
  (nocalls ==> int_calls_expr start = [] /\ int_calls_expr len = [] /\ int_calls_expr a = []) ==>
  expr_vv_sim ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
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

Resume slice_extcode_typed_entry[reads]:
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def,
        allocLimitsTheory.type_alloc_ok_def, compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def]) >>
  qpat_x_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ _` kall_tac >>
  qpat_x_assum `!xs. ~names_builtin _ xs` kall_tac >>
  qpat_x_assum `~is_self_code _` kall_tac >>
  `expr_sim ctx func cenv cx ty start es` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `nocalls` >> fs[exprs_case_def]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[slice_extcode_actions] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `start_op`, `sa`, `st1`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >> suspend "length"
QED

Resume slice_extcode_typed_entry[length]:
  `?gs. bind (eval_expr cx start) (read_result cx) (es with gas_obs := gs) =
    (INL v,mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_case nocalls ctx func cenv cx len` by
    (fs[exprs_case_def] >>
     qpat_x_assum `(_ ==> expr_sim_case _ _ _ _ _ len /\ _)` mp_tac >>
     impl_tac >- (qpat_x_assum `bind _ _ _ = (INL _,_)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> metis_tac[]) >> simp[]) >>
  drule_all slice_uint_read_post >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env len (mid with gas_obs := [])` by
    gvs[expr_body_pre_def] >>
  `expr_sim ctx func cenv cx ty len (mid with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac >- (qexists_tac `env` >> fs[]) >>
     qexists_tac `nocalls` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by metis_tac[expr_body_pre_gas_admissible] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  `~t.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  irule slice_read_outcome_bind >> simp[] >>
  qexistsl_tac [`cenv`, `len_op`, `st1`, `st2`, `ty`] >> gvs[] >>
  rpt gen_tac >> strip_tac >> suspend "address"
QED

Resume slice_extcode_typed_entry[address]:
  `?s vs t. eval_exprs cx [start;len] s = (INL vs,t)` by
    (irule slice_two_marked_reads_success >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any)) >>
  `expr_sim_case nocalls ctx func cenv cx a` by metis_tac[] >>
  qpat_x_assum `exprs_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `(_ ==> expr_sim_case _ _ _ _ _ a)` kall_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ start _` kall_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ len _` kall_tac >>
  qpat_x_assum `gas_admissible _ _ es` kall_tac >>
  qpat_x_assum `gas_admissible _ _ mid` kall_tac >>
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
  `~t'.vs_halted` by metis_tac[slice_marked_read_ok_not_halted] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` kall_tac >>
  gvs[] >>
  `k <= n` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >> drule slice_literal_read_length >> intLib.ARITH_TAC) >>
  `expr_body_pre cenv cx env a (mid' with gas_obs := [])` by
    gvs[expr_body_pre_def] >>
  `stmt_state_rel ctx func cenv cx (mid' with gas_obs := []) t'` by
    metis_tac[expr_post_state] >>
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
  qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` kall_tac >>
  qpat_x_assum `bind _ _ (mid with gas_obs := gs2) = _` kall_tac >>
  qpat_x_assum `slice_operands_ok _ _` kall_tac >>
  `!op. MEM op [start_op;len_op] ==>
    (?w. op = Lit w) \/ (?x. op = Var x /\ not_fresh_at st2 x)` by
    (Cases_on `start_op` >> Cases_on `len_op` >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def]) >>
  Cases_on `compile_slice_extcode addr_op start_op len_op out_buf out_data st4` >>
  gvs[as_ptr_val_def] >>
  suspend "finish"
QED

Resume slice_extcode_typed_entry[finish]:
  `q = out_buf` by metis_tac[slice_extcode_shape] >> gvs[] >>
  `fn_has_code st2 r func` by
    (irule fragExecTheory.fn_has_code_mid >>
     fs[ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, compileEnvTheory.cs_extends_refl]) >>
  `nocalls ==> int_calls_expr a = []` by metis_tac[] >>
  irule slice_gas_outcome_conseq >>
  qexistsl_tac [
    `\res ee z. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len])
        (mid' with gas_obs := []) st2 r t' ee tv
        (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out_buf LocMemory)) z /\
      z.vs_current_bb = r.cs_current_bb /\ z.vs_inst_idx = LENGTH r.cs_current_insts`,
    `\res ee rr. expr_exit res rr`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule (slice_two_operand_post_rebase |> SPEC_ALL |> Q.INST
        [`sd` |-> `st1`, `se` |-> `st2`,
         `e1` |-> `mid with gas_obs := []`, `e2` |-> `mid' with gas_obs := []`]) >>
      qpat_assum `expr_post _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
      fs[ci_mono_def] >> metis_tac[]) >>
  irule (slice_extcode_continue_entry_seq |> SPEC_ALL |> Q.INST
    [`result` |-> `Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin ct (Acc Code) [a];start;len]`,
     `a` |-> `a`] |> SRULE [expr_type_def]) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (qpat_assum `compile_slice_out_buf _ _ = _` (irule_at Any) >>
      qpat_assum `compile_slice_extcode _ _ _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `lower_value _ _ _ a _ = _` (irule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `nocalls` >> simp[]
QED

Finalise slice_extcode_typed_entry
