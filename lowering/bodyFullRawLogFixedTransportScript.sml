Theory bodyFullRawLogFixedTransport
Ancestors
  bodyFullRawLogFixedBoundary bodySimFull bodyPtrDefs exprSimDefs
  exprSimMemDefs exprLoweringProps stmtSimDefs loweringPosts
  exprSimWordArgs exprOperandVar vyperValue venomState words list
  finite_map pred_set bodyRawLogArgPre exprSimSource vyperTyping vyperState
  valueEncoding valueEncodingProofs compileEnv loweringStateRelDefs

Theorem raw_log_fixed_child_tail_input:
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es0 /\
  MEM data args /\ expr_sim_inv cenv cx env es /\
  bind (eval_expr cx data) (read_result cx)
    (es with gas_obs := input_gas) =
    (INL (BytesV bs),mid with gas_obs := output_gas) /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  post_value_type cenv data = expr_type data /\
  evaluate_type (get_tenv cx) (expr_type data) = SOME (BaseTV (BytesT (Fixed 32))) /\
  compile_alloc_buffer 32 sa = (buf,sd) /\
  sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sd /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx es u /\
  buf.buf_operand = Var p /\ not_fresh_at sd p /\
  eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  w2n w + 32 < dimword (:256) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
     regions_disjoint (w2n w) 32 b n) /\
  (!name b n. local_region cenv es.scopes u name b n ==>
     regions_disjoint (w2n w) 32 b n) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
  expr_post H ctx func cenv cx data es sd sm u mid (BytesV bs) data_op t /\
  expr_post H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\
  expr_store_bound cx (expr_type data) (BytesV bs) data_op t /\
  ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G1 tn1 t /\
  ghost_kept_at lo cenv es sd Gu tnu u G1 tn1 /\
  alloca_history func t /\ u.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operands ops s0 = SOME (MAP event_value_to_word vals) /\
  EVERY (\op. op_taint tn0 op = {}) ops /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
              (!l. op <> Label l)) ops ==>
  ?word.
    expr_post H ctx func cenv cx data es sa sm s0 mid (BytesV bs) data_op t /\
    expr_store_bound cx (expr_type data) (BytesV bs) data_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv data) (BytesV bs) data_op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    LENGTH bs = 32 /\ eval_operand data_op t = SOME word /\
    TAKE 32 (word_to_bytes_be word) = bs /\
    buf.buf_operand = Var p /\ eval_operand buf.buf_operand t = SOME w /\
    ptr_covers G1 tn1 p t 32 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\
    (!name b n. local_region cenv mid.scopes t name b n ==>
       regions_disjoint (w2n w) 32 b n) /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
       regions_disjoint (w2n w) 32 b n) /\
    eval_operands ops t = SOME (MAP event_value_to_word vals) /\
    EVERY (\op. op_taint tn1 op = {}) ops /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  `expr_body_pre cenv cx env data es` by
    metis_tac[expr_body_pre_raw_log_arg] >>
  `value_has_type (BaseTV (BytesT (Fixed 32))) (BytesV bs)` by
    (`expr_body_pre cenv cx env data (es with gas_obs := input_gas)` by
       simp[] >>
     Cases_on `eval_expr cx data (es with gas_obs := input_gas)` >>
     rename1 `eval_expr cx data (es with gas_obs := input_gas) = (res,st)` >>
     Cases_on `res` >> gvs[bind_def] >>
     drule read_result_state >> strip_tac >> gvs[] >>
     qpat_x_assum `eval_expr cx data _ = _`
       (mp_then Any mp_tac expr_body_pre_runtime_typed) >>
     simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  `LENGTH bs = 32` by fs[value_has_type_def] >>
  `?word. eval_operand data_op t = SOME word /\
     TAKE 32 (word_to_bytes_be word) = bs` by
    (`expr_val_rel cx (BaseT (BytesT (Fixed 32))) (BytesV bs) data_op t` by
       gvs[expr_post_def] >>
     qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
     simp[expr_val_rel_def, is_word_type_def] >>
     strip_tac >> goal_assum (drule_at Any) >>
     gvs[typed_val_to_w256_def] >>
     `PAD_RIGHT (0w:word8) 32 bs = bs` by simp[PAD_RIGHT] >>
     gvs[] >> qspec_then `bs` mp_tac TAKE_word_to_bytes_be_word_of_bytes_be >>
     simp[]) >>
  qexists `word` >>
  `ptr_covers G1 tn1 p t 32 /\
   FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32)` by
    (irule raw_log_fixed_scratch_post >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `!x v. not_fresh_at sd x /\ lookup_var x u = SOME v ==>
      lookup_var x t = SOME v` by fs[expr_post_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    fs[expr_post_def, locals_kept_def] >>
  `!name b n. local_region cenv mid.scopes t name b n ==>
      local_region cenv es.scopes u name b n` by
    (rpt strip_tac >> irule local_region_kept >>
     conj_tac >- (qexistsl [`mid`,`t`,`sd`] >> simp[]) >>
     metis_tac[]) >>
  `eval_operand buf.buf_operand t = SOME w` by
    (simp[eval_operand_def] >>
     qpat_x_assum `!x v. not_fresh_at sd x /\ _ ==> _`
       (qspecl_then [`p`,`w`] mp_tac) >>
     gvs[eval_operand_def]) >>
  `!name b n. local_region cenv es.scopes u name b n <=>
      local_region cenv es.scopes s0 name b n` by
    (fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (fs[ghost_kept_at_def] >>
     conj_tac >-
       (rpt strip_tac >>
        `aid < sd.cs_next_id` by decide_tac >>
        `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
        `i IN tnu.t_mem` by
          (qpat_x_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _`
             (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
        qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
          (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x t = SOME v` by metis_tac[] >>
  conj_tac >-
    (`!xs ws. EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\
                            (!l. op <> Label l)) xs /\
        eval_operands xs s0 = SOME ws ==> eval_operands xs t = SOME ws` by
       (Induct_on `xs` >> simp[eval_operands_def] >>
        Cases_on `h` >> simp[eval_operand_def, AllCaseEqs()] >>
        rpt strip_tac >> gvs[] >>
        first_x_assum drule >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  fs[EVERY_MEM, ghost_kept_at_def] >> rpt strip_tac >>
  Cases_on `op` >> simp[ptrDisciplineTheory.op_taint_def] >>
  rename1 `MEM (Var x) ops` >>
  `not_fresh_at sa x` by metis_tac[] >>
  `op_taint tn1 (Var x) = op_taint tn0 (Var x)` by metis_tac[] >>
  `op_taint tn0 (Var x) = {}` by metis_tac[] >>
  gvs[ptrDisciplineTheory.op_taint_def]
QED
