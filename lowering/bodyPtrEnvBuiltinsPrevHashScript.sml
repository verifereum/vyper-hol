(* PrevHash source and clean scalar sequence boundaries. *)
Theory bodyPtrEnvBuiltinsPrevHash
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsGas bodyPtrEnvBuiltinsScalarCompose
  bodyPtrEnvBuiltinsEdges bodyPtrDefs exprLoweringProps exprSimAccounts
  fragGasPathPtr fragExec ptrDiscipline compileEnv exprLowering
  vyperInterpreter vyperContext vyperState vyperValue vyperTypeSystem
  exprSimProps emitHelper emitHelperProps builtinProps gasSummary
  venomState venomInst venomExecSemantics finite_map list rich_list
  valueEncoding exprSimUnopProps exprSimPrecompiles loweringPosts
  bodyPtrPreds exprPtrUnwrap exprSimHypsDefs gasSummary exprSimEnv
  stmtFragPtr exprSimWordArgs vyperAST

Theorem prevhash_source_all_tails:
  tx_env_ok cx.txn ==>
  !tail. bind (eval_expr cx (Builtin (env_item_type PrevHash) (Env PrevHash) []))
    (read_result cx) (es with gas_obs := tail) =
    (INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))),
     es with gas_obs := tail)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def, read_result_def] >>
  simp[Once evaluate_def, bind_def, read_result_def, return_def,
       evaluate_builtin_def, tx_env_ok_evaluate_prevhash]
QED

Theorem prevhash_emit_decompose:
  compile_env_var PrevHash sa = (op,sb) ==>
  ?num sm prev sn.
    emit_op NUMBER [] sa = (num,sm) /\
    emit_op SUB [num; Lit 1w] sm = (prev,sn) /\
    emit_op BLOCKHASH [prev] sn = (op,sb)
Proof
  simp[compile_env_var_def, comp_bind_def] >>
  Cases_on `emit_op NUMBER [] sa` >>
  Cases_on `emit_op SUB [q; Lit 1w] r` >> simp[]
QED

Theorem prevhash_context_read:
  stmt_state_rel ctx fn cenv cx es s /\
  stmt_state_rel ctx fn cenv cx es t ==>
  t.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w)) =
  s.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w))
Proof
  strip_tac >>
  `call_ctx_rel cx.txn s.vs_call_ctx s.vs_tx_ctx s.vs_block_ctx /\
   call_ctx_rel cx.txn t.vs_call_ctx t.vs_tx_ctx t.vs_block_ctx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `t.vs_block_ctx.bc_number = s.vs_block_ctx.bc_number` by
    gvs[call_ctx_rel_def] >>
  metis_tac[call_ctx_rel_prevhash]
QED

Theorem prevhash_counted_run:
  compile_env_var PrevHash sa = (op,sb) /\ fn_has_code sa sb fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME
      (s.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w))) /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule prevhash_emit_decompose >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb` by
    metis_tac[emit_op_extends_next_var] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn /\ fn_has_code sn sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_rel fn cenv es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s)` by simp[gas_path_ptr_rules] >>
  `cs_extends sa sa` by simp[cs_extends_refl] >>
  `sa.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sa.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x s = lookup_var x s) /\
    s.vs_memory = s.vs_memory /\ s.vs_allocas = s.vs_allocas` by simp[] >>
  `step_inst_base (mk_inst sa.cs_next_id NUMBER []
      [STRING #"%" (toString sa.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString sa.cs_next_var))
      s.vs_block_ctx.bc_number s)` by
    simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
  qpat_assum `emit_op NUMBER [] sa = _`
    (mp_then Any mp_tac emit_scalar_builtin_append) >>
  simp[MEM] >> disch_then drule_all >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `!a. MEM a [num; Lit 1w] ==> op_taint tn1 a = {}` by
    (rpt strip_tac >> gvs[op_taint_def]) >>
  `step_inst_base (mk_inst sm.cs_next_id SUB [num; Lit 1w]
    [STRING #"%" (toString sm.cs_next_var)]) s1 =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
      (s.vs_block_ctx.bc_number - 1w) s1)` by
    simp[step_inst_base_opcode_eqs, exec_pure2_def, mk_inst_def,
         eval_operands_def, eval_operand_def] >>
  qpat_assum `emit_op SUB _ sm = _`
    (mp_then Any mp_tac emit_scalar_builtin_append) >>
  gvs[MEM] >> disch_then drule_all >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `!a. MEM a [prev] ==> op_taint tn2 a = {}` by simp[] >>
  `s2.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w)) =
    s.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w))` by
    metis_tac[prevhash_context_read] >>
  `step_inst_base (mk_inst sn.cs_next_id BLOCKHASH [prev]
    [STRING #"%" (toString sn.cs_next_var)]) s2 =
    OK (update_var (STRING #"%" (toString sn.cs_next_var))
      (s.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w))) s2)` by
    simp[step_inst_base_opcode_eqs, exec_read1_def, mk_inst_def, eval_operands_def] >>
  qpat_assum `emit_op BLOCKHASH _ sn = _`
    (mp_then Any mp_tac emit_scalar_builtin_append) >>
  gvs[MEM] >> disch_then drule_all >>
  disch_then strip_assume_tac >> metis_tac[]
QED

Theorem prevhash_stack_encoding:
  typed_val_to_w256 (BaseTV (BytesT (Fixed 32)))
    (BytesV (word_to_bytes_be (w:bytes32))) = w
Proof
  simp[typed_val_to_w256_def, PAD_RIGHT, length_word_to_bytes_be,
       word_of_bytes_be_to_bytes]
QED

Theorem prevhash_counted_post:
  lower_value compile_expr cenv ty (Builtin (env_item_type PrevHash) (Env PrevHash) []) sa = (op,sb) /\
  fn_has_code sa sb fn /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx fn cenv cx (Builtin (env_item_type PrevHash) (Env PrevHash) [])
      es sa sb s (es with gas_obs := [])
      (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))) op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx (env_item_type PrevHash)
      (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes))) op G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >> drule lower_value_env >> strip_tac >>
  drule_all prevhash_counted_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `s.vs_block_ctx.bc_blockhash (w2n (s.vs_block_ctx.bc_number - 1w)) =
    EL 0 cx.txn.block_hashes` by
    (simp[EL] >> irule call_ctx_rel_prevhash >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def, env_item_type_def, is_word_type_def] >>
  irule expr_post_typed_stack_intro >>
  simp[expr_type_def, env_item_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, prevhash_stack_encoding] >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sa`, `s`] >> simp[wb_frame_refl]
QED

Theorem compile_prevhash_sim_ptr:
  expr_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rw[expr_sim_ptr_def] >>
  drule_all prevhash_counted_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `tx_env_ok cx.txn` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BytesV (word_to_bytes_be (EL 0 cx.txn.block_hashes)))`,
    `es`, `G'`, `tn'`, `OK t`] >>
  simp[gas_explicit_def, expr_type_def, env_item_type_def, is_word_type_def,
       prevhash_source_all_tails] >> gvs[env_item_type_def, EL]
QED

Theorem compile_prevhash_vv_sim_ptr:
  expr_vv_sim_ptr d ctx PG fn cenv cx ty
    (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  irule expr_vv_sim_ptr_stack >> conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var PrevHash sa` >> simp[as_stack_val_def]) >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  simp[compile_prevhash_sim_ptr]
QED

Theorem body_prevhash_ptr_case:
  body_expr_ptr_ok cx (Builtin ann (Env PrevHash) args)
Proof
  rw[body_expr_ptr_ok_def] >>
  `args = [] /\ ann = env_item_type PrevHash` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> simp[compile_prevhash_sim_ptr, compile_prevhash_vv_sim_ptr]
QED
