(* Counted scalar builtin execution and its consumer postconditions. *)
Theory bodyPtrEnvBuiltinsScalar
Ancestors
  bodyPtrEnvBuiltinsBoundary bodyPtrEnvBuiltinsEdges ghostPcTransportPtr
  bodyPtrDefs ptrDiscipline fragGasPathPtr emitHelperProps exprLoweringProps
  emitHelper fragExec compileEnv loweringStateRelDefs codegenRel contextCodegenRel loweringPosts
  venomState venomInst venomExecSemantics finite_map pred_set list rich_list
  exprLowering vyperContext vyperValue valueEncoding valueEncodingProofs
  integer_word words exprSimWordArgs exprSimProps exprSimEnv stmtFragPtr
  vyperAST exprSimPrecompiles vyperTypeSystem gasSummary
  exprPtrUnwrap bodyPtrPreds exprSimHypsDefs exprSimCalldata loweringSlice

Theorem ghost_inv_inst_idx[simp]:
  ghost_inv d cenv cx es G tn (s with vs_inst_idx := k) <=>
  ghost_inv d cenv cx es G tn s
Proof
  Cases_on `d` >- simp[ghost_inv_def, return_buf_ptr_def, stor_taint_ok_def,
                        lookup_var_def] >>
  PairCases_on `x` >>
  simp[ghost_inv_def, ptr_covers_def, return_buf_ptr_def,
       stor_taint_ok_def, lookup_var_def]
QED

Theorem emit_scalar_builtin_run:
  emit_op opc args sa = (op, sb) /\ fn_has_code sa sb fn /\
  MEM opc [CALLER; ADDRESS; CALLVALUE; TIMESTAMP; NUMBER; BLOBBASEFEE;
    GASPRICE; BLOCKHASH; CHAINID; COINBASE; GASLIMIT; BASEFEE; PREVRANDAO;
    ORIGIN; GAS; CALLDATASIZE; BALANCE; EXTCODESIZE; EXTCODEHASH;
    BLOBHASH; ISZERO; SUB; ADD; SHR; SHL] /\
  (!a. MEM a args ==> op_taint tn a = {}) /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc args
    [STRING #"%" (toString sa.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var)) w s) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s (if opc = GAS then 1 else 0) G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\
    (opc <> ADD /\ opc <> SUB ==> op_prov G' op = NONE) /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `~not_fresh_at sa (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def] >>
  drule_all emit_scalar_builtin_counted_suffix >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  drule_all scalar_builtin_update_ghosts >>
  disch_then (qspecl_then [`w`, `args`, `sa.cs_next_id`, `PG`] strip_assume_tac) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es
    (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[stmt_state_rel_inst_idx, update_var_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- (irule scalar_builtin_output_clean >> simp[]) >>
  conj_tac
  >- (strip_tac >> irule scalar_builtin_output_no_prov >> gvs[MEM]) >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem env_builtin_counted_run:
  item <> PrevHash /\ item <> MsgGas /\
  compile_env_var item sa = (op, sb) /\ fn_has_code sa sb fn /\
  evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  ghost_kept cenv es0 sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME (val_to_w256 v) /\
    stmt_state_rel ctx fn cenv cx es t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> Cases_on `item` >>
  gvs[compile_env_var_def, vyperContextTheory.evaluate_builtin_def] >>
  drule emit_scalar_builtin_run >> simp[MEM] >>
  disch_then irule >> simp[] >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
  gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
      val_to_w256_address, val_to_w256_def, integer_wordTheory.i2w_def]
QED

Theorem env_builtin_stack_encoding:
  item <> PrevHash /\ item <> MsgGas /\
  evaluate_builtin cx acc (env_item_type item) (Env item) [] [] = INL v ==>
  is_word_type (env_item_type item) /\
  ?tv. evaluate_type (get_tenv cx) (env_item_type item) = SOME tv /\
       typed_val_to_w256 tv v = val_to_w256 v
Proof
  strip_tac >> Cases_on `item` >>
  gvs[vyperContextTheory.evaluate_builtin_def, env_item_type_def,
      is_word_type_def, vyperValueTheory.evaluate_type_def,
      typed_val_to_w256_def, val_to_w256_def] >>
  simp_tac (srw_ss() ++ wordsLib.SIZES_ss) []
QED

Theorem env_builtin_counted_post:
  item <> PrevHash /\ item <> MsgGas /\
  lower_value compile_expr cenv ty (Builtin (env_item_type item) (Env item) []) sa = (op, sb) /\
  fn_has_code sa sb fn /\
  evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx fn cenv cx (Builtin (env_item_type item) (Env item) [])
      es sa sb s (es with gas_obs := []) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx (env_item_type item) v op G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  drule lower_value_env >> strip_tac >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  drule_all env_builtin_counted_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all env_builtin_stack_encoding >> strip_tac >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def] >>
  irule expr_post_typed_stack_intro >>
  simp[expr_type_def] >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sa`, `s`] >> simp[wb_frame_refl]
QED

Theorem compile_env_sim_ptr:
  item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin ann (Env item) []) es
Proof
  strip_tac >> gvs[] >> rw[expr_sim_ptr_def] >>
  `?v. evaluate_builtin cx es.accounts (env_item_type item) (Env item) [] [] = INL v /\
       !tail. bind (eval_expr cx (Builtin (env_item_type item) (Env item) []))
         (read_result cx) (es with gas_obs := tail) =
           (INL v, es with gas_obs := tail)` by
    metis_tac[PURE_REWRITE_RULE [ETA_THM] env_source_all_tails] >>
  drule_all env_builtin_counted_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all env_builtin_stack_encoding >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL v`, `es`, `G'`, `tn'`, `OK t`] >>
  simp[gas_explicit_def, expr_type_def]
QED

Theorem compile_env_vv_sim_ptr:
  item <> PrevHash /\ item <> MsgGas /\ ann = env_item_type item ==>
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (Builtin ann (Env item) []) es
Proof
  strip_tac >> irule expr_vv_sim_ptr_stack >> conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var item sa` >> simp[as_stack_val_def]) >>
  conj_tac
  >- metis_tac[eval_expr_builtin_value] >>
  irule compile_env_sim_ptr >> simp[]
QED

Theorem body_env_ptr_case:
  item <> PrevHash /\ item <> MsgGas ==>
  body_expr_ptr_ok cx (Builtin ann (Env item) args)
Proof
  strip_tac >> rw[body_expr_ptr_ok_def] >>
  `args = [] /\ ann = env_item_type item` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> metis_tac[compile_env_sim_ptr, compile_env_vv_sim_ptr]
QED

Theorem calldata_counted_post:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
  fn_has_code sa sb fn /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    expr_post ctx fn cenv cx (Builtin (BaseT (UintT 256)) CalldataLen [])
      es sa sb s (es with gas_obs := []) (IntV &LENGTH cx.txn.calldata) op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (es with gas_obs := []) G' tn' t /\
    ptr_val_ok cx (BaseT (UintT 256)) (IntV &LENGTH cx.txn.calldata) op G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >> gvs[lower_value_calldata_len] >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE []
     [STRING #"%" (toString sa.cs_next_var)]) s =
     OK (update_var (STRING #"%" (toString sa.cs_next_var))
       (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s)` by
    (simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
     gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
         val_to_w256_def, integer_wordTheory.i2w_def]) >>
  `ghost_kept cenv es sa G tn s G tn` by simp[ghost_kept_refl] >>
  drule emit_scalar_builtin_run >> simp[MEM] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def, is_word_type_def] >>
  irule expr_post_word_intro >>
  simp[expr_type_def, is_word_type_def, word_value_def] >>
  irule wb_frame_readonly_tail >>
  qexistsl_tac [`sa`, `s`] >> simp[wb_frame_refl]
QED

Theorem compile_calldata_sim_ptr:
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin (BaseT (UintT 256)) CalldataLen []) es
Proof
  rw[expr_sim_ptr_def] >>
  drule_all calldata_counted_post >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (IntV &LENGTH cx.txn.calldata)`, `es`, `G'`, `tn'`, `OK t`] >>
  simp[gas_explicit_def, expr_type_def, is_word_type_def, calldata_source_all_tails]
QED

Theorem compile_calldata_vv_sim_ptr:
  expr_vv_sim_ptr d ctx PG fn cenv cx ty (Builtin (BaseT (UintT 256)) CalldataLen []) es
Proof
  irule expr_vv_sim_ptr_stack >>
  simp[compile_calldata_len_stack, compile_calldata_sim_ptr] >>
  metis_tac[eval_expr_builtin_value]
QED

Theorem body_calldata_ptr_case:
  body_expr_ptr_ok cx (Builtin ann CalldataLen args)
Proof
  rw[body_expr_ptr_ok_def] >>
  `args = [] /\ ann = BaseT (UintT 256)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> simp[compile_calldata_sim_ptr, compile_calldata_vv_sim_ptr]
QED
