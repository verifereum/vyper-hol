(*
 * Expression simulation: len(msg.data) (#636, Builtins row 1)
 *
 * len(msg.data) is the builtin CalldataLen, which the lowering emits as one
 * CALLDATASIZE.  Venom reads the length of cc_calldata, which call_ctx_rel
 * makes the transaction's calldata, the bytes the source measures; so the
 * case is compile_env_sim's (exprSim) with one more read.
 *
 * TOP-LEVEL:
 *   compile_calldatasize_sim — expr_vv_ok of CalldataLen
 *
 * Also exported: lower_value_calldata_len, compile_calldata_len_stack,
 *   eval_expr_calldata_len.  Local: names_builtin_calldata_len,
 *   compile_calldata_len_dispatch.
 *)

Theory exprSimCalldata
Ancestors
  exprSimProps
  exprSimHypsDefs
  exprSimValues
  loweringPosts
  list fragExec loweringSlice exprSimStack gasNormalPrefix gasSummary gasContext fragGasMode fragGasPath
  exprBopLowering exprLowering exprLoweringProps builtinSimple emitHelper
  compileEnv loweringStateRelDefs valueEncoding emitHelperProps
  venomExecSemantics venomInst venomState vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeSystem

Theorem names_builtin_calldata_len[local]:
  !args. ~names_builtin CalldataLen args
Proof
  `!bt args. names_builtin bt args ==> bt <> CalldataLen` suffices_by
    metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED

Theorem compile_calldata_len_dispatch[local]:
  !cenv ty ann args sa.
    compile_expr cenv ty (Builtin ann CalldataLen args) sa =
    as_stack_val ann (compile_builtin_calldatasize sa)
Proof
  rpt gen_tac >>
  simp[compile_expr_builtin_dispatch, names_builtin_calldata_len] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def]
QED

Theorem compile_calldata_len_stack:
  !cenv ty ann args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann CalldataLen args) sa =
              (StackValue t op, sb)
Proof
  simp[compile_calldata_len_dispatch, as_stack_val_pair]
QED

Theorem lower_value_calldata_len:
  !cenv ty ann args sa.
    lower_value compile_expr cenv ty (Builtin ann CalldataLen args) sa =
    emit_op CALLDATASIZE [] sa
Proof
  rpt gen_tac >>
  simp[lower_value_def, comp_bind_def, compile_calldata_len_dispatch,
       compile_builtin_calldatasize_def] >>
  Cases_on `emit_op CALLDATASIZE [] sa` >>
  simp[as_stack_val_def, unwrap_value_def, comp_return_def]
QED

Theorem eval_expr_calldata_len:
  !cx ann es res es'.
    eval_expr cx (Builtin ann CalldataLen []) es = (res, es') ==>
    es' = es /\ res = INL (Value (IntV &LENGTH cx.txn.calldata))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
       builtin_args_length_ok_def] >>
  simp[Once evaluate_def, return_def, evaluate_builtin_def] >>
  rw[] >> gvs[]
QED

Theorem calldata_source_all_tails:
  !cx es tail.
    bind (eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen []))
      (read_result cx) (es with gas_obs := tail) =
    (INL (IntV &LENGTH cx.txn.calldata), es with gas_obs := tail)
Proof
  rpt gen_tac >>
  Cases_on `eval_expr cx (Builtin (BaseT (UintT 256)) CalldataLen [])
    (es with gas_obs := tail)` >>
  drule eval_expr_calldata_len >> strip_tac >>
  gvs[bind_def, read_result_def, return_def]
QED

Theorem calldata_target_prefix:
  lower_value compile_expr cenv ty (Builtin (BaseT (UintT 256)) CalldataLen []) sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path ctx func s0 0 (OK t) /\
      expr_post ctx func cenv cx (Builtin (BaseT (UintT 256)) CalldataLen [])
        es sa sb s0 (es with gas_obs := [])
        (IntV &LENGTH cx.txn.calldata) op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> gvs[lower_value_calldata_len] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id CALLDATASIZE [] [out]) s0 =
     OK (update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s0)` by
    (simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
        val_to_w256_def, integer_wordTheory.i2w_def]) >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qexists_tac `update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s0
                with vs_inst_idx := SUC s0.vs_inst_idx` >>
  conj_tac
  >- (`CALLDATASIZE <> GAS /\ CALLDATASIZE <> INVOKE /\
       ~is_terminator CALLDATASIZE` by simp[is_terminator_def] >>
      drule_all emit_op_zero_path >> simp[Abbr `out`]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `stmt_state_rel ctx func cenv cx es
      (update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  drule msg_gas_state_frame >>
  disch_then (qspecl_then [
    `(update_var out (val_to_w256 (IntV &LENGTH cx.txn.calldata)) s0).vs_gas_readings`,
    `SUC s0.vs_inst_idx`, `[]`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def, locals_kept_mem,
       stmt_state_rel_inst_idx, update_var_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, Abbr `out`] >>
  rpt strip_tac >> metis_tac[]
QED

(* len(msg.data): one CALLDATASIZE, whose word is the length of the
   transaction's calldata (call_ctx_rel), as a uint256. *)
Theorem compile_calldatasize_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann CalldataLen args)
Proof
  rpt strip_tac >>
  `expr_ok cenv (Builtin ann CalldataLen args)` suffices_by
    simp[expr_ok_def] >>
  irule expr_ok_stack >> rpt conj_tac
  >- metis_tac[eval_expr_builtin_value]
  >- simp[compile_calldata_len_stack] >>
  rw[expr_sim_ok_def] >>
  `args = [] /\ ann = BaseT (UintT 256)` by
    gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >>
  irule expr_sim_values >> rpt strip_tac >>
  `?t. gas_path ctx func s0 0 (OK t) /\
       expr_post ctx func cenv cx (Builtin (BaseT (UintT 256)) CalldataLen [])
         es sa sb s0 (es with gas_obs := [])
         (IntV &LENGTH cx.txn.calldata) op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    metis_tac[calldata_target_prefix] >>
  qexistsl_tac [`[]`, `IntV &LENGTH cx.txn.calldata`, `es`, `t`] >>
  simp[gas_value_prefix_def, gas_marked_exec_def, gas_marked_path_def,
       calldata_source_all_tails, GSYM ETA_THM]
QED

