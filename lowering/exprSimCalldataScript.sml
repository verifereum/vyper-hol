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
  list fragExec loweringSlice exprSim exprSimHyps exprSimWordBuiltins
  exprBopLowering exprLowering exprLoweringProps builtinSimple emitHelper
  compileEnv valueEncoding
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
  gvs[] >> irule expr_sim_values >> rpt conj_tac
  >~ [`expr_res_ok`] >- metis_tac[eval_expr_calldata_len] >>
  rpt strip_tac >> drule eval_expr_calldata_len >> strip_tac >> gvs[] >>
  gvs[lower_value_calldata_len] >>
  irule frag_exec_conseq >>
  qexistsl_tac [`\s. s = s0 /\ stmt_state_rel func cenv cx es s`,
                `\s. stmt_state_rel func cenv cx es s /\
                     eval_operand op s =
                       SOME (val_to_w256 (IntV &LENGTH cx.txn.calldata)) /\
                     (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                            lookup_var x s = SOME w) /\
                     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                              FLOOKUP s.vs_allocas aid = SOME b) /\
                     s.vs_memory = s0.vs_memory`,
                `\r. F`] >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       vyperASTTheory.expr_type_def, is_word_type_def,
       typed_val_to_w256_word_value, word_value_def] >>
  drule emit_op_frag >> disch_then irule >>
  simp[is_terminator_def] >> rpt strip_tac >>
  simp[step_inst_base_opcode_eqs, exec_read0_def, mk_inst_def] >>
  fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
     val_to_w256_def, integer_wordTheory.i2w_def]
QED
