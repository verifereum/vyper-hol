(* PrevHash source and clean scalar sequence boundaries. *)
Theory bodyPtrEnvBuiltinsPrevHash
Ancestors
  bodyPtrEnvBuiltinsScalar bodyPtrEnvBuiltinsGas compileEnv exprLowering
  vyperInterpreter vyperContext vyperState vyperValue vyperTypeSystem
  exprSimProps emitHelper emitHelperProps builtinProps gasSummary
  venomState venomInst venomExecSemantics finite_map list rich_list

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
