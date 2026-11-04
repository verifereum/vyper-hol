Theory externalReturnSizeProbe
Ancestors
  compileVyper compileEnv exprLowering vyperTypeSystem vyperValue
  vyperAST words

Theorem external_return_capacity_wrap[local]:
  (update_cenv_ret_abi ce
    (BaseT (BytesT (Dynamic (2 ** 256 - 64))))).ce_max_return_size =
    2 ** 256
Proof
  simp[update_cenv_ret_abi_def, abi_size_bound_def,
       is_abi_dynamic_def, external_return_needs_wrap_cases] >>
  EVAL_TAC
QED

Theorem external_return_capacity_word_zero[local]:
  (n2w (2 ** 256) : 256 word) = 0w
Proof
  CONV_TAC wordsLib.WORD_CONV
QED

Theorem external_return_large_bytes_type_valid[local]:
  well_formed_type tenv (BaseT (BytesT (Dynamic (2 ** 256 - 64))))
Proof
  simp[well_formed_type_def, evaluate_type_def, type_slot_size_def] >>
  EVAL_TAC
QED

Theorem external_return_large_bytes_accepts_empty[local]:
  type_stmt env (BaseT (BytesT (Dynamic (2 ** 256 - 64))))
    (Return (SOME (Literal (BaseT (BytesT (Dynamic 1))) (BytesL [])))) =
    SOME env
Proof
  simp[type_stmt_def, well_typed_expr_def, well_typed_literal_def,
       type_widens_to_def, arg_type_fits_def,
       external_return_large_bytes_type_valid, expr_type_def,
       well_formed_type_def, evaluate_type_def, type_slot_size_def] >>
  EVAL_TAC
QED

(* The complete-unit boundary rejects this candidate independently of its
   locally valid source typing and wrapped ABI allocation arithmetic. *)
Theorem external_return_large_bytes_rejected[local]:
  ~fn_allocs_ok tops
    (mut, nr, rr, fname, fargs, dflts,
     BaseT (BytesT (Dynamic (2 ** 256 - 64))), fbody)
Proof
  simp[fn_allocs_ok_def, type_memory_bytes_def] >>
  EVAL_TAC
QED
