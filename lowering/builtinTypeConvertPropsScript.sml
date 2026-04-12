Theory builtinTypeConvertProps
Ancestors
  builtinTypeConvert1 builtinTypeConvert2

(* Combine the per-arm theorems from split files *)

Theorem compile_type_convert_correct:
  ∀ v conv_op w ss st op st'.
    compile_type_convert v conv_op st = (op, st') ∧
    eval_operand v ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss' result.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' = SOME result) ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  Cases_on `conv_op` >>
  metis_tac[compile_type_convert_1, compile_type_convert_2,
            compile_type_convert_3, compile_type_convert_4,
            compile_type_convert_5, compile_type_convert_6,
            compile_type_convert_7, compile_type_convert_8,
            compile_type_convert_9, compile_type_convert_10,
            compile_type_convert_11, compile_type_convert_12,
            compile_type_convert_13, compile_type_convert_14,
            compile_type_convert_15, compile_type_convert_16,
            compile_type_convert_17, compile_type_convert_18,
            compile_type_convert_19, compile_type_convert_20]
QED
