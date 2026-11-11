(* Range regression checks: the lowered operands, not the AST bound, select
   folding/checks, and a computed bound that is too small fails in both the
   source and the target. Also execute the five corrected fixture ASTs in the
   source. *)
Theory evalCompilerRange
Ancestors
  evalCompilerSubsetState compileVyper stmtLowering vyperCompiler
  vyperInterpreter vyperContext alist integer_word venomExecSemantics
Libs finite_mapLib computeLib wordsLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  (CONJUNCTS vyperInterpreterTheory.evaluate_def))

Definition range_test_opcodes_def:
  range_test_opcodes fty start_e end_e bound =
    let loop = For "i" fty (Range start_e end_e) bound [Pass] in
    let cenv = build_compile_env [] External Nonpayable "foo"
                 [("x", fty)] NoneT [loop] F in
    let cs = SND (compile_stmt cenv NoLoop NoneT loop
                   (initial_compile_state "entry")) in
    MAP (\i. i.inst_opcode)
      (FLAT (MAP (\b. b.bb_instructions) cs.cs_blocks) ++ cs.cs_current_insts)
End

(* Source literals select static lowering. *)
Theorem range_literal_operands_skip_checks:
  range_test_opcodes (BaseT (UintT 256))
    (Literal (BaseT (UintT 256)) (IntL 0))
    (Literal (BaseT (UintT 256)) (IntL 3)) 3 =
  range_test_opcodes (BaseT (UintT 256))
    (Literal (BaseT (UintT 256)) (IntL 0))
    (Literal (BaseT (UintT 256)) (IntL 3)) 0 /\
  FILTER (\opc. opc = SUB \/ opc = ASSERT)
    (range_test_opcodes (BaseT (UintT 256))
      (Literal (BaseT (UintT 256)) (IntL 0))
      (Literal (BaseT (UintT 256)) (IntL 3)) 3) = []
Proof
  EVAL_TAC
QED

(* Source names force SUB plus two checks, even at bound zero. *)
Theorem range_nonliteral_operands_checked:
  FILTER (\opc. opc = SUB \/ opc = ASSERT)
    (range_test_opcodes (BaseT (UintT 256))
      (Literal (BaseT (UintT 256)) (IntL 0))
      (Name (BaseT (UintT 256)) "x") 0) = [SUB; ASSERT; ASSERT] /\
  FILTER (\opc. opc = SUB \/ opc = ASSERT)
    (range_test_opcodes (BaseT (UintT 256))
      (Name (BaseT (UintT 256)) "x")
      (Literal (BaseT (UintT 256)) (IntL 3)) 3) = [SUB; ASSERT; ASSERT] /\
  FILTER (\opc. opc = SUB \/ opc = ASSERT)
    (range_test_opcodes (BaseT (IntT 256))
      (Name (BaseT (IntT 256)) "x")
      (Name (BaseT (IntT 256)) "x") 0) = [SUB; ASSERT; ASSERT] /\
  MEM SGT (range_test_opcodes (BaseT (IntT 256))
      (Name (BaseT (IntT 256)) "x")
      (Name (BaseT (IntT 256)) "x") 0)
Proof
  EVAL_TAC
QED

Definition range_fixture_source_result_def:
  range_fixture_source_result tops fname args =
    FST (call_external NONE []
      (initial_machine_state with
        <| sources := [(0w, [(NONE, tops)])];
           layouts := [(0w, ([((NONE, "counter"), 0)], []))] |>)
      (empty_call_txn with <| function_name := fname; args := args |>))
End

Theorem for_pass_source_result:
  range_fixture_source_result for_pass_program "foo" [] = INL (IntV 1)
Proof
  EVAL_TAC
QED

Theorem for_accum_source_result:
  range_fixture_source_result for_accum_program "foo" [] = INL (IntV 1)
Proof
  EVAL_TAC
QED

Theorem for_continue_source_result:
  range_fixture_source_result for_continue_program "foo" [] = INL (IntV 2)
Proof
  EVAL_TAC
QED

Theorem for_break_source_result:
  range_fixture_source_result for_break_program "foo" [] = INL (IntV 1)
Proof
  EVAL_TAC
QED

Theorem storage_scalar_loop_source_result:
  range_fixture_source_result storage_scalar_loop_program "set_add_in_loop"
    [IntV 4] = INL (IntV 7)
Proof
  EVAL_TAC
QED

Theorem range_empty_endpoint_checked:
  FILTER (\opc. opc = SUB \/ opc = ASSERT)
    (range_test_opcodes (BaseT (UintT 256))
      (TypeBuiltin (BaseT (UintT 256)) Empty (BaseT (UintT 256)) [])
      (Literal (BaseT (UintT 256)) (IntL 2)) 1) = [SUB; ASSERT; ASSERT]
Proof
  EVAL_TAC
QED

Definition range_bound_failure_stmt_def:
  range_bound_failure_stmt = For "i" (BaseT (UintT 256))
    (Range (TypeBuiltin (BaseT (UintT 256)) Empty (BaseT (UintT 256)) [])
           (Literal (BaseT (UintT 256)) (IntL 2))) 1 [Pass]
End

Theorem range_bound_failure_source:
  FST (eval_stmt empty_evaluation_context range_bound_failure_stmt empty_state) =
    INR (Error (RuntimeError "For too long"))
Proof
  EVAL_TAC
QED

Theorem range_bound_failure_target:
  (case run_context 20
    (FST (extract_context "entry"
      (SND (emit_void STOP []
        (SND (compile_stmt
          (build_compile_env [] External Nonpayable "foo" [] NoneT
            [range_bound_failure_stmt] F)
          NoLoop NoneT range_bound_failure_stmt
          (initial_compile_state "entry")))))))
    (init_venom_state "entry") of Abort Revert_abort _ => T | _ => F)
Proof
  EVAL_TAC
QED
