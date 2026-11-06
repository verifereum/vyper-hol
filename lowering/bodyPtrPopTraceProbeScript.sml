Theory bodyPtrPopTraceProbe
Ancestors
  bodyPtrPopSourceEval bodyPtrPopGlobalUnit bodyPtrPopGlobalLoweringInputs
  bodyPtrPopGlobalLegality bodyPtrPopGlobalSource bodyPtrDefs
  exprLowering context venomExecSemantics ptrSafeRun ptrDiscipline
  venomState venomInst finite_map vyperValue

(* Named concrete compiler output and initial state bound executable trace
   probes; these are fixtures, not replacement semantic predicates. *)
Definition pop_trace_compiled_def:
  pop_trace_compiled = SND (compile_expr pop_global_package_env
    (BaseT (UintT 256)) (Pop (BaseT (UintT 256)) pop_global_target)
    (initial_compile_state "probe"))
End
Definition pop_trace_fn_def:
  pop_trace_fn = mk_raw_function "probe"
    (REVERSE pop_trace_compiled.cs_blocks ++
     [<|bb_label := pop_trace_compiled.cs_current_bb;
        bb_instructions := pop_trace_compiled.cs_current_insts ++
                           [mk_inst 1000 STOP [] []]|>])
End
Definition pop_trace_start_def:
  pop_trace_start = sstore 0w 1w (sstore 1w 1w
    (sstore 2w 1w (sstore 3w 7w (init_venom_state "probe"))))
End
Definition pop_trace_taint_def:
  pop_trace_taint = entry_taint with t_stor := {(6w,0)}
End

Theorem pop_trace_aborts:
  ?s. run_from 100 pop_global_runtime_context pop_trace_fn pop_trace_start =
      Abort Revert_abort s /\ sload 0w s = 0w /\ sload 1w s = 0w /\
      sload 2w s = 0w /\ sload 3w s = 0w
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[]
QED
