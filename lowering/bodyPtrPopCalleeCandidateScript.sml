Theory bodyPtrPopCalleeCandidate
Ancestors
  bodyPtrPopGlobalCompile supportedProgram fragExec vyperValue
Libs finite_mapLib computeLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

(* Closed diagnostic abbreviations: this unit has a real effectful caller,
   unlike the excluded global fixture. No simulation premise is assumed. *)
Definition pop_callee_word_def:
  pop_callee_word = BaseT (UintT 256)
End
Definition pop_callee_child_def:
  pop_callee_child = ArrayT pop_callee_word (Dynamic 2)
End
Definition pop_callee_middle_def:
  pop_callee_middle = ArrayT pop_callee_child (Dynamic 2)
End
Definition pop_callee_root_type_def:
  pop_callee_root_type = ArrayT pop_callee_middle (Dynamic 2)
End
Definition pop_callee_index_def:
  pop_callee_index = Call pop_callee_word (IntCall (NONE,"shorten")) [] NONE
End
Definition pop_callee_read_def:
  pop_callee_read = Subscript pop_callee_child
    (Subscript pop_callee_middle
      (TopLevelName pop_callee_root_type (NONE,"b"))
      (Literal pop_callee_word (IntL 1))) pop_callee_index
End
Definition pop_callee_body_def:
  pop_callee_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"b")))
       (TopLevelName pop_callee_root_type (NONE,"replacement"));
     Return (SOME (Literal pop_callee_word (IntL 0)))]
End
Definition pop_callee_tops_def:
  pop_callee_tops =
    [VariableDecl Private Storage "b" pop_callee_root_type (SOME 0);
     VariableDecl Private Storage "replacement" pop_callee_root_type (SOME 20);
     FunctionDecl Internal Nonpayable F F "shorten" [] []
       pop_callee_word pop_callee_body;
     FunctionDecl External Nonpayable F F "__default__" [] [] NoneT
       [Expr pop_callee_read]]
End
Definition pop_callee_target_def:
  pop_callee_target = SubscriptTarget
    (SubscriptTarget (TopLevelNameTarget (NONE,"b"))
       (Literal pop_callee_word (IntL 1))) pop_callee_index
End

Theorem pop_callee_supported:
  supported_program pop_callee_tops
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_callee_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit pop_callee_tops pop_global_policy)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Definition pop_callee_unit_def:
  pop_callee_unit = THE (lower_vyper_runtime_unit pop_callee_tops pop_global_policy)
End
Definition pop_callee_cenv_def:
  pop_callee_cenv = build_compile_env pop_callee_tops External Nonpayable
    "__default__" [] NoneT [Expr pop_callee_read] F
End
Definition pop_callee_start_def:
  pop_callee_start = initial_compile_state "@fallback_0"
End

Theorem pop_callee_real_caller_invokes:
  EXISTS (\fn. EXISTS (\i. i.inst_opcode = INVOKE) (fn_insts fn))
    pop_callee_unit.cu_context.ctx_functions
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

