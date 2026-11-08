Theory bodyPtrBytestringBuiltinsSignedProgram
Ancestors
  bodyPtrBytestringBuiltinsSignedFrame bodyPtrBytestringBuiltinsActualUnit
  compileVyper

(* Actual source program for the replacement installation probe. *)
Definition signed_program_tops_def:
  signed_program_tops =
    [FunctionDecl External Nonpayable F F "probe"
      [("b", BaseT (BytesT (Dynamic 1)))] []
      (BaseT (BytesT (Dynamic 1))) [Return (SOME signed_frame_expr)]]
End

Definition signed_program_base_env_def:
  signed_program_base_env = build_compile_env signed_program_tops External
    Nonpayable "probe" [("b", BaseT (BytesT (Dynamic 1)))]
    (BaseT (BytesT (Dynamic 1))) [Return (SOME signed_frame_expr)] F
End

Definition signed_program_env_def:
  signed_program_env = signed_program_base_env with
    <|ce_ret_enc_info := AbiComplex [(AbiBytestring 1,32,64,T)];
      ce_ret_dec_info := DecBytestring 1; ce_max_return_size := 96|>
End

Theorem signed_program_package:
  set_external_package_target order_frame_policy.rpol_target
    (package_external_fn signed_program_tops F (assign_nkeys signed_program_tops 0)
      (Nonpayable,F,F,"probe",[("b", BaseT (BytesT (Dynamic 1)))],[],
       BaseT (BytesT (Dynamic 1)),[Return (SOME signed_frame_expr)])) =
  ("fn_probe", signed_program_env,
   [("b",F,T,32,DecBytestring 1)],36,F,F,0,F,F,
   [Return (SOME signed_frame_expr)],SOME (BaseT (BytesT (Dynamic 1))))
Proof
  rewrite_tac[signed_program_env_def, signed_program_base_env_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

Theorem signed_program_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit signed_program_tops order_frame_policy)
Proof
  simp[lower_vyper_runtime_unit_def, signed_program_tops_def,
       classify_functions_def, classify_function_def, fn_allocs_ok_def,
       allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def,
       signed_frame_static] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

(* Extract the actual cursor immediately after positional argument decoding. *)
Definition signed_program_cursor_def:
  signed_program_cursor =
    (do fb <- fresh_label "fallback";
        compile_selector_dispatch_linear
          (MAP (\(sel,lbl,z). (sel,lbl))
            [compute_selector (type_env signed_program_tops) "probe"
              [BaseT (BytesT (Dynamic 1))]]) fb;
        new_block "fn_probe";
        compile_entry_checks 36 F;
        compile_register_positional_args signed_program_env
          [("b",F,T,32,DecBytestring 1)] 4
     od) (initial_compile_state "__entry")
End

Theorem signed_program_cursor_local:
  FLOOKUP (FST signed_program_cursor).ce_vars "b" = SOME (PtrVar (Var "%11") 64)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

(* The unit and function are extracted from lowering, never hand-installed. *)
Definition signed_program_unit_def:
  signed_program_unit = THE (lower_vyper_runtime_unit signed_program_tops order_frame_policy)
End

Definition signed_program_fn_def:
  signed_program_fn = HD signed_program_unit.cu_context.ctx_functions
End

Definition signed_program_expr_compiled_def:
  signed_program_expr_compiled = lower_value compile_expr
    (FST signed_program_cursor) (BaseT (BytesT (Dynamic 1))) signed_frame_expr
    (SND signed_program_cursor)
End

Theorem signed_program_lowering:
  lower_vyper_runtime_unit signed_program_tops order_frame_policy = SOME signed_program_unit
Proof
  mp_tac signed_program_lowering_exists >>
  Cases_on `lower_vyper_runtime_unit signed_program_tops order_frame_policy` >>
  simp[signed_program_unit_def]
QED

Theorem signed_program_code_installed:
  fn_has_code (SND signed_program_cursor) (SND signed_program_expr_compiled) signed_program_fn
Proof
  simp[signed_program_fn_def, signed_program_unit_def,
       lower_vyper_runtime_unit_def, signed_program_tops_def,
       classify_functions_def, classify_function_def, fn_allocs_ok_def,
       allocLimitsTheory.alloc_limits_stmt_def, allocLimitsTheory.alloc_limits_expr_def,
       signed_frame_static] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp_tac bool_ss [] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp_tac bool_ss []
QED

Theorem signed_program_cursor_position:
  (SND signed_program_cursor).cs_current_bb = "fn_probe" /\
  LENGTH (SND signed_program_cursor).cs_current_insts = 16 /\
  (SND signed_program_cursor).cs_next_id = 26 /\
  (SND signed_program_cursor).cs_next_var = 18
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem signed_program_expr_prefix:
  DROP 16 (TAKE 22 (SND signed_program_expr_compiled).cs_current_insts) =
    [mk_inst 26 MLOAD [Var "%11"] ["%18"];
     mk_inst 27 ADD [Var "%11"; Lit 32w] ["%19"];
     mk_inst 28 MLOAD [Var "%19"] ["%20"];
     mk_inst 29 ISZERO [Var "%18"] ["%21"];
     mk_inst 30 ISZERO [Var "%21"] ["%22"];
     mk_inst 31 MUL [Var "%20"; Var "%22"] ["%23"]]
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED
