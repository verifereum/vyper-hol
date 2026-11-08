Theory bodyPtrBytestringBuiltinsSupportedHostProbe
Ancestors
  bodyPtrBytestringBuiltinsSignedProgram supportedProgram
  bodyPtrBytestringBuiltinsSignedTailProbe bodyPtrBytestringBuiltinsSourceFrame
  compileVyper

(* Finite alternative host fixture; unlike SignedProgram it contains no Slice. *)
Definition supported_host_tops_def:
  supported_host_tops =
    [FunctionDecl External Nonpayable F F "probe"
      [("b", BaseT (BytesT (Dynamic 1)))] [] (BaseT (UintT 256))
      [Return (SOME signed_tail)]]
End

Theorem supported_host_supported:
  supported_program supported_host_tops
Proof
  EVAL_TAC
QED

Theorem supported_host_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit supported_host_tops order_frame_policy)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

(* Fresh return ABI metadata computed from this host, not the bytes return. *)
Definition supported_host_env_def:
  supported_host_env = update_cenv_ret_abi
    (build_compile_env supported_host_tops External Nonpayable "probe"
      [("b", BaseT (BytesT (Dynamic 1)))] (BaseT (UintT 256))
      [Return (SOME signed_tail)] F) (BaseT (UintT 256))
End

Theorem supported_host_package:
  set_external_package_target order_frame_policy.rpol_target
    (package_external_fn supported_host_tops F (assign_nkeys supported_host_tops 0)
      (Nonpayable,F,F,"probe",[("b", BaseT (BytesT (Dynamic 1)))],[],
       BaseT (UintT 256),[Return (SOME signed_tail)])) =
  ("fn_probe", supported_host_env, [("b",F,T,32,DecBytestring 1)],
   36,F,F,0,F,F,[Return (SOME signed_tail)],SOME (BaseT (UintT 256)))
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def]
QED

Definition supported_host_cursor_def:
  supported_host_cursor =
    (do fb <- fresh_label "fallback";
        compile_selector_dispatch_linear
          (MAP (\(sel,lbl,z). (sel,lbl))
            [compute_selector (type_env supported_host_tops) "probe"
              [BaseT (BytesT (Dynamic 1))]]) fb;
        new_block "fn_probe";
        compile_entry_checks 36 F;
        compile_register_positional_args supported_host_env
          [("b",F,T,32,DecBytestring 1)] 4
     od) (initial_compile_state "__entry")
End

Definition supported_host_fn_def:
  supported_host_fn = HD
    (THE (lower_vyper_runtime_unit supported_host_tops order_frame_policy)).cu_context.ctx_functions
End

Definition supported_host_slice_compiled_def:
  supported_host_slice_compiled = lower_value compile_expr
    (FST supported_host_cursor) (BaseT (BytesT (Dynamic 1)))
    signed_frame_expr (SND supported_host_cursor)
End

Theorem supported_host_slice_block_too_short:
  !bb. lookup_block (SND supported_host_slice_compiled).cs_current_bb
         supported_host_fn.fn_blocks = SOME bb ==>
       LENGTH bb.bb_instructions <
         LENGTH (SND supported_host_slice_compiled).cs_current_insts
Proof
  simp[supported_host_fn_def, lower_vyper_runtime_unit_def,
       supported_host_tops_def, classify_functions_def, classify_function_def,
       fn_allocs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
       allocLimitsTheory.alloc_limits_expr_def, signed_tail_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem supported_host_slice_not_installed:
  ~fn_has_code (SND supported_host_cursor)
    (SND supported_host_slice_compiled) supported_host_fn
Proof
  strip_tac >> fs[fragExecTheory.fn_has_code_def] >>
  qpat_x_assum `SOME bb = _` (mp_tac o SYM) >>
  disch_then (mp_tac o MATCH_MP supported_host_slice_block_too_short) >>
  imp_res_tac rich_listTheory.IS_PREFIX_LENGTH >> decide_tac
QED
