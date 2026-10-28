(* TOP-LEVEL: a checked LOG may read an array before a later argument pops it.
   The source argument list must retain the original array value. *)
Theory vyperEventArgumentLifetime
Ancestors
  vyperInterpreter vyperState vyperValueOperation vyperTypeContract
  stmtLowering exprLowering exprLoweringProps compileEnv context venomState venomExecSemantics
  vyperCompiler finite_map list words
Libs
  vyperCheckContractLib finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset

Definition log_pop_args_def:
  log_pop_args =
    [Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "xs";
     Pop (BaseT (UintT 256)) (NameTarget "xs")]
End

Definition log_pop_source_state_def:
  log_pop_source_state vs = empty_state with scopes :=
    [FEMPTY |+ ("xs", <| assignable := T;
      type := ArrayTV (BaseTV (UintT 256)) (Dynamic 3);
      value := ArrayV (DynArrayV vs) |>)]
End

Theorem log_pop_source_arguments:
  !cx.
    eval_exprs cx log_pop_args (log_pop_source_state [IntV 1; IntV 2]) =
      (INL [ArrayV (DynArrayV [IntV 1; IntV 2]); IntV 2],
       log_pop_source_state [IntV 1])
Proof
  gen_tac >> simp[log_pop_args_def, log_pop_source_state_def,
    evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
    lookup_scopes_val_def, lookup_scopes_def, find_containing_scope_def,
    return_def, materialise_def, type_check_def, lift_option_type_def,
    lift_option_def, lift_sum_def, assign_target_def, assign_subscripts_def,
    set_scopes_def, assign_result_def, pop_element_def, popped_value_def] >>
  EVAL_TAC >> simp[finite_mapTheory.fmap_EXT, FLOOKUP_UPDATE]
QED

Definition log_pop_cenv_def:
  log_pop_cenv = (ARB : compile_env) with
    <| ce_vars := FEMPTY |+ ("xs", MemLoc 256 128);
       ce_var_type := K (SOME (ArrayT (BaseT (UintT 256)) (Dynamic 3))) |>
End

Definition log_pop_compiled_def:
  log_pop_compiled = compile_log_eval_all log_pop_cenv log_pop_args
    (initial_compile_state "entry")
End

Definition log_pop_venom_state_def:
  log_pop_venom_state =
    mstore 320 2w (mstore 288 1w (mstore 256 2w
      ((init_venom_state "entry") with vs_alloca_next := 512)))
End

(* Check the actual emitted argument code, including the snapshot allocation.
   The saved array has length two, the popped value is two, and xs now has
   length one. Inspecting both operands prevents a length-only false positive. *)
Theorem log_pop_compiled_arguments:
  (case run_inst_seq (SND log_pop_compiled).cs_current_insts log_pop_venom_state of
     OK out =>
       (OPTION_MAP (\ptr. (mload (w2n ptr) out,
                          mload (w2n ptr + 32) out,
                          mload (w2n ptr + 64) out))
          (eval_operand (FST (HD (FST log_pop_compiled))) out),
        eval_operand (FST (EL 1 (FST log_pop_compiled))) out,
        mload 256 out)
   | _ => (NONE,NONE,0w)) = (SOME (2w,1w,2w),SOME 2w,1w)
Proof
  EVAL_TAC
QED

Definition log_pop_context_def:
  log_pop_context =
    FST (extract_context "entry"
      (SND (emit_void STOP []
        (SND (compile_stmt
          (log_pop_cenv with ce_event_info := K (SOME
            (123, [ArrayT (BaseT (UintT 256)) (Dynamic 3); BaseT (UintT 256)], [F;F])))
          NoLoop NoneT (Log (NONE,"E") log_pop_args)
          (initial_compile_state "entry"))))))
End

(* Fixed event metadata keeps signature hashing outside this test. Execution
   includes the generated array loop, ABI tuple encoding and physical LOG. *)
Theorem log_pop_emitted_data:
  (case run_function 1000 log_pop_context (HD log_pop_context.ctx_functions)
      log_pop_venom_state of
     Halt out => out.vs_logs =
       [<| logger := 0w; topics := [123w];
           data := FLAT (MAP (\w:bytes32. word_to_bytes w T) [64w;2w;2w;1w;2w]) |>] /\
       mload 256 out = 1w
   | _ => F)
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  PURE_ONCE_REWRITE_TAC [run_blocks_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``run_blocks``]) >>
  EVAL_TAC
QED

val args = rhs (concl (REWRITE_CONV [log_pop_args_def] ``log_pop_args``));
val program =
  ``[(NONE,[EventDecl "E"
      [(("a",ArrayT (BaseT (UintT 256)) (Dynamic 3)),F);
       (("b",BaseT (UintT 256)),F)];
    FunctionDecl External Nonpayable F F "f"
      [("x",ArrayT (BaseT (UintT 256)) (Dynamic 3))] [] NoneT
      [AnnAssign "xs" (ArrayT (BaseT (UintT 256)) (Dynamic 3))
         (Name (ArrayT (BaseT (UintT 256)) (Dynamic 3)) "x");
       Log (NONE,"E") ^args]])] : (num option # toplevel list) list``;
val () = List.app (fn mode =>
  let val th = vyperCheckContractLib.check_contract_conv
        ``check_contract ^mode [] 0w ^program``
  in if optionSyntax.is_some (rhs (concl th)) then
       ignore (save_thm ((if aconv mode ``T`` then "log_pop_deploy_checked"
                         else "log_pop_runtime_checked"), th))
     else raise Fail "LOG array/pop program rejected"
  end) [``F``, ``T``];

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed LOG argument theorem: " ^ name)
  end) (DB.thms "vyperEventArgumentLifetime")
