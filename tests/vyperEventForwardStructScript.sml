(* TOP-LEVEL: event data containing a forward-declared nested struct must use
   the evaluated field footprint, independently of declaration order. *)
Theory vyperEventForwardStruct
Ancestors
  compileVyper compileEnv vyperContext vyperValue vyperTypeContract
  stmtLowering exprLowering exprLoweringProps context vyperCompiler
  venomState venomExecSemantics finite_map list words
Libs
  vyperCheckContractLib finite_mapLib

val () = computeLib.upd_compset add_finite_map_compset

Definition forward_struct_tops_def:
  forward_struct_tops =
    [StructDecl "Outer" [("inner",StructT (NONE,"Inner"))];
     StructDecl "Inner" [("x",BaseT (UintT 256))];
     EventDecl "E" [(("a",StructT (NONE,"Outer")),F)];
     FunctionDecl External Nonpayable F F "f" [("x",StructT (NONE,"Outer"))] [] NoneT
       [Log (NONE,"E") [Name (StructT (NONE,"Outer")) "x"]]]
End

Theorem forward_struct_layout:
  FLOOKUP (make_struct_fields_map forward_struct_tops) "Outer" =
    SOME [("inner",StructT (NONE,"Inner"),32)] /\
  type_memory_size (THE (evaluate_type (type_env forward_struct_tops) (StructT (NONE,"Outer")))) = 32
Proof
  EVAL_TAC
QED

Definition forward_struct_cenv_def:
  forward_struct_cenv = (ARB : compile_env) with
    <| ce_struct_fields := make_struct_fields_map forward_struct_tops;
       ce_vars := FEMPTY |+ ("x",MemLoc 256 32);
       ce_var_type := K (SOME (StructT (NONE,"Outer")));
       ce_event_info := K (SOME (123,[StructT (NONE,"Outer")],[F])) |>
End

Definition forward_struct_log_context_def:
  forward_struct_log_context =
    FST (extract_context "entry"
      (SND (emit_void STOP []
        (SND (compile_stmt forward_struct_cenv NoLoop NoneT
          (Log (NONE,"E") [Name (StructT (NONE,"Outer")) "x"])
          (initial_compile_state "entry"))))))
End

Theorem forward_struct_emitted_data:
  (case run_function 1000 forward_struct_log_context
      (HD forward_struct_log_context.ctx_functions)
      (mstore 256 41w ((init_venom_state "entry") with vs_alloca_next := 512)) of
     Halt out => out.vs_logs =
       [<|logger := 0w; topics := [123w]; data := word_to_bytes (41w:bytes32) T|>]
   | _ => F)
Proof
  EVAL_TAC
QED

val tops = rhs (concl (REWRITE_CONV [forward_struct_tops_def] ``forward_struct_tops``));
val () = List.app (fn mode =>
  let val th = vyperCheckContractLib.check_contract_conv
        ``check_contract ^mode [] 0w [(NONE,^tops)]``
  in if optionSyntax.is_some (rhs (concl th)) then
       ignore (save_thm ((if aconv mode ``T`` then "forward_struct_deploy_checked"
                         else "forward_struct_runtime_checked"), th))
     else raise Fail "forward nested-struct LOG rejected"
  end) [``F``, ``T``];
