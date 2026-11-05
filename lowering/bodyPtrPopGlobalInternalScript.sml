Theory bodyPtrPopGlobalInternal
Ancestors
  bodyPtrPopGlobalDispatch bodyPtrPopGlobalLoweringBoundary
  bodyPtrPopGlobalLoweringInputs moduleLowering compileEnv exprLowering
  stmtLowering emitHelper venomInst
Libs monadsyntax

Theorem pop_global_return_count:
  pop_global_package_env.ce_returns_count = 1
Proof
  EVAL_TAC
QED

Theorem pop_global_return_bytes:
  type_memory_bytes pop_global_package_env (BaseT (UintT 256)) = 32
Proof
  EVAL_TAC
QED

(* Closed prologue state and body environment bound the statement reductions. *)
Definition pop_global_body_env_def:
  pop_global_body_env = pop_global_package_env with
    <| ce_return_pc := SOME (PtrVar (Var "%5") 0);
       ce_imm_alloca := NONE; ce_alloca_locals := T |>
End
Definition pop_global_prologue_state_def:
  pop_global_prologue_state = pop_global_dispatch_state with
    <| cs_next_var := 7; cs_next_id := 10;
       cs_current_bb := "internal 0 replace()_runtime";
       cs_current_insts :=
         [mk_inst 8 RETPC_PARAM [Lit 0w] ["%5"];
          mk_inst 9 ALLOCA [Lit 32w] ["%6"]];
       cs_blocks :=
         <| bb_label := "@fallback_0";
            bb_instructions := [mk_inst 7 REVERT [Lit 0w; Lit 0w] []] |> ::
         pop_global_dispatch_state.cs_blocks |>
End

Theorem pop_global_prologue_computed:
  (do new_block "internal 0 replace()_runtime";
      emit_op RETPC_PARAM [Lit 0w];
      compile_alloc_buffer 32;
      return () od) pop_global_dispatch_state = ((),pop_global_prologue_state)
Proof
  EVAL_TAC
QED

