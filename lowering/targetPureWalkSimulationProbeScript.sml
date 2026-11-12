(* Compiler-side interfaces for the module probe; no full counterexample yet. *)
Theory targetPureWalkSimulationProbe
Ancestors
  targetPureWalkModuleProbe intCallStep venomExecSemantics
  venomState venomInst list finite_map compileEnv exprLowering vyperAST
  emitHelper fragExec loweringStateRelDefs

Definition simulation_probe_label_def:
  simulation_probe_label = internal_fn_label 0 "index" [] F
End

Definition simulation_probe_cenv_def:
  simulation_probe_cenv = (ARB : compile_env) with
    <| ce_vars := FEMPTY |+ ("a", PtrVar (Var "a_ptr") 32);
       ce_module_vars := FEMPTY;
       ce_imm_alloca := NONE;
       ce_var_type := (\n. if n = "a" then
         SOME (ArrayT (BaseT (UintT 256)) (Fixed 1)) else NONE);
       ce_func_info := (\n. (0,0,[]));
       ce_func_ids := (\n. 0);
       ce_func_param_types := (\n. []);
       ce_func_return_type := (\n. BaseT (UintT 256));
       ce_func_mutability := build_func_mutability module_probe_tops;
       ce_is_ctor := F |>
End

Theorem simulation_probe_immutable_base_zero[local]:
  !s. immutable_base_zero simulation_probe_cenv s
Proof
  simp[immutable_base_zero_def, simulation_probe_cenv_def]
QED

Definition simulation_probe_callee_def:
  simulation_probe_callee = mk_raw_function simulation_probe_label
    [<| bb_label := simulation_probe_label;
        bb_instructions := [instruction 0 RET [Lit 0w] []] |>]
End

Definition simulation_probe_context_def:
  simulation_probe_context = mk_venom_context [simulation_probe_callee] NONE
End

Theorem simulation_probe_invoke_restores:
  !s id. step_inst 1 simulation_probe_context
    (mk_inst id INVOKE [Label simulation_probe_label] []) s = OK s
Proof
  rpt gen_tac >> simp[mk_inst_def] >>
  simp[Once step_inst_def, decode_invoke_def, simulation_probe_context_def,
       mk_venom_context_def, lookup_function_def, simulation_probe_callee_def,
       mk_raw_function_def, FIND_thm, eval_operands_def, setup_callee_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, eval_phis_def,
       phi_prefix_length_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, eval_operands_def, eval_operand_def,
       bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem simulation_probe_compile_call:
  !cfn ret_ty ty st dflt.
    compile_call cfn simulation_probe_cenv ret_ty ty (IntCall (NONE,"index"))
      [] dflt st =
    (let (u,st') = emit_void INVOKE [Label simulation_probe_label] st in
       (StackValue (BaseT (UintT 256)) (Lit 0w),st'))
Proof
  simp[compile_call_def, simulation_probe_cenv_def,
       simulation_probe_label_def, compile_multi_vvs_def,
       compile_stage_intcall_args_def, nsid_to_string_def, comp_return_def]
QED

Theorem simulation_probe_compile_target:
  !st. compile_get_target_ptr compile_expr simulation_probe_cenv
    module_probe_target st =
    (do emit_void INVOKE [Label simulation_probe_label];
        ptr <- compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F
          (compile_ptr_load F simulation_probe_cenv.ce_imm_alloca LocMemory);
        comp_return (ptr,SOME LocMemory,SOME (ValPT (BaseT (UintT 256)))) od) st
Proof
  gen_tac >> rewrite_tac[module_probe_target_def, compile_get_target_ptr_def] >>
  simp[simulation_probe_cenv_def, comp_bind_def, comp_return_def,
       lower_value_def, Once compile_expr_def, compile_call_def,
       compile_multi_vvs_def, compile_stage_intcall_args_def,
       nsid_to_string_def, simulation_probe_label_def,
       expr_type_def, unwrap_value_def, word_scale_def,
       elem_size_in_location_def, is_signed_type_def, FLOOKUP_UPDATE,
       type_memory_bytes_def, is_slot_addressed_def, comp_ignore_bind_def] >>
  Cases_on `emit_void INVOKE [Label (internal_fn_label 0 "index" [] F)] st` >>
  simp[unwrap_value_def, comp_return_def]
QED

Theorem simulation_probe_invoke_fragment:
  !sa sb s0 R.
    emit_void INVOKE [Label simulation_probe_label] sa = ((),sb) ==>
    frag_exec simulation_probe_context sa sb (\s. s = s0)
      (\t. t = s0 with vs_inst_idx := LENGTH sb.cs_current_insts) R
Proof
  rpt gen_tac >>
  simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >> irule frag_exec_invoke >> simp[] >>
  qexistsl_tac [`1`, `s0`] >> simp[mk_inst_def, simulation_probe_invoke_restores]
QED
