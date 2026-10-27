(* A returning internal call gives its caller the allocation frontier back:
   a loop around a call to an allocating callee runs every iteration at the
   same frontier, which unit_alloca_budget bounds. *)
Theory allocaFrontierWitness
Ancestors
  vyperCompiler venomExecSemantics venomState venomInst finite_map list words
  contextCodegenRel

Definition frontier_callee_def:
  frontier_callee = mk_raw_function "callee"
    [<| bb_label := "callee";
        bb_instructions :=
          [instruction 0 ALLOCA [Lit 32w] ["ptr"];
           instruction 1 RET [Lit 0w] []] |>]
End

Definition frontier_caller_def:
  frontier_caller = mk_raw_function "caller"
    [<| bb_label := "caller";
        bb_instructions :=
          [instruction 2 INVOKE [Label "callee"] [];
           instruction 3 JMP [Label "caller"] []] |>]
End

Definition frontier_context_def:
  frontier_context =
    mk_venom_context [frontier_caller; frontier_callee] (SOME "caller")
End

Theorem frontier_context_budget:
  unit_alloca_budget frontier_context = 64
Proof
  EVAL_TAC >> simp[dimword_def, fcpTheory.index_bit0,
    fcpTheory.index_bit1, fcpTheory.index_one, fcpTheory.finite_bit0,
    fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

Theorem frontier_invoke_restores:
  step_inst 1 frontier_context
    (instruction 2 INVOKE [Label "callee"] []) s = OK s
Proof
  simp[Once step_inst_def, decode_invoke_def, frontier_context_def,
       mk_venom_context_def, lookup_function_def, frontier_callee_def,
       frontier_caller_def, mk_raw_function_def, FIND_thm,
       eval_operands_def, setup_callee_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, eval_phis_def,
       phi_prefix_length_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, exec_alloca_def, update_var_def, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, eval_operands_def, eval_operand_def,
       bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def,
       dimword_def, fcpTheory.index_bit0, fcpTheory.index_bit1,
       fcpTheory.index_one, fcpTheory.finite_bit0, fcpTheory.finite_bit1,
       fcpTheory.finite_one, venom_state_component_equality]
QED

Theorem frontier_context_checked:
  lowering_context_ok frontier_context /\
  reachable_call_graph_acyclic frontier_context
Proof
  EVAL_TAC >> simp[dimword_def, fcpTheory.index_bit0,
    fcpTheory.index_bit1, fcpTheory.index_one, fcpTheory.finite_bit0,
    fcpTheory.finite_bit1, fcpTheory.finite_one]
QED
