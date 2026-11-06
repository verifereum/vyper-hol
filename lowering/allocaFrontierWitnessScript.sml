(* A RET with no adopted FMP gives its caller the allocation frontier back.
   A loop calling the allocating callee therefore reuses its 32-byte region
   on every call, instead of accumulating an unbounded frontier. *)
Theory allocaFrontierWitness
Ancestors
  vyperCompiler venomExecSemantics venomState venomInst finite_map list words
  contextCodegenRel arithmetic

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

(* The temporary callee allocation fits within the unit's 64-byte budget
   above the caller's frontier, even though the callee gets a fresh id map. *)
Theorem frontier_callee_peak:
  ?cs t.
    setup_callee frontier_callee [] s = SOME cs /\
    step_inst 0 frontier_context (instruction 0 ALLOCA [Lit 32w] ["ptr"]) cs = OK t /\
    t.vs_alloca_next = s.vs_alloca_next + 32 /\
    t.vs_alloca_next <= s.vs_alloca_next + unit_alloca_budget frontier_context
Proof
  simp[setup_callee_def, frontier_callee_def, mk_raw_function_def,
       step_inst_non_invoke, step_inst_base_def, exec_alloca_def,
       update_var_def, frontier_context_budget, dimword_def,
       fcpTheory.index_bit0, fcpTheory.index_bit1, fcpTheory.index_one,
       fcpTheory.finite_bit0, fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

Theorem frontier_context_checked:
  lowering_context_ok frontier_context /\
  reachable_call_graph_acyclic frontier_context
Proof
  EVAL_TAC >> simp[dimword_def, fcpTheory.index_bit0,
    fcpTheory.index_bit1, fcpTheory.index_one, fcpTheory.finite_bit0,
    fcpTheory.finite_bit1, fcpTheory.finite_one]
QED

Theorem frontier_entry_seed[local]:
  ~initial_vs.vs_halted /\
  codegen_reachability_package Inv frontier_context initial_vs ==>
  ?s. Inv frontier_context frontier_caller
        (instruction 2 INVOKE [Label "callee"] []) s /\
      active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
      ~s.vs_halted /\ s.vs_alloca_next = initial_vs.vs_alloca_next
Proof
  `frontier_context.ctx_entry = SOME "caller"` by EVAL_TAC >>
  `lookup_function "caller" frontier_context.ctx_functions = SOME frontier_caller`
    by EVAL_TAC >>
  `fn_entry_label frontier_caller = SOME "caller"` by EVAL_TAC >>
  simp[codegen_reachability_package_def] >> rpt strip_tac >>
  qexists `initial_vs with <| vs_prev_bb := NONE; vs_current_bb := "caller";
                            vs_inst_idx := 0 |>` >>
  `active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] [])
    (initial_vs with <| vs_prev_bb := NONE; vs_current_bb := "caller";
                       vs_inst_idx := 0 |>)`
    by simp[active_inst_def, frontier_caller_def, mk_raw_function_def] >>
  simp[] >>
  qpat_x_assum `fn_entry_inv _ _ _ _` mp_tac >>
  simp[fn_entry_inv_def] >> disch_then irule >>
  simp[enters_block_def, frontier_caller_def, mk_raw_function_def,
       lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def]
QED

(* One real caller-block execution: INVOKE, then its back edge. *)
Definition frontier_loop_step_def:
  frontier_loop_step s = jump_to "caller" (s with vs_inst_idx := 1)
End

Theorem frontier_active_invoke[local]:
  active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s ==>
  s.vs_inst_idx = 0 /\ s.vs_current_bb = "caller"
Proof
  simp[active_inst_def, frontier_caller_def, mk_raw_function_def] >>
  Cases_on `s.vs_inst_idx` >> simp[] >>
  rename1 `SUC idx < 2` >> Cases_on `idx` >> simp[]
QED

Theorem frontier_loop_step_exec:
  active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  ~s.vs_halted ==>
  exec_block 1 frontier_context (HD frontier_caller.fn_blocks) s =
    OK (frontier_loop_step s)
Proof
  strip_tac >> drule frontier_active_invoke >> strip_tac >>
  simp[Once exec_block_def, frontier_caller_def, mk_raw_function_def,
       get_instruction_def, frontier_invoke_restores, is_terminator_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, is_terminator_def, jump_to_def,
       frontier_loop_step_def]
QED

Theorem frontier_cycle[local]:
  reachability_closed Inv frontier_context /\
  Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  ~s.vs_halted ==>
  ?t. Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] []) t /\
      active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) t /\
      ~t.vs_halted /\ t.vs_alloca_next = s.vs_alloca_next /\
      t = frontier_loop_step s
Proof
  rpt strip_tac >>
  `s.vs_inst_idx = 0 /\ s.vs_current_bb = "caller"`
    by (drule frontier_active_invoke >> simp[]) >>
  qabbrev_tac `u = s with vs_inst_idx := 1` >>
  `active_inst frontier_caller (instruction 3 JMP [Label "caller"] []) u` by
    simp[Abbr `u`, active_inst_def, frontier_caller_def, mk_raw_function_def] >>
  `Inv frontier_context frontier_caller (instruction 3 JMP [Label "caller"] []) u` by
    (qpat_x_assum `reachability_closed _ _` mp_tac >>
     simp[reachability_closed_def] >> rpt strip_tac >>
     qpat_x_assum `!fn inst inst' s s' fuel.
       _ /\ _ /\ ~is_terminator _ /\ _ ==> _`
       (qspecl_then [`frontier_caller`, `instruction 2 INVOKE [Label "callee"] []`,
                     `instruction 3 JMP [Label "caller"] []`, `s`,
                     `s`, `1`] mp_tac) >>
     simp[frontier_invoke_restores, is_terminator_def, Abbr `u`,
          active_inst_def, frontier_caller_def, mk_raw_function_def]) >>
  qexists `jump_to "caller" u` >>
  reverse conj_tac
  >- simp[jump_to_def, Abbr `u`, active_inst_def, frontier_caller_def,
          mk_raw_function_def, frontier_loop_step_def] >>
  qpat_x_assum `reachability_closed _ _` mp_tac >>
  simp[reachability_closed_def] >> rpt strip_tac >>
  qpat_x_assum `!fn inst inst' s s' s1 fuel. _` irule >>
  conj_tac
  >- simp[active_inst_def, frontier_caller_def, mk_raw_function_def,
          jump_to_def] >>
  qexistsl [`1`, `instruction 3 JMP [Label "caller"] []`, `u`,
             `jump_to "caller" u`] >>
  simp[step_inst_non_invoke, step_inst_base_def, is_terminator_def,
       enters_block_def, frontier_caller_def, mk_raw_function_def,
       lookup_block_def, FIND_thm, eval_phis_def, phi_prefix_length_def,
       jump_to_def] >>
  simp[Abbr `u`]
QED

(* Every finite number of actual loop iterations preserves the caller's
   frontier.  This is not a claim that the infinite loop terminates. *)
Theorem frontier_loop_iterations:
  reachability_closed Inv frontier_context /\
  Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  ~s.vs_halted ==>
  !n. Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] [])
        (FUNPOW frontier_loop_step n s) /\
      active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] [])
        (FUNPOW frontier_loop_step n s) /\
      ~(FUNPOW frontier_loop_step n s).vs_halted /\
      (FUNPOW frontier_loop_step n s).vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> Induct >- simp[] >>
  pop_assum strip_assume_tac >> simp[FUNPOW_SUC] >>
  mp_tac (Q.INST [`s` |-> `FUNPOW frontier_loop_step n s`]
    (SPEC_ALL frontier_cycle)) >>
  impl_tac >- simp[] >> strip_tac >> gvs[]
QED

Theorem frontier_reachable_bounded:
  ~initial_vs.vs_halted /\
  codegen_reachability_package Inv frontier_context initial_vs ==>
  ?s. !n.
    Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] [])
      (FUNPOW frontier_loop_step n s) /\
    active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] [])
      (FUNPOW frontier_loop_step n s) /\
    ~(FUNPOW frontier_loop_step n s).vs_halted /\
    (FUNPOW frontier_loop_step n s).vs_alloca_next = initial_vs.vs_alloca_next /\
    exec_block 1 frontier_context (HD frontier_caller.fn_blocks)
      (FUNPOW frontier_loop_step n s) =
      OK (FUNPOW frontier_loop_step (SUC n) s)
Proof
  strip_tac >>
  `reachability_closed Inv frontier_context` by
    fs[codegen_reachability_package_def] >>
  drule_all frontier_entry_seed >> strip_tac >>
  drule_all frontier_loop_iterations >> strip_tac >>
  qexists `s` >> gen_tac >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  simp[FUNPOW_SUC] >> drule_all frontier_loop_step_exec >> simp[]
QED

(* In particular the initial frontier stays zero, below the static budget,
   independently of how many times the call site is visited. *)
Theorem frontier_initial_loop_bounded:
  codegen_reachability_package Inv frontier_context (init_venom_state "caller") ==>
  ?s. !n.
    Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] [])
      (FUNPOW frontier_loop_step n s) /\
    (FUNPOW frontier_loop_step n s).vs_alloca_next = 0 /\
    (FUNPOW frontier_loop_step n s).vs_alloca_next <=
      unit_alloca_budget frontier_context
Proof
  strip_tac >>
  `~(init_venom_state "caller").vs_halted` by simp[init_venom_state_def] >>
  drule_all frontier_reachable_bounded >> strip_tac >>
  qexists `s` >> gen_tac >>
  first_x_assum (qspec_then `n` strip_assume_tac) >>
  gvs[init_venom_state_def, frontier_context_budget]
QED
