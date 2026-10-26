(* A returning internal call retains its allocation charge in today's
   semantics, even though its allocation-id map is discarded. *)
Theory allocaFrontierWitness
Ancestors
  vyperCompiler venomExecSemantics venomState venomInst finite_map list words
  unitTransformDefs contextCodegenRel

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

Theorem frontier_invoke_increases:
  step_inst 1 frontier_context
    (instruction 2 INVOKE [Label "callee"] []) s =
  OK (s with vs_alloca_next := s.vs_alloca_next + 32)
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

Theorem frontier_entry_seed[local]:
  ~initial_vs.vs_halted /\
  codegen_reachability_package Inv frontier_context initial_vs ==>
  ?s. Inv frontier_context frontier_caller
        (instruction 2 INVOKE [Label "callee"] []) s /\
      active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
      ~s.vs_halted
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

Theorem frontier_cycle[local]:
  reachability_closed Inv frontier_context /\
  Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
  ~s.vs_halted ==>
  ?t. Inv frontier_context frontier_caller (instruction 2 INVOKE [Label "callee"] []) t /\
      active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) t /\
      ~t.vs_halted /\ t.vs_alloca_next = s.vs_alloca_next + 32
Proof
  rpt strip_tac >>
  `s.vs_inst_idx = 0 /\ s.vs_current_bb = "caller"` by
    (qpat_x_assum `active_inst _ _ _` mp_tac >>
     simp[active_inst_def, frontier_caller_def, mk_raw_function_def] >>
     Cases_on `s.vs_inst_idx` >> simp[] >>
     rename1 `SUC idx < 2` >>
     Cases_on `idx` >> simp[]) >>
  qabbrev_tac `u = s with <|vs_alloca_next := s.vs_alloca_next + 32;
                            vs_inst_idx := 1|>` >>
  `active_inst frontier_caller (instruction 3 JMP [Label "caller"] []) u` by
    simp[Abbr `u`, active_inst_def, frontier_caller_def, mk_raw_function_def] >>
  `Inv frontier_context frontier_caller (instruction 3 JMP [Label "caller"] []) u` by
    (qpat_x_assum `reachability_closed _ _` mp_tac >>
     simp[reachability_closed_def] >> rpt strip_tac >>
     qpat_x_assum `!fn inst inst' s s' fuel.
       _ /\ _ /\ ~is_terminator _ /\ _ ==> _`
       (qspecl_then [`frontier_caller`, `instruction 2 INVOKE [Label "callee"] []`,
                     `instruction 3 JMP [Label "caller"] []`, `s`,
                     `s with vs_alloca_next := s.vs_alloca_next + 32`, `1`] mp_tac) >>
     simp[frontier_invoke_increases, is_terminator_def, Abbr `u`,
          active_inst_def, frontier_caller_def, mk_raw_function_def]) >>
  qexists `jump_to "caller" u` >>
  reverse conj_tac
  >- simp[jump_to_def, Abbr `u`, active_inst_def, frontier_caller_def,
          mk_raw_function_def] >>
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

(* The call graph has one edge, but its single call site can run arbitrarily
   often. This concerns finite reachable prefixes, not execution fuel. *)
Theorem frontier_reachable_unbounded:
  ~initial_vs.vs_halted /\
  codegen_reachability_package Inv frontier_context initial_vs ==>
  !n. ?s. Inv frontier_context frontier_caller
           (instruction 2 INVOKE [Label "callee"] []) s /\
           n <= s.vs_alloca_next
Proof
  strip_tac >>
  `reachability_closed Inv frontier_context` by
    fs[codegen_reachability_package_def] >>
  `!n. ?s. Inv frontier_context frontier_caller
                  (instruction 2 INVOKE [Label "callee"] []) s /\
            active_inst frontier_caller (instruction 2 INVOKE [Label "callee"] []) s /\
            ~s.vs_halted /\ n <= s.vs_alloca_next` by
    (Induct
     >- (drule_all frontier_entry_seed >> simp[])
     >> pop_assum strip_assume_tac >>
     drule_all frontier_cycle >> strip_tac >>
     qexists `t` >> simp[] >> decide_tac) >>
  metis_tac[]
QED

Theorem frontier_not_memory_ok:
  ~initial_vs.vs_halted ==>
  ~raw_unit_memory_ok frontier_context initial_vs
Proof
  strip_tac >> strip_tac >>
  drule raw_unit_memory_ok_invariant >> strip_tac >>
  drule_all frontier_reachable_unbounded >>
  disch_then (qspec_then `dimword (:256)` strip_assume_tac) >>
  first_x_assum drule >> simp[]
QED

Theorem frontier_initial_counterexample:
  o1_initial_state_ok (init_venom_state "caller") /\
  ~raw_unit_memory_ok frontier_context (init_venom_state "caller")
Proof
  simp[o1_initial_state_ok_def, init_venom_state_def,
       frontier_not_memory_ok]
QED

