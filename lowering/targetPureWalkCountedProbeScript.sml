(* Counted execution interfaces for the zero-index candidate. *)
Theory targetPureWalkCountedProbe
Ancestors
  targetPureWalkSimulationProbe fragGasMode fragGasPath gasCount
  venomExecSemantics venomInst venomState compileEnv list
  exprSimArrayIndex fragGasFresh freshWrites varsExt sourceValueFrames

Theorem simulation_probe_invoke_count:
  !s id. gas_count_step 1 simulation_probe_context
    (mk_inst id INVOKE [Label simulation_probe_label] []) s = 0
Proof
  rpt gen_tac >>
  simp[Once gas_count_step_def, mk_inst_def, decode_invoke_def,
       simulation_probe_context_def, simulation_probe_callee_def,
       mk_venom_context_def, mk_raw_function_def, lookup_function_def,
       FIND_thm, eval_operands_def, setup_callee_def] >>
  simp[Once gas_count_blocks_def, lookup_block_def, FIND_thm,
       eval_phis_def, phi_prefix_length_def] >>
  simp[Once gas_count_block_def, get_instruction_def] >>
  simp[Once gas_count_step_def, is_terminator_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs,
       eval_operands_def, eval_operand_def] >>
  qmatch_goalsub_abbrev_tac `run_block_non_phis 0 cc bb st` >>
  qabbrev_tac `rr = run_block_non_phis 0 cc bb st` >>
  qpat_x_assum `Abbrev (rr = _)` (K all_tac) >>
  Cases_on `rr` >> simp[Once gas_count_blocks_def]
QED

Theorem simulation_probe_invoke_edge:
  !fn s bb id.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id INVOKE [Label simulation_probe_label] []) ==>
    gas_path_edge simulation_probe_context fn s 0
      (OK (s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >> simp[gas_path_edge_def] >>
  qexists_tac `1` >>
  simp[simulation_probe_invoke_restores, simulation_probe_invoke_count,
       mk_inst_def, is_terminator_def]
QED

Theorem simulation_probe_array_path:
  !sa sb p loader ctx fn cenv cx es s w.
    compile_array_subscript (Var "a_ptr") (Lit 0w) F 1 32 32 F loader sa =
      (p,sb) /\ fn_has_code sa sb fn /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
    not_fresh_at sa "a_ptr" /\ eval_operand (Var "a_ptr") s = SOME w /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\
      eval_operand p t = SOME w /\ stmt_state_rel ctx fn cenv cx es t /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
        lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt strip_tac >>
  `straight_fresh (compile_array_subscript (Var "a_ptr") (Lit 0w)
      F 1 32 32 F loader)` by
    (rewrite_tac[compile_array_subscript_split] >>
     simp[] >>
     `(comp_bind (comp_return (Lit 1w))
       (\len_op. comp_ignore_bind (array_bounds_check (Lit 0w) len_op F)
         (array_elem_ptr (Var "a_ptr") (Lit 0w) F 32 32))) =
       comp_ignore_bind (array_bounds_check (Lit 0w) (Lit 1w) F)
         (array_elem_ptr (Var "a_ptr") (Lit 0w) F 32 32)` by
       simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
     simp[straight_fresh_array_check_ptr]) >>
  `eval_operand (Var "a_ptr") (drop_fresh sa s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  drule compile_array_subscript_ok >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh, eval_operand_def, array_len_ok_def,
       idx_in_range_def] >>
  strip_tac >>
  gvs[] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[wordsTheory.WORD_MULT_CLAUSES]
QED
