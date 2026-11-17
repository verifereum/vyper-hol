Theory bodyFullBuiltinPrecompileSuffixAbort
Ancestors
  bodyFullBuiltinPrecompileSuffixPath bodySimFull
  bodyPtrPrecompileBuiltinsSuffix bodyPtrPrecompileBuiltinsSuffixGhost
  fragGasSeqPtr fragExecMem fragExec instMemFrontier memSafeRun
  venomInstProofs venomExecSemantics venomInst venomState instIdxIndep
  ptrDiscipline exprLoweringProps finite_map list rich_list arithmetic
  fragGasOriginPtr fragGasOrigin fragGasPathPtr gasCount gasEvents ptrSafeRun
  emitHelperProps contextCodegenRel unitTransformDefs codegenRel

Theorem precompile_suffix_abort_full_family:
  ((addr = 1w /\ an = 128w /\ rn = 32w) \/
   (addr = 6w /\ an = 128w /\ rn = 64w) \/
   (addr = 7w /\ an = 96w /\ rn = 64w)) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\
  eval_operand (Var dst) s = SOME wo /\
  w2n wi + w2n an <= s.vs_alloca_next /\
  w2n wo + w2n rn <= s.vs_alloca_next /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  eval_operand (Var cv) v = SOME 0w /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [gi;ci;ai] (DROP s.vs_inst_idx bb.bb_instructions) /\
  (func.fn_name,id) NOTIN explicit /\ ~ctx_has_dalloca ctx /\
  (!H. valid_horizon cx st0 H trace ==>
    ptr_covers G tn src s (w2n an) /\
    ptr_covers G tn dst s (w2n rn) /\
    (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\
    tn.t_stor SUBSET (DF H).d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
    tn.t_trans SUBSET (DF H).d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)) ==>
  ?t G' tn'.
    t = (revert_state (set_returndata [] v) with vs_inst_idx := s.vs_inst_idx + 2) /\
    G' = G2 /\ tn' = tn2 /\
    (!H. valid_horizon cx st0 H trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [F] (Abort Revert_abort t,G',tn'))
Proof
  strip_tac >>
  qexistsl [`revert_state (set_returndata [] v) with vs_inst_idx := s.vs_inst_idx + 2`,
            `G2`, `tn2`] >>
  simp[NoAsms] >> gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  `run_inst_seq [gi;ci] s = OK v` by gvs[run_inst_seq_def] >>
  `?g t. inst_seq_ptr (DF H) lo ctx func PG G tn [gi;ci;ai] s g t` by
    (irule suffix_checked >> metis_tac[]) >>
  `inst_seq_ptr (DF H) lo ctx func PG G tn [gi;ci;ai] s G2 tn2` by
    (drule_all suffix_final_ghost >> metis_tac[]) >>
  `run_inst_seq_mem_ok [gi;ci;ai] s` by suspend "memory" >>
  `inst_seq_ptr (DF H) lo ctx func PG G tn [gi;ci] s G2 tn2` by
    gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
        mk_inst_def, is_terminator_def] >>
  `run_inst_seq_mem_ok [gi;ci] s` by
    gvs[run_inst_seq_mem_ok_def] >>
  `isPREFIX [gi;ci] (DROP s.vs_inst_idx bb.bb_instructions)` by
    metis_tac[IS_PREFIX_APPEND, APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) [gi;ci]` by
    simp[mk_inst_def, is_terminator_def] >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [F]
      (OK (v with vs_inst_idx := s.vs_inst_idx + 2),G2,tn2)` by
    (drule_all run_inst_seq_gas_origin_ptr_path >>
     disch_then (qspec_then `explicit` mp_tac) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `w = v with vs_inst_idx := s.vs_inst_idx + 2` >>
  `~w.vs_halted /\ lookup_block w.vs_current_bb func.fn_blocks = SOME bb` by
    (`step_inst 0 ctx gi s = OK u /\ step_inst 0 ctx ci u = OK v` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     `~is_terminator gi.inst_opcode /\ ~is_terminator ci.inst_opcode` by
       simp[mk_inst_def, is_terminator_def] >>
     drule_all step_preserves_halted >>
     drule_all step_preserves_control_flow >> strip_tac >> strip_tac >>
     qpat_x_assum `step_inst 0 ctx ci u = _` kall_tac >>
     drule_all step_preserves_halted >>
     drule_all step_preserves_control_flow >>
     simp[Abbr `w`]) >>
  `get_instruction bb w.vs_inst_idx = SOME ai` by
    (simp[Abbr `w`] >>
     qpat_x_assum `isPREFIX [gi;ci;ai] _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >>
     gvs[ADD1]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G2 tn2 ai w` by
    (qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [gi;ci;ai] _ G2 tn2` mp_tac >>
     gvs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
         mk_inst_def, is_terminator_def, Abbr `w`, ADD1]) >>
  `step_inst_base ai w = Abort Revert_abort (revert_state (set_returndata [] w))` by
    (qpat_x_assum `ai = _` SUBST_ALL_TAC >>
     irule step_ASSERT_revert >> gvs[Abbr `w`, eval_operand_def, lookup_var_def]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (w,G2,tn2) []
      (Abort Revert_abort (revert_state (set_returndata [] w)),G2,tn2)` by
    suspend "assert_origin" >>
  qpat_assum `gas_origin_ptr_path _ _ [F] (OK _,_,_)`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[NoAsms] >> disch_then drule >>
  simp[Abbr `w`, revert_state_def, set_returndata_def]
QED

Resume precompile_suffix_abort_full_family[memory]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `step_inst_base gi s = _` kall_tac >>
  qpat_x_assum `step_inst_base ci u = _` kall_tac >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_gas_def, bind_outputs_def] >>
  Cases_on `s.vs_gas_readings` >> simp[] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_STATICCALL,
       inst_dload_in_section_def] >>
  simp[run_inst_seq_mem_ok_last, below_frontier_no_ranges,
       inst_dload_in_section_def, mk_inst_def, eval_operand_def,
       lookup_var_def, FLOOKUP_UPDATE, update_var_def] >>
  gvs[eval_operand_def, lookup_var_def, wordsTheory.dimword_def] >>
  qmatch_goalsub_abbrev_tac `step_inst_base ii st` >>
  Cases_on `step_inst_base ii st` >> simp[]
QED

Resume precompile_suffix_abort_full_family[assert_origin]:
  markerLib.RESUME_TAC >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >>
  gvs[step_inst_non_invoke, ptr_safe_step_def, gas_count_step_def,
      gas_events_step_def, mk_inst_def, exit_result_def,
      mem_safe_step_non_invoke, inst_mem_below_frontier_def,
      inst_dload_in_section_def, source_memory_read_ranges_def,
      source_memory_write_ranges_def, memory_range_of_operands_def]
QED

Finalise precompile_suffix_abort_full_family
