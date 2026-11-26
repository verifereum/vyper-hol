(* Empty Pop exits at the reached ASSERT; no header write takes place. *)
Theory bodyPopZeroAssertMods
Ancestors
  bodyPtrBopAssert ptrSafetyTransport exprSimPop fragGasEmitCtrl fragExec
  gasEvents gasCount memSafeRun unitTransformDefs ptrDiscipline
  contextCodegenRel codegenRel allocaHistory venomMemDefs
  venomExecSemantics venomState venomInst

Theorem pop_zero_assert_exit_mods:
  lookup_block s3.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s3.vs_inst_idx = SOME (mk_inst id ASSERT [Var x2] []) /\
  ~s3.vs_halted /\ lookup_var x2 s3 = SOME 0w /\
  op_taint tn (Var x2) = {} /\ allocas_from lo s3 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s3) ==>
  let u = revert_state (set_returndata [] s3) in
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s3,G,tn) []
         (Abort Revert_abort u,G,tn)) /\
  u.vs_halted /\ u.vs_returndata = [] /\
  (u with <|vs_halted := s3.vs_halted; vs_returndata := s3.vs_returndata|>) = s3 /\
  u.vs_current_bb = s3.vs_current_bb /\ u.vs_inst_idx = s3.vs_inst_idx /\
  u.vs_allocas = s3.vs_allocas /\ u.vs_alloca_next = s3.vs_alloca_next /\
  u.vs_fmp = s3.vs_fmp /\ allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (alloca_inv s3 ==> alloca_inv u) /\
  (alloca_history func s3 ==> alloca_history func u)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `u = revert_state (set_returndata [] s3)` >>
  conj_tac
  >- (gen_tac >>
      `ptr_inst_ok D lo 0 ctx func G tn (mk_inst id ASSERT [Var x2] []) s3` by
        (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
         qexists `0` >> simp[bop_assert_ptr_inst_ok]) >>
      irule exit_inst_origin_ptr >> simp[exit_result_def, Abbr `u`] >>
      simp[mk_inst_def, step_inst_non_invoke, pop_step_ASSERT,
           gas_events_step_def, gas_count_step_def, mem_safe_step_non_invoke,
           dalloca_no_wrap_def, inst_mem_below_frontier_def, inst_dload_in_section_def,
           source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `allocas_from lo u = allocas_from lo s3 /\
   allocas_below_fmp u = allocas_below_fmp s3` by
    simp[NoAsms, Abbr `u`, revert_state_def, set_returndata_def,
         allocas_from_def, allocas_below_fmp_def] >>
  `alloca_inv u = alloca_inv s3 /\ alloca_history func u = alloca_history func s3` by
    simp[NoAsms, Abbr `u`, revert_state_def, set_returndata_def,
         alloca_history_def, alloca_inv_def, allocas_non_overlapping_def,
         alloca_next_valid_def] >>
  asm_rewrite_tac[] >>
  simp[Abbr `u`, revert_state_def, set_returndata_def, venom_state_component_equality]
QED
