(* The failing slot-store edge, starting at the reached Pop cursor. *)
Theory bodyPopStaticStoreMods
Ancestors
  fragGasEmitCtrl fragExec loweringHalt emitHelperProps
  ptrSafeRun ptrDiscipline memSafeRun gasEvents gasCount
  venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs

Theorem pop_static_store_exit_mods:
  s5.vs_call_ctx.cc_static /\ ~s5.vs_halted /\
  lookup_block s5.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s5.vs_inst_idx =
    SOME (mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []) /\
  eval_operand hdr s5 = SOME slot /\ eval_operand (Var x3) s5 = SOME value /\
  op_taint tn hdr = {} /\ op_taint tn (Var x3) = {} /\
  allocas_from lo s5 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s5) ==>
  let h = halt_state (set_returndata [] s5) in
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s5,G,tn) [] (Abort ExHalt_abort h,G,tn)) /\
    allocas_from lo h /\ (ctx_has_dalloca ctx ==> allocas_below_fmp h)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  reverse conj_tac
  >- (conj_tac
      >- (qpat_assum `allocas_from lo s5` mp_tac >>
          simp[NoAsms, halt_state_def, set_returndata_def, allocas_from_def]) >>
      qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s5` mp_tac >>
      simp[NoAsms, halt_state_def, set_returndata_def, allocas_below_fmp_def] >>
      metis_tac[]) >>
  qabbrev_tac `i = mk_inst id (if tr then TSTORE else SSTORE) [hdr;Var x3] []` >>
  `step_inst_base i s5 = Abort ExHalt_abort (halt_state (set_returndata [] s5))` by
    (Cases_on `tr` >> simp[Abbr `i`] >>
     metis_tac[loweringHaltTheory.step_TSTORE,emitHelperPropsTheory.step_SSTORE]) >>
  gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn i s5` by
    (Cases_on `tr` >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, Abbr `i`, mk_inst_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp_tac bool_ss [] >> disch_tac >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     rpt strip_tac >> gvs[]) >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by
    (Cases_on `tr` >> simp[Abbr `i`, mk_inst_def]) >>
  `mem_safe_step 0 ctx i s5` by
    (Cases_on `tr` >>
     simp[Abbr `i`, mem_safe_step_non_invoke, mk_inst_def,
          inst_mem_below_frontier_def, inst_dload_in_section_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  irule exit_inst_origin_ptr >> simp[exit_result_def] >>
  simp[step_inst_non_invoke, gas_events_step_def, gas_count_step_def]
QED
