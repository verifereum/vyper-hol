Theory readonlyInvokeCopyFwdExecutionBump
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdOpaqueReturn readonlyInvokeCopyFwdExecutionMemoryScalars
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdRel
  o1LowerDloadOccurrence internalReturnCopyFwdSim pointerConfinedDefs
  ptrDiscipline memLocDefs taintAgree
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_bump_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = BUMP /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `?bop szop pout nout bump_base size_word.
    inst.inst_operands = [bop;szop] /\ inst.inst_outputs = [pout;nout] /\
    eval_operand bop s = SOME bump_base /\ eval_operand szop s = SOME size_word /\
    u = update_var nout (bump_base+size_word) (update_var pout bump_base s)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn bop = {} /\ op_taint tn szop = {}` by
    (gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand bop t = SOME bump_base /\ eval_operand szop t = SOME size_word` by
    (conj_tac >|
     [mp_tac (Q.INST [`op` |-> `bop`, `x` |-> `bump_base:256 word`, `rt` |-> `tn`]
        ricf_execution_nonaddress_operand),
      mp_tac (Q.INST [`op` |-> `szop`, `x` |-> `size_word:256 word`, `rt` |-> `tn`]
        ricf_execution_nonaddress_operand)] >>
     (impl_tac >- simp[is_pointer_preserving_op_def, mem_read_ops_def,
        mem_write_ops_def]) >> simp[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
     sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  `?v. bind_outputs [pout;nout] [bump_base;bump_base+size_word] t = SOME v /\
    ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
      sites (ricf_complete_params PG s.vs_params)
      (DRESTRICT G (COMPL {pout;nout}))
      (tn with t_var := DRESTRICT tn.t_var (COMPL {pout;nout})) u v` by
    (mp_tac (Q.INST [`outs` |-> `[pout;nout]`,
       `vals` |-> `[bump_base:256 word;bump_base+size_word]`, `s'` |-> `u`,
       `X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
       `PG` |-> `ricf_complete_params PG s.vs_params`]
       ricf_opaque_frame_bind_outputs) >>
     (impl_tac >- simp[bind_outputs_def]) >> simp[]) >>
  `v = update_var nout (bump_base+size_word) (update_var pout bump_base t)` by
    gvs[bind_outputs_def] >>
  `step_inst fuel Ct inst t = OK v` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  `step_prov PG G inst u = DRESTRICT G (COMPL {pout;nout}) /\
   step_taint inst s u tn = tn with t_var := DRESTRICT tn.t_var (COMPL {pout;nout}) /\
   occurrence_sites_step a B inst u = B` by
    simp[step_prov_def, out_prov_def, set_prov_def, step_taint_def,
      set_var_taint_def, mem_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, new_site_bytes_def, step_writes_def, written_taint_def,
      source_memory_write_ranges_def, range_bytes_def, update_var_def,
      FLOOKUP_DEF, occurrence_sites_step_def, taint_component_equality,
      SF CONJ_ss] >>
  `ricf_opaque_live_stack_agree D (ricf_original_copy_ids C)
    (tn with t_var := DRESTRICT tn.t_var (COMPL {pout;nout}))
    maps stk targets u v` by
    (`tn with t_var := tn.t_var = tn` by simp[taint_component_equality] >>
     mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`,
       `out` |-> `pout`, `x` |-> `bump_base:256 word`,
       `y` |-> `bump_base:256 word`, `tv` |-> `tn.t_var`]
       ricf_opaque_live_stack_update_var) >>
     (impl_tac >- simp[]) >> strip_tac >> fs[] >>
     mp_tac (Q.INST [`ids` |-> `ricf_original_copy_ids C`, `out` |-> `nout`,
       `s` |-> `update_var pout (bump_base:256 word) s`,
       `t` |-> `update_var pout (bump_base:256 word) t`,
       `x` |-> `(bump_base:256 word)+size_word`, `y` |-> `(bump_base:256 word)+size_word`,
       `tv` |-> `DRESTRICT tn.t_var (COMPL {pout;nout})`]
       ricf_opaque_live_stack_update_var) >>
     (impl_tac >- simp[]) >> simp[]) >>
  qexists_tac `v` >> simp[] >>
  mp_tac (Q.INST [`rt` |-> `tn`, `Ct` |-> `Ct`, `fuel` |-> `fuel`]
    ricf_execution_next) >>
  (impl_tac >- (simp[is_terminator_def, Once ircf_dead_def, update_var_def] >>
    rpt conj_tac >>
    gvs[ircf_dead_def, ircf_cross_def, ricf_cert_crosses_def,
      ricf_support_agree_def, update_var_def] >> metis_tac[])) >> simp[]
QED
