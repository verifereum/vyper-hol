Theory readonlyInvokeCopyFwdExecutionMemoryWrites
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsMemory readonlyInvokeCopyFwdStepsMemoryData
  readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  internalReturnCopyFwdSim readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHeterogeneousLedger o1LowerDloadOccurrence
  regularCallEmitSim o1LowerDloadRangeTransport taintAgree ptrDiscipline
  venomExecSemantics venomState venomInst venomMemProps codegenRel contextCodegenRel
  finite_map list pred_set words byte

Theorem ricf_opaque_frame_write_memory[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (tn.t_mem DIFF {i | dst <= i /\ i < dst+len}) SUBSET M /\
  (!k. k < len /\ dst+k NOTIN M ==> EL k xs = EL k ys) /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(dst <= db+k /\ db+k < dst+len) /\
    ~(dst <= sb+k /\ sb+k < dst+len) /\
    (db+k IN M <=> db+k IN tn.t_mem) /\
    (sb+k IN M <=> sb+k IN tn.t_mem)) ==>
  ricf_opaque_frame_agree fn D X sites PG G (tn with t_mem := M)
    (write_memory_with_expansion dst xs s) (write_memory_with_expansion dst ys t)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  drule (Q.INST [`a` |-> `dst`, `xs` |-> `xs`, `ys` |-> `ys`,
    `len` |-> `len`, `M` |-> `M`] ricf_frame_write_memory) >>
  disch_then (qspecl_then [`ys`,`xs`,`len`,`dst`,`M`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[ricf_opaque_view_def, write_memory_with_expansion_def]
QED

Theorem ricf_execution_write_memory_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK (write_memory_with_expansion dst xs s) /\
  step_inst fuel Ct inst t = OK (write_memory_with_expansion dst ys t) /\
  active_inst fn next ((write_memory_with_expansion dst xs s)
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_prov PG G inst (write_memory_with_expansion dst xs s) = G /\
  step_taint inst s (write_memory_with_expansion dst xs s) tn =
    (tn with t_mem := M) /\
  occurrence_sites_step a B inst (write_memory_with_expansion dst xs s) = B /\
  LENGTH xs = len /\ LENGTH ys = len /\
  (tn.t_mem DIFF {i | dst <= i /\ i < dst+len}) SUBSET M /\
  (!k. k < len /\ dst+k NOTIN M ==> EL k xs = EL k ys) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+len) /\
      ~(dst <= sb+k /\ sb+k < dst+len) /\
      (db+k IN M <=> db+k IN tn.t_mem) /\
      (sb+k IN M <=> sb+k IN tn.t_mem)) ==>
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (write_memory_with_expansion dst xs s) tn) fn next
    ((write_memory_with_expansion dst xs s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((write_memory_with_expansion dst ys t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (write_memory_with_expansion dst xs s))
    ledger E sites maps targets (tn with t_mem := M)
Proof
  strip_tac >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  `ircf_dead (ricf_original_copy_ids C) (write_memory_with_expansion dst xs s) stk =
     ircf_dead (ricf_original_copy_ids C) s stk /\
   (write_memory_with_expansion dst xs s).vs_params = s.vs_params` by
    simp[ircf_dead_def, write_memory_with_expansion_def] >>
  mp_tac (Q.INST [`u` |-> `write_memory_with_expansion dst xs s`,
    `v` |-> `write_memory_with_expansion dst ys t`, `rt` |-> `tn`]
    ricf_execution_next) >>
  impl_tac >- (simp[] >>
  rpt conj_tac
  >- (irule ricf_opaque_frame_write_memory >> metis_tac[])
  >- (fs[ricf_opaque_live_stack_agree_def] >>
      simp[ricf_opaque_live_stack_agree_def, GSYM write_memory_with_expansion_def,
        ricf_write_memory_merge] >> rpt strip_tac >>
      irule (Q.INST [`tn` |-> `tn with t_var := (EL j stk).cf_tvar`]
        ricf_opaque_frame_write_memory) >> simp[] >> metis_tac[])
  >- (qpat_x_assum `!gam. _` (qspec_then `ricf_phase_ranges 0 ledger` mp_tac) >>
      simp[] >> strip_tac >>
      irule ricf_cross_byte_frame >> qexistsl_tac [`s`,`t`,`tn`] >>
      simp[] >> rpt strip_tac >>
      simp[read_byte_write_memory_with_expansion] >> metis_tac[])
  >- (irule ricf_cert_crosses_refresh >> qexistsl_tac [`s`,`t`,`tn`] >>
      simp[] >> rpt strip_tac >>
      rename1 `MEM gam (ricf_phase_stack_ranges stk ledger)` >>
      qpat_x_assum `!gam. _` (qspec_then `gam` mp_tac) >> simp[] >> strip_tac >>
      simp[read_byte_write_memory_with_expansion] >> metis_tac[])
  >> simp[ricf_support_agree_def, read_byte_write_memory_with_expansion] >>
     qx_gen_tac `i` >> strip_tac >>
     Cases_on `dst <= i /\ i < dst+LENGTH xs`
     >- (simp[] >> `dst+(i-dst) = i /\ i-dst < LENGTH xs` by decide_tac >> metis_tac[]) >>
     simp[] >>
     fs[ricf_support_agree_def, SUBSET_DEF] >> metis_tac[]) >> simp[]
QED

Theorem ricf_execution_mstore8_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = MSTORE8 /\
  inst.inst_operands = [addr;value] /\ inst.inst_outputs = [] /\
  eval_operand addr s = SOME (n2w dst) /\ eval_operand addr t = SOME (n2w dst) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  dst < dimword (:256) /\ (w2w x : word8) = w2w y /\
  active_inst fn next ((mstore8 dst x s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==> db+k <> dst /\ sb+k <> dst) ==>
  step_inst fuel Ct inst t = OK (mstore8 dst y t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (mstore8 dst x s) tn) fn next
    ((mstore8 dst x s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((mstore8 dst y t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (mstore8 dst x s))
    ledger E sites maps targets (step_taint inst s (mstore8 dst x s) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (mstore8 dst x s) /\
   step_inst fuel Ct inst t = OK (mstore8 dst y t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
  `{i:num | dst <= i /\ i < dst+1} = {dst}` by
    (simp[EXTENSION] >> decide_tac) >>
  `step_taint inst s (mstore8 dst x s) tn = tn with t_mem := tn.t_mem DIFF {dst}` by
    (simp[step_taint_def, mem_taint_def, new_site_bytes_def, written_taint_def,
      step_writes_def, source_memory_write_ranges_def, range_bytes_def,
      out_taint_def, set_var_taint_def, adopt_reset_def, store_taint_def,
      imm_taint_def, mstore8_eq_write_mem, write_memory_with_expansion_def,
      DRESTRICT_UNIV, taint_component_equality, fixed_source_write_range_def,
      FLOOKUP_DEF] >>
     SET_TAC[arithmeticTheory.LESS_EQ_ADD]) >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`len` |-> `1`, `xs` |-> `[w2w (x:256 word)]`,
    `ys` |-> `[w2w (y:256 word)]`,
    `M` |-> `tn.t_mem DIFF {dst}`] ricf_execution_write_memory_next) >>
  impl_tac >- (simp[GSYM mstore8_eq_write_mem, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, is_terminator_def] >>
  rpt conj_tac >> rpt strip_tac >>
     `db+k <> dst /\ sb+k <> dst` by metis_tac[] >>
     gvs[] >> decide_tac) >> simp[GSYM mstore8_eq_write_mem]
QED

Theorem ricf_execution_write_equal_bytes_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK (write_memory_with_expansion dst xs s) /\
  step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t) /\
  active_inst fn next ((write_memory_with_expansion dst xs s)
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_prov PG G inst (write_memory_with_expansion dst xs s) = G /\
  step_taint inst s (write_memory_with_expansion dst xs s) tn =
    (tn with t_mem := tn.t_mem DIFF {i | dst <= i /\ i < dst+LENGTH xs}) /\
  occurrence_sites_step a B inst (write_memory_with_expansion dst xs s) = B /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+LENGTH xs) /\
      ~(dst <= sb+k /\ sb+k < dst+LENGTH xs)) ==>
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (write_memory_with_expansion dst xs s) tn) fn next
    ((write_memory_with_expansion dst xs s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((write_memory_with_expansion dst xs t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (write_memory_with_expansion dst xs s))
    ledger E sites maps targets (step_taint inst s (write_memory_with_expansion dst xs s) tn)
Proof
  strip_tac >>
  mp_tac (Q.INST [`len` |-> `LENGTH (xs:word8 list)`, `xs` |-> `xs:word8 list`,
    `ys` |-> `xs:word8 list`,
    `M` |-> `tn.t_mem DIFF {i | dst <= i /\ i < dst+LENGTH (xs:word8 list)}`]
    ricf_execution_write_memory_next) >>
  impl_tac >- (simp[] >> rpt strip_tac >>
  `~(dst <= db+k /\ db+k < dst+LENGTH xs) /\
   ~(dst <= sb+k /\ sb+k < dst+LENGTH xs)` by metis_tac[] >> fs[]) >> simp[]
QED

