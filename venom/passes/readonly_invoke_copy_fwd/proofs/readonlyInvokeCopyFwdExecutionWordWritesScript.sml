Theory readonlyInvokeCopyFwdExecutionWordWrites
Ancestors
  readonlyInvokeCopyFwdExecutionMemoryWrites
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdStepsMemory readonlyInvokeCopyFwdStepsMemoryData
  readonlyInvokeCopyFwdMemory
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  internalReturnCopyFwdSim readonlyInvokeCopyFwdHistoryPhase
  readonlyInvokeCopyFwdHeterogeneousLedger o1LowerDloadOccurrence
  regularCallEmitSim o1LowerDloadRangeTransport taintAgree ptrDiscipline
  venomExecSemantics venomState venomInst venomMemProps codegenRel contextCodegenRel
  finite_map list pred_set words byte

Theorem ricf_execution_mstore_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = MSTORE /\
  inst.inst_operands = [addr;value] /\ inst.inst_outputs = [] /\
  eval_operand addr s = SOME (n2w dst) /\ eval_operand addr t = SOME (n2w dst) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  dst < dimword (:256) /\ op_taint tn value = m /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  active_inst fn next ((mstore dst x s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+32) /\
      ~(dst <= sb+k /\ sb+k < dst+32)) ==>
  step_inst fuel Ct inst t = OK (mstore dst y t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (mstore dst x s) tn) fn next
    ((mstore dst x s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((mstore dst y t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (mstore dst x s))
    ledger E sites maps targets (step_taint inst s (mstore dst x s) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (mstore dst x s) /\
   step_inst fuel Ct inst t = OK (mstore dst y t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
  simp[] >>
  qabbrev_tac `M = (tn.t_mem DIFF {i | dst <= i /\ i < dst+32}) UNION
    {dst+k | k IN m}` >>
  `step_taint inst s (mstore dst x s) tn = tn with t_mem := M` by
    (simp[step_taint_def, mem_taint_def, new_site_bytes_def, written_taint_def,
      step_writes_def, source_memory_write_ranges_def, range_bytes_def,
      out_taint_def, set_var_taint_def, adopt_reset_def, store_taint_def,
      imm_taint_def, mstore_eq_write_mem, write_memory_with_expansion_def,
      DRESTRICT_UNIV, Abbr `M`, taint_component_equality,
      fixed_source_write_range_def, FLOOKUP_DEF] >> SET_TAC[]) >>
  `!i. ~(dst <= i /\ i < dst+32) ==> (i IN M <=> i IN tn.t_mem)` by
    (fs[Abbr `M`, SUBSET_DEF] >> rpt strip_tac >>
     eq_tac >> rpt strip_tac >> gvs[] >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  mp_tac (Q.INST [`len` |-> `32`, `M` |-> `M`,
    `xs` |-> `word_to_bytes (x:256 word) T`,
    `ys` |-> `word_to_bytes (y:256 word) T`] ricf_execution_write_memory_next) >>
  impl_tac >- (simp[GSYM mstore_eq_write_mem, byteTheory.LENGTH_word_to_bytes,
    step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def,
    is_terminator_def] >> rpt conj_tac
  >- (simp[Abbr `M`] >> SET_TAC[])
  >- (fs[word_agree_except_def, Abbr `M`] >> metis_tac[])
  >> metis_tac[arithmeticTheory.ADD_COMM]) >> simp[GSYM mstore_eq_write_mem]
QED

Theorem ricf_opaque_frame_istore[local]:
  ricf_opaque_frame_agree fn D X sites PG G tn s t /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  (!db sb sz k. (db,sb,sz) IN ricf_site_triples sites /\ k < sz ==>
    ~(dst <= db+k /\ db+k < dst+32) /\
    ~(dst <= sb+k /\ sb+k < dst+32)) ==>
  ricf_opaque_frame_agree fn D X sites PG G
    (tn with <|t_mem := (tn.t_mem DIFF {i | dst <= i /\ i < dst+32}) UNION
       {dst+k | k IN m}; t_imm := key_update tn.t_imm dst m|>)
    (istore dst x s) (istore dst y t)
Proof
  simp[ricf_opaque_frame_agree_def] >> strip_tac >>
  mp_tac (Q.INST [`a` |-> `dst`,
    `s` |-> `ricf_opaque_view fn PG G s`, `t` |-> `ricf_opaque_view fn PG G t`,
    `PG` |-> `ricf_visible_params PG`, `G` |-> `ricf_visible_prov G`]
    ricf_frame_istore) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  simp[ricf_opaque_view_def, istore_def, mstore_eq_write_mem,
    write_memory_with_expansion_def]
QED

Theorem ricf_execution_istore_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = ISTORE /\
  inst.inst_operands = [addr;value] /\ inst.inst_outputs = [] /\
  eval_operand addr s = SOME (n2w dst) /\ eval_operand addr t = SOME (n2w dst) /\
  eval_operand value s = SOME x /\ eval_operand value t = SOME y /\
  dst < dimword (:256) /\ op_taint tn value = m /\
  word_agree_except m x y /\ m SUBSET count 32 /\
  active_inst fn next ((istore dst x s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+32) /\
      ~(dst <= sb+k /\ sb+k < dst+32)) ==>
  step_inst fuel Ct inst t = OK (istore dst y t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (istore dst x s) tn) fn next
    ((istore dst x s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((istore dst y t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (istore dst x s))
    ledger E sites maps targets (step_taint inst s (istore dst x s) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (istore dst x s) /\
   step_inst fuel Ct inst t = OK (istore dst y t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[] >>
  qabbrev_tac `M = (tn.t_mem DIFF {i | dst <= i /\ i < dst+32}) UNION
    {dst+k | k IN m}` >>
  qabbrev_tac `un = tn with <|t_mem := M; t_imm := key_update tn.t_imm dst m|>` >>
  `step_taint inst s (istore dst x s) tn = un` by
    (simp[step_taint_def, mem_taint_def, new_site_bytes_def, written_taint_def,
      step_writes_def, source_memory_write_ranges_def, range_bytes_def,
      out_taint_def, set_var_taint_def, adopt_reset_def, store_taint_def,
      imm_taint_def, istore_def, mstore_eq_write_mem, write_memory_with_expansion_def,
      DRESTRICT_UNIV, Abbr `M`, Abbr `un`, taint_component_equality,
      fixed_source_write_range_def, FLOOKUP_DEF] >> SET_TAC[]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_opaque_live_stack_agree D (ricf_original_copy_ids C) tn maps stk targets s t /\
   ircf_cross tn (ricf_phase_ranges 0 ledger) s t /\
   ricf_cert_crosses tn (ricf_phase_stack_ranges stk ledger) stk s t /\
   ricf_support_agree B E tn s t` by fs[ricf_execution_invariant_def] >>
  mp_tac (Q.INST [`u` |-> `istore dst x s`, `v` |-> `istore dst y t`,
    `rt` |-> `tn`] ricf_execution_next) >>
  impl_tac >- (simp[is_terminator_def, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def] >> rpt conj_tac
  >- (`ircf_dead (ricf_original_copy_ids C) (istore dst x s) stk =
       ircf_dead (ricf_original_copy_ids C) s stk /\
       (istore dst x s).vs_params = s.vs_params` by
        simp[ircf_dead_def, istore_def, mstore_eq_write_mem,
          write_memory_with_expansion_def] >>
      simp[Abbr `un`, Abbr `M`] >>
      irule ricf_opaque_frame_istore >> metis_tac[])
  >- (fs[ricf_opaque_live_stack_agree_def] >>
      simp[ricf_opaque_live_stack_agree_def, ricf_merge_istore,
        Abbr `un`, Abbr `M`] >> rpt strip_tac >>
      irule (Q.INST [`tn` |-> `tn with t_var := (EL j stk).cf_tvar`]
        ricf_opaque_frame_istore |> SRULE []) >> simp[] >> metis_tac[])
  >- (simp[Abbr `un`, Abbr `M`] >> irule ricf_cross_istore >> metis_tac[])
  >- (fs[ricf_cert_crosses_def, EVERY_MEM] >>
      simp[ricf_cert_crosses_def, EVERY_MEM] >> rpt strip_tac >>
      simp[Abbr `un`, Abbr `M`] >> irule ricf_cross_istore >>
      metis_tac[arithmeticTheory.ADD_COMM])
  >> simp[ricf_support_agree_def, Abbr `un`, istore_def,
       mstore_eq_write_mem, read_byte_write_memory_with_expansion] >>
     qx_gen_tac `i` >> strip_tac >> IF_CASES_TAC >> gvs[]
     >- (`dst+(i-dst) = i /\ i-dst < 32` by decide_tac >>
         fs[word_agree_except_def, Abbr `M`] >> metis_tac[])
     >> fs[ricf_support_agree_def, Abbr `M`] >> metis_tac[]) >>
  simp[step_prov_def, set_prov_def, DRESTRICT_UNIV, occurrence_sites_step_def]
QED

Theorem ricf_execution_mcopy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = MCOPY /\
  inst.inst_operands = [dstop;srcop;lenop] /\ inst.inst_outputs = [] /\
  eval_operand dstop s = SOME (n2w dst) /\ eval_operand dstop t = SOME (n2w dst) /\
  eval_operand srcop s = SOME (n2w src) /\ eval_operand srcop t = SOME (n2w tgt) /\
  eval_operand lenop s = SOME (n2w len) /\ eval_operand lenop t = SOME (n2w len) /\
  dst < dimword (:256) /\ src < dimword (:256) /\
  tgt < dimword (:256) /\ len < dimword (:256) /\
  (!k. k < len /\ src+k NOTIN tn.t_mem ==>
    read_byte (src+k) s.vs_memory = read_byte (tgt+k) t.vs_memory) /\
  active_inst fn next ((mcopy dst src len s) with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+len) /\
      ~(dst <= sb+k /\ sb+k < dst+len)) ==>
  step_inst fuel Ct inst t = OK (mcopy dst tgt len t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (mcopy dst src len s) tn) fn next
    ((mcopy dst src len s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((mcopy dst tgt len t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (mcopy dst src len s))
    ledger E sites maps targets (step_taint inst s (mcopy dst src len s) tn)
Proof
  strip_tac >>
  `step_inst fuel C inst s = OK (mcopy dst src len s) /\
   step_inst fuel Ct inst t = OK (mcopy dst tgt len t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  qabbrev_tac `M = (tn.t_mem DIFF {i | dst <= i /\ i < dst+len}) UNION
    {dst+k | k < len /\ src+k IN tn.t_mem}` >>
  `step_taint inst s (mcopy dst src len s) tn = tn with t_mem := M` by
    (mp_tac (Q.INST [`s` |-> `s`, `tn` |-> `tn`,
       `dop` |-> `dstop`, `rop` |-> `srcop`, `lop` |-> `lenop`,
       `d` |-> `n2w dst:256 word`, `r` |-> `n2w src:256 word`,
       `z` |-> `n2w len:256 word`] step_taint_mcopy) >>
     impl_tac >- simp[] >> simp[Abbr `M`, arithmeticTheory.ADD_COMM]) >>
  `write_memory_with_expansion dst (read_memory src len s) s = mcopy dst src len s /\
   write_memory_with_expansion dst (read_memory tgt len t) t = mcopy dst tgt len t` by
    simp[mcopy_def, read_memory_def] >>
  `!i. ~(dst <= i /\ i < dst+len) ==> (i IN M <=> i IN tn.t_mem)` by
    (simp[Abbr `M`] >> rpt strip_tac >>
     eq_tac >> rpt strip_tac >> gvs[] >> decide_tac) >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`len` |-> `len`, `M` |-> `M`,
    `xs` |-> `read_memory src len s`, `ys` |-> `read_memory tgt len t`]
    ricf_execution_write_memory_next) >>
  impl_tac >- (simp[ld_read_memory_length, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, is_terminator_def] >> rpt conj_tac
  >- (simp[Abbr `M`] >> SET_TAC[])
  >- (rpt strip_tac >> simp[ld_read_memory_element] >>
      `src+k NOTIN tn.t_mem` by (fs[Abbr `M`] >> metis_tac[]) >>
      metis_tac[arithmeticTheory.ADD_COMM])
  >> metis_tac[arithmeticTheory.ADD_COMM]) >> simp[]
QED
