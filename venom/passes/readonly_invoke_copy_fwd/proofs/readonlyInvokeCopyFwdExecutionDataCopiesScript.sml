Theory readonlyInvokeCopyFwdExecutionDataCopies
Ancestors
  readonlyInvokeCopyFwdExecutionMemoryWrites readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdRel
  o1LowerDloadOccurrence ptrDiscipline taintAgree
  venomExecSemantics venomState venomInst codegenRel contextCodegenRel
  finite_map list pred_set words

Theorem ricf_execution_data_copy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ MEM inst.inst_opcode [CALLDATACOPY;DLOADBYTES;CODECOPY] /\
  inst.inst_operands = [dstop;srcop;lenop] /\ inst.inst_outputs = [] /\
  eval_operand dstop s = SOME (n2w dst) /\ eval_operand dstop t = SOME (n2w dst) /\
  eval_operand srcop s = SOME (n2w src) /\ eval_operand srcop t = SOME (n2w src) /\
  eval_operand lenop s = SOME (n2w len) /\ eval_operand lenop t = SOME (n2w len) /\
  dst < dimword (:256) /\ src < dimword (:256) /\ len < dimword (:256) /\
  data = (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
    else if inst.inst_opcode = DLOADBYTES then s.vs_data_section else s.vs_code) /\
  data = (if inst.inst_opcode = CALLDATACOPY then t.vs_call_ctx.cc_calldata
    else if inst.inst_opcode = DLOADBYTES then t.vs_data_section else t.vs_code) /\
  xs = TAKE len (DROP src data ++ REPLICATE len 0w) /\
  active_inst fn next ((write_memory_with_expansion dst xs s)
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+len) /\
      ~(dst <= sb+k /\ sb+k < dst+len)) ==>
  step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (write_memory_with_expansion dst xs s) tn) fn next
    ((write_memory_with_expansion dst xs s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((write_memory_with_expansion dst xs t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (write_memory_with_expansion dst xs s))
    ledger E sites maps targets (step_taint inst s (write_memory_with_expansion dst xs s) tn)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  `step_inst fuel C inst s = OK (write_memory_with_expansion dst xs s) /\
   step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t)` by
    (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> gvs[]) >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`Ct` |-> `Ct`, `fuel` |-> `fuel`, `xs` |-> `xs:word8 list`]
    ricf_execution_write_equal_bytes_next) >>
  impl_tac >- (simp[] >>
  fs[MEM] >>
  simp[is_terminator_def, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, step_taint_def, mem_taint_def,
    new_site_bytes_def, written_taint_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, out_taint_def,
    set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    write_memory_with_expansion_def, taint_component_equality,
    sized_source_write_range_def, FLOOKUP_DEF] >>
  (conj_tac >- SET_TAC[]) >>
  qpat_x_assum `!gam. _` mp_tac >> simp[arithmeticTheory.ADD_COMM]) >> simp[]
QED

Theorem ricf_execution_returndatacopy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = RETURNDATACOPY /\
  inst.inst_operands = [dstop;srcop;lenop] /\ inst.inst_outputs = [] /\
  eval_operand dstop s = SOME (n2w dst) /\ eval_operand dstop t = SOME (n2w dst) /\
  eval_operand srcop s = SOME (n2w src) /\ eval_operand srcop t = SOME (n2w src) /\
  eval_operand lenop s = SOME (n2w len) /\ eval_operand lenop t = SOME (n2w len) /\
  dst < dimword (:256) /\ src < dimword (:256) /\ len < dimword (:256) /\
  s.vs_returndata = t.vs_returndata /\ src+len <= LENGTH s.vs_returndata /\
  xs = TAKE len (DROP src s.vs_returndata) /\
  active_inst fn next ((write_memory_with_expansion dst xs s)
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+len) /\
      ~(dst <= sb+k /\ sb+k < dst+len)) ==>
  step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (write_memory_with_expansion dst xs s) tn) fn next
    ((write_memory_with_expansion dst xs s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((write_memory_with_expansion dst xs t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (write_memory_with_expansion dst xs s))
    ledger E sites maps targets (step_taint inst s (write_memory_with_expansion dst xs s) tn)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  `~(LENGTH s.vs_returndata < len+src) /\
   ~(LENGTH t.vs_returndata < len+src)` by (gvs[] >> decide_tac) >>
  `step_inst fuel C inst s = OK (write_memory_with_expansion dst xs s) /\
   step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
      arithmeticTheory.GREATER_DEF] >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`Ct` |-> `Ct`, `fuel` |-> `fuel`, `xs` |-> `xs:word8 list`]
    ricf_execution_write_equal_bytes_next) >>
  impl_tac >- (simp[] >>
  simp[is_terminator_def, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, step_taint_def, mem_taint_def,
    new_site_bytes_def, written_taint_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, out_taint_def,
    set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    write_memory_with_expansion_def, taint_component_equality,
    sized_source_write_range_def, FLOOKUP_DEF] >>
  (conj_tac >- SET_TAC[]) >>
  qpat_x_assum `!gam. _` mp_tac >> simp[arithmeticTheory.ADD_COMM]) >> simp[]
QED

Theorem ricf_execution_extcodecopy_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = EXTCODECOPY /\
  inst.inst_operands = [accountop;dstop;srcop;lenop] /\ inst.inst_outputs = [] /\
  eval_operand accountop s = SOME account /\ eval_operand accountop t = SOME account /\
  eval_operand dstop s = SOME (n2w dst) /\ eval_operand dstop t = SOME (n2w dst) /\
  eval_operand srcop s = SOME (n2w src) /\ eval_operand srcop t = SOME (n2w src) /\
  eval_operand lenop s = SOME (n2w len) /\ eval_operand lenop t = SOME (n2w len) /\
  dst < dimword (:256) /\ src < dimword (:256) /\ len < dimword (:256) /\
  (lookup_account (w2w account) s.vs_accounts).code =
    (lookup_account (w2w account) t.vs_accounts).code /\
  xs = TAKE len (DROP src (lookup_account (w2w account) s.vs_accounts).code ++
    REPLICATE len 0w) /\
  active_inst fn next ((write_memory_with_expansion dst xs s)
    with vs_inst_idx := SUC s.vs_inst_idx) /\
  (!gam. gam = ricf_phase_ranges 0 ledger \/
      MEM gam (ricf_phase_stack_ranges stk ledger) \/
      gam = ricf_site_triples sites \/
      (?j. j < LENGTH stk /\ gam = ricf_site_triples (EL j maps)) ==>
    !db sb sz k. (db,sb,sz) IN gam /\ k < sz ==>
      ~(dst <= db+k /\ db+k < dst+len) /\
      ~(dst <= sb+k /\ sb+k < dst+len)) ==>
  step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t) /\
  ricf_execution_invariant vs C D stk PG G
    (step_taint inst s (write_memory_with_expansion dst xs s) tn) fn next
    ((write_memory_with_expansion dst xs s) with vs_inst_idx := SUC s.vs_inst_idx)
    ((write_memory_with_expansion dst xs t) with vs_inst_idx := SUC s.vs_inst_idx)
    n a U B HP (occurrence_step a HP H inst (write_memory_with_expansion dst xs s))
    ledger E sites maps targets (step_taint inst s (write_memory_with_expansion dst xs s) tn)
Proof
  strip_tac >>
  `LENGTH xs = len` by (simp[] >> gvs[]) >>
  `step_inst fuel C inst s = OK (write_memory_with_expansion dst xs s) /\
   step_inst fuel Ct inst t = OK (write_memory_with_expansion dst xs t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  conj_tac >- simp[] >>
  mp_tac (Q.INST [`Ct` |-> `Ct`, `fuel` |-> `fuel`, `xs` |-> `xs:word8 list`]
    ricf_execution_write_equal_bytes_next) >>
  impl_tac >- (simp[] >>
  simp[is_terminator_def, step_prov_def, set_prov_def, DRESTRICT_UNIV,
    occurrence_sites_step_def, step_taint_def, mem_taint_def,
    new_site_bytes_def, written_taint_def, step_writes_def,
    source_memory_write_ranges_def, range_bytes_def, out_taint_def,
    set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    write_memory_with_expansion_def, taint_component_equality,
    sized_source_write_range_def, FLOOKUP_DEF] >>
  (conj_tac >- SET_TAC[]) >>
  qpat_x_assum `!gam. _` mp_tac >> simp[arithmeticTheory.ADD_COMM]) >> simp[]
QED
