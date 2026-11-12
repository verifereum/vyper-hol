(* Gas reserve for creation, charged once by step_create. *)
Theory asmFrameCreateGas
Ancestors
  asmFrameCreateStep asmRunBounded asmCallGasArithmetic asmFrameLocalStep
  vfmRunCall vfmDomainCollection frameStep asmFrameRel codegenRel vfmExecution
  vfmExecutionProp asmSem list vfmConstants

Theorem asm_create_underflow[local]:
  s.contexts = (c,rb)::rest /\
  ~((if two then 4 else 3) <= LENGTH c.stack) ==>
  step_create two s = (INR (SOME StackUnderflow),s)
Proof
  strip_tac >>
  simp[step_create_def, pop_stack_def, get_current_context_def,
       bind_def, ignore_bind_def, assert_def, fail_def, return_def]
QED

Theorem asm_frame_create_gas:
  !prog data es0 a es H.
    asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 a es /\
    a.as_pc < LENGTH prog /\ ~is_data_inst (EL a.as_pc prog) /\
    asm_inst_gas_ok H (EL a.as_pc prog) a.as_stack /\
    50000 + 8 * H + memory_cost H <= frame_gas_left es /\
    MEM (EL a.as_pc prog) [AsmOp "CREATE"; AsmOp "CREATE2"] ==>
    (!op r s'.
       next_opcode (FST (HD es.contexts)) = SOME op /\
       step_inst op es = (r,s') /\
       LENGTH s'.contexts = LENGTH es.contexts ==>
       r <> INR (SOME OutOfGas) /\
       (frame_gas_left es - (50000 + 8 * H + memory_cost H)) DIV 64 <=
         frame_gas_left s') /\
    (!es1. frame_next es es1 ==>
       (frame_gas_left es - (50000 + 8 * H + memory_cost H)) DIV 64 <=
         frame_gas_left es1)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `asm_frame_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [asm_frame_rel_def]) >>
  `c.stack = a.as_stack` by gvs[asm_evm_rel_def] >>
  `~c.msgParams.static` by metis_tac[] >>
  `next_opcode (FST (HD es.contexts)) = SOME
     (if EL a.as_pc prog = AsmOp "CREATE" then Create else Create2)` by
    (irule asm_frame_create_decode >> simp[] >>
     conj_tac >- fs[listTheory.MEM] >> metis_tac[]) >>
  qabbrev_tac `two = (EL a.as_pc prog <> AsmOp "CREATE")` >>
  `EL a.as_pc prog = AsmOp (if two then "CREATE2" else "CREATE")` by
    (gvs[listTheory.MEM, Abbr `two`]) >>
  `next_opcode c = SOME (if two then Create2 else Create)` by
    (Cases_on `two` >> gvs[]) >>
  `asm_inst_gas_ok H (AsmOp (if two then "CREATE2" else "CREATE")) c.stack` by
    metis_tac[] >>
  drule asm_inst_gas_ok_create_ranges >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `k = static_gas (if two then Create2 else Create) +
    init_code_word_cost * word_size (w2n (EL 2 c.stack)) +
    (if two then keccak256_per_word_cost * word_size (w2n (EL 2 c.stack)) else 0) +
    memory_expansion_cost (buffer_length c.memory)
      (if 0 < w2n (EL 2 c.stack) then
       word_size (w2n (EL 1 c.stack) + w2n (EL 2 c.stack)) * 32 else 0)` >>
  `k <= 50000 + 8 * H + memory_cost H` by
    (drule_all create_upfront_cost_bound >>
     disch_then (qspecl_then [`two`, `buffer_length c.memory`] mp_tac) >>
     Cases_on `two` >>
     simp[Abbr `k`, init_code_word_cost_def, keccak256_per_word_cost_def] >>
     decide_tac) >>
  conj_tac >- suspend "raw" >> suspend "handled"
QED

Resume asm_frame_create_gas[raw]:
  rpt gen_tac >> strip_tac >>
  `op = (if two then Create2 else Create)` by
    (qpat_x_assum `next_opcode (FST _) = SOME op` mp_tac >>
     Cases_on `two` >> simp[]) >>
  `step_create two es = (r,s')` by
    (qpat_x_assum `step_inst _ _ = _` mp_tac >>
     Cases_on `two` >> gvs[step_inst_def]) >>
  Cases_on `(if two then 4 else 3) <= LENGTH c.stack`
  >- (qpat_x_assum `Abbrev (k = _)`
        (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
        fs[frame_gas_left_def] >>
      drule_all asm_create_raw_budget >> strip_tac >>
      gvs[frame_gas_left_def]) >>
  drule_all asm_create_underflow >> strip_tac >>
  gvs[frame_gas_left_def] >>
  irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac
    `(c.msgParams.gasLimit - c.gasUsed - (50000 + 8 * H + memory_cost H))` >>
  simp[arithmeticTheory.DIV_LESS_EQ]
QED

Resume asm_frame_create_gas[handled]:
  gen_tac >> strip_tac >>
  qpat_x_assum `frame_next _ _`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS) o
     REWRITE_RULE [frame_next_def]) >>
  reverse (Cases_on `(if two then 4 else 3) <= LENGTH c.stack`)
  >- (drule_all asm_create_underflow >> strip_tac >>
      `step es = handle_step (SOME StackUnderflow) es` by
        (irule asm_create_step_terminal >> metis_tac[]) >>
      `handle_step (SOME StackUnderflow) es = (INL (),v)` by metis_tac[] >>
      `es.contexts <> []` by simp[] >>
      drule_all handle_step_inl_pops >> gvs[] >> decide_tac) >>
  qpat_x_assum `Abbrev (k = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `50000 + 8 * H + memory_cost H <= c.msgParams.gasLimit - c.gasUsed` by
    fs[frame_gas_left_def] >>
  Cases_on `step_create two es` >>
  rename1 `step_create two es = (res,mid)` >>
  drule_all asm_create_raw_budget >>
  strip_tac >>
  `res = INL ()` by
    (Cases_on `res`
     >- (rename1 `INL z = INL ()` >> Cases_on `z` >> simp[]) >>
     drule_all asm_create_raw_failure >>
     qpat_x_assum `k = _` mp_tac >> simp[] >>
     disch_then (fn th => pure_rewrite_tac[GSYM th]) >>
     rpt strip_tac >> gvs[]) >>
  `step es = (INL (),mid)` by
    (irule asm_create_step_success >> metis_tac[]) >>
  `v = mid` by fs[] >> gvs[ExclSF "ARITH"] >>
  Cases_on `es1 = mid`
  >- gvs[frame_gas_left_def] >>
  gvs[frame_gas_left_def] >>
  `wf_state mid` by
    (drule_all vfmRunCallTheory.step_preserves_wf_state >> simp[]) >>
  `?dm. mid.msdomain = Collect dm` by
    (drule_at (Pat `step _ = _`) vfmDomainCollectionTheory.step_preserves_collect >> simp[]) >>
  `LENGTH mid.contexts = SUC (LENGTH es.contexts)` by simp[] >>
  drule_at (Pat `step_create _ _ = _`) asm_create_raw_child_entry >>
  disch_then (qspecl_then [`rest`, `rb`, `d`, `c`] mp_tac) >>
  simp[ExclSF "ARITH"] >> strip_tac >>
  qpat_x_assum `p.gasUsed = _` kall_tac >>
  drule_at (Pat `_.contexts = _::_::_`) asm_create_run_code_continuation >>
  simp[ExclSF "ARITH"] >> strip_tac >>
  simp[ExclSF "ARITH", frame_gas_left_def] >>
  qpat_x_assum `_ DIV 64 <= _ - p.gasUsed` mp_tac >>
  qpat_x_assum `_.gasUsed <= p.gasUsed` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Finalise asm_frame_create_gas
