Theory dftOccurrenceCallObserve
Ancestors
  dftOccurrenceCallTrace dftOccurrenceCallPosition dftOccurrenceCallClosure
  dftOccurrenceCallCrossing dftOccurrenceCallStack dftOccurrenceGasEdit
  dftOccurrenceMachine dftOpenMachine dftOpenErase unitMemInv arithmetic list

Theorem dft_mixed_sync_observe_outside:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  dft_mixed_sync bb0 pre gas call post v w l r /\
  l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  (bb = bb0 ==> s.vs_inst_idx <> LENGTH pre /\
                   s.vs_inst_idx <> SUC (LENGTH pre)) /\
  dft_open_observe fnR inst st r.dft_occ_core ==>
  dft_open_observe fn inst st l.dft_occ_core
Proof
  simp[dft_mixed_sync_def] >> rpt strip_tac >> gvs[dft_edit_control_def] >>
  `get_instruction (dft_gas_edit_block bb0 pre gas call post bb) s.vs_inst_idx =
   get_instruction bb s.vs_inst_idx` by
    metis_tac[dft_gas_edit_instruction_outside] >>
  gvs[dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_mixed_good_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r /\
  dft_open_observe fnR inst st r.dft_occ_core /\ inst_mem_ranges inst st <> [] ==>
  ?a fnL instL sL. a <= 1 /\
    dft_open_observe fnL instL sL (FUNPOW (dft_occ_oracle_next w C) a l).dft_occ_core /\
    sL.vs_memory = st.vs_memory /\ sL.vs_alloca_next = st.vs_alloca_next /\
    inst_mem_ranges instL sL = inst_mem_ranges inst st
Proof
  strip_tac >>
  qpat_x_assum `dft_mixed_good _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dft_mixed_good_def])
  >- suspend "sync"
  >- metis_tac[dft_mixed_discharge_observe] >>
  metis_tac[dft_mixed_cleared_observe]
QED

Resume dft_mixed_good_observe[sync]:
  `?ctl stack n. l.dft_occ_core = DftOpen ctl stack n /\
    dft_fill_control 0 ctl = ctl` by metis_tac[dft_mixed_sync_def] >>
  Cases_on `ctl`
  >- (gvs[dft_mixed_sync_def, dft_edit_control_def, dft_open_observe_def])
  >- suspend "at" >>
  gvs[dft_mixed_sync_def, dft_edit_control_def, dft_open_observe_def]
QED

Resume dft_mixed_good_observe[at]:
  gvs[dft_fill_control_def] >>
  rename1 `l.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n` >>
  Cases_on `bb = bb0 /\ s.vs_inst_idx = LENGTH pre`
  >- (gvs[] >> drule_all dft_mixed_crossing_call_observe >>
      disch_then (qspec_then `C` strip_assume_tac) >>
      qexistsl_tac [`1`,`fn`,`call`,`sL`] >> simp[]) >>
  `dft_open_observe fn inst st l.dft_occ_core` by
    (irule dft_mixed_sync_observe_outside >> simp[] >>
     metis_tac[dft_mixed_safe_sync_def]) >>
  qexistsl_tac [`0`,`fn`,`inst`,`st`] >> gvs[]
QED

Finalise dft_mixed_good_observe

Theorem dft_mixed_good_prefix_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_mixed_good bb0 pre gas call post v w l r /\
  dft_open_observe fnR inst st
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) n r).dft_occ_core /\
  inst_mem_ranges inst st <> [] ==>
  ?k fnL instL sL. k <= 2 * n + 1 /\
    dft_open_observe fnL instL sL (FUNPOW (dft_occ_oracle_next w C) k l).dft_occ_core /\
    sL.vs_memory = st.vs_memory /\ sL.vs_alloca_next = st.vs_alloca_next /\
    inst_mem_ranges instL sL = inst_mem_ranges inst st
Proof
  strip_tac >>
  `?m. m <= 2 * n /\ dft_mixed_good bb0 pre gas call post v w
    (FUNPOW (dft_occ_oracle_next w C) m l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) n r)` by
    metis_tac[dft_mixed_good_prefix] >>
  drule_all dft_mixed_good_observe >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexistsl_tac [`a + m`,`fnL`,`instL`,`sL`] >>
  simp[FUNPOW_ADD] >> decide_tac
QED

Theorem dft_mixed_init_prefix_observe:
  bb0.bb_instructions = pre ++ [gas;call] ++ post /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  call.inst_opcode = INVOKE /\ ~MEM v call.inst_outputs /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==> ~MEM (Var v) ops) /\
  dft_open_observe fnR inst st
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre gas call post C)) n
      (dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn bb0 pre gas call post fn) 0 s) [] nR))).dft_occ_core /\
  inst_mem_ranges inst st <> [] ==>
  ?k fnL instL sL. k <= 2 * n + 1 /\
    dft_open_observe fnL instL sL
      (FUNPOW (dft_occ_oracle_next w C) k
        (dft_occ_init (DftOpen (DftEnter fn 0 s) [] nL))).dft_occ_core /\
    sL.vs_memory = st.vs_memory /\ sL.vs_alloca_next = st.vs_alloca_next /\
    inst_mem_ranges instL sL = inst_mem_ranges inst st
Proof
  strip_tac >> irule dft_mixed_good_prefix_observe >>
  simp[] >> metis_tac[dft_mixed_good_init]
QED
