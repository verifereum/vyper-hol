Theory dftOccurrenceGasEditTrace
Ancestors
  dftOccurrenceGasEdit dftOccurrenceMachine dftOpenMachine
  unitMemInv contextCodegenRel venomExecSemantics venomInst arithmetic list

Theorem dft_gas_edit_rel_iterate:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id /\
  dft_gas_edit_rel bb0 pre x y post w C l r ==>
  !j. dft_gas_edit_rel bb0 pre x y post w C
    (FUNPOW (dft_occ_oracle_next w C) j l)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j r)
Proof
  strip_tac >> Induct >> simp[FUNPOW_SUC] >>
  irule dft_gas_edit_rel_next >> simp[]
QED

Theorem dft_edit_map_terminal:
  (dft_edit_occ fm bm c).dft_occ_core = DftOpen (DftDone result) [] cnt <=>
  c.dft_occ_core = DftOpen (DftDone result) [] cnt
Proof
  Cases_on `c.dft_occ_core` >> rename1 `DftOpen ctl stack n` >>
  Cases_on `ctl` >> simp[dft_edit_occ_def, dft_edit_core_def,
    dft_edit_control_def, MAP_EQ_NIL]
QED

Theorem dft_edit_gas_cut_not_terminal:
  dft_edit_gas_cut core ==> core <> DftOpen (DftDone result) [] cnt
Proof
  simp[dft_edit_gas_cut_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_gas_edit_rel_terminal:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_gas_edit_rel bb0 pre x y post w C l r ==>
  (l.dft_occ_core = DftOpen (DftDone result) [] cnt <=>
   r.dft_occ_core = DftOpen (DftDone result) [] cnt)
Proof
  simp[dft_gas_edit_rel_def] >> strip_tac
  >- simp[dft_edit_map_terminal] >>
  drule_all dft_gas_edit_middle_active >>
  metis_tac[dft_edit_gas_cut_not_terminal]
QED

Theorem dft_edit_gas_ranges:
  inst.inst_opcode = GAS ==> inst_mem_ranges inst s = []
Proof
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem dft_edit_gas_cut_observe:
  dft_edit_gas_cut core /\ dft_open_observe fn inst s core ==>
  inst_mem_ranges inst s = []
Proof
  simp[dft_edit_gas_cut_def, dft_open_observe_def] >>
  rpt strip_tac >> gvs[] >> irule dft_edit_gas_ranges >> simp[]
QED

Theorem dft_gas_edit_sync_observe:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  dft_edit_safe c /\ dft_edit_cut bb0 (LENGTH pre) c /\
  dft_open_observe fnR inst s
    (dft_edit_occ (dft_gas_edit_fn bb0 pre x y post)
      (dft_gas_edit_block bb0 pre x y post) c).dft_occ_core /\
  inst_mem_ranges inst s <> [] ==>
  ?fnL. dft_open_observe fnL inst s c.dft_occ_core
Proof
  Cases_on `dft_edit_before bb0 (LENGTH pre) c`
  >- (rpt strip_tac >> gvs[dft_edit_before_def] >>
      gvs[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
          dft_open_observe_def, dft_gas_edit_block_def, get_instruction_def,
          EL_APPEND_EQN] >> metis_tac[dft_edit_gas_ranges]) >>
  rpt strip_tac >>
  `!fn b bb st stack n. c.dft_occ_core = DftOpen (DftAt fn b bb st) stack n ==>
    get_instruction (dft_gas_edit_block bb0 pre x y post bb) st.vs_inst_idx =
    get_instruction bb st.vs_inst_idx` by metis_tac[dft_gas_edit_sync_fetch] >>
  Cases_on `c.dft_occ_core` >> rename1 `DftOpen ctl stack n` >>
  Cases_on `ctl` >>
  gvs[dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
      dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_gas_edit_rel_observe:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_gas_edit_rel bb0 pre x y post w C l r /\
  dft_open_observe fnR inst s r.dft_occ_core /\ inst_mem_ranges inst s <> [] ==>
  ?fnL. dft_open_observe fnL inst s l.dft_occ_core
Proof
  simp[dft_gas_edit_rel_def] >> strip_tac
  >- metis_tac[dft_gas_edit_sync_observe] >>
  drule_all dft_gas_edit_middle_active >>
  metis_tac[dft_edit_gas_cut_observe]
QED

Theorem dft_gas_edit_init_iterate:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id ==>
  !j. dft_gas_edit_rel bb0 pre x y post w C
    (FUNPOW (dft_occ_oracle_next w C) j
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n)))
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j
      (dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n)))
Proof
  strip_tac >> irule dft_gas_edit_rel_iterate >>
  simp[dft_gas_edit_init] >> metis_tac[]
QED

(* No endpoint assumptions: this instance includes the edited block in the
   function and the function in the context. Other blocks/callees are arbitrary. *)
Theorem dft_gas_edit_containing_init:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id ==>
  let fn0 = fn with fn_blocks := bb0 :: blocks;
      C0 = C with ctx_functions := fn0 :: callees in
  !j. dft_gas_edit_rel bb0 pre x y post w C0
    (FUNPOW (dft_occ_oracle_next w C0) j
      (dft_occ_init (DftOpen (DftEnter fn0 0 s) [] n)))
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C0)) j
      (dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn bb0 pre x y post fn0) 0 s) [] n)))
Proof
  metis_tac[dft_gas_edit_init_iterate]
QED
