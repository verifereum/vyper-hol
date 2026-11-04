Theory dftOccurrenceOrdinaryObserve
Ancestors
  dftOccurrenceOrdinaryEdit dftOrdinarySwap dftBlockSim venomInstProofs
  dftOpenMachine
  unitMemInv contextCodegenRel codegenRel venomEffects venomInst
  venomExecSemantics venomState pred_set list

Theorem dft_ordinary_observe_operand:
  dft_ordinary_swap_pair x y /\ step_inst fuel C y s = OK t /\
  MEM op x.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  strip_tac >> irule eval_operand_step_pres >>
  qexistsl_tac [`C`, `fuel`, `y`] >>
  gvs[dft_ordinary_swap_pair_def, inst_defs_def, inst_uses_def] >>
  rpt strip_tac >> gvs[] >> drule mem_var_operand_vars >> strip_tac >>
  fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem dft_ordinary_no_memory_ranges:
  ~(Eff_MEMORY IN read_effects i.inst_opcode) /\
  ~(Eff_MEMORY IN write_effects i.inst_opcode) ==> inst_mem_ranges i s = []
Proof
  simp[] >> Cases_on `i.inst_opcode` >>
  simp[read_effects_def, write_effects_def, all_effects_def, empty_effects_def] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem dft_ordinary_observe_memory:
  dft_ordinary_swap_pair x y /\ step_inst fuel C y s = OK t /\
  inst_mem_ranges x u <> [] ==> t.vs_memory = s.vs_memory
Proof
  strip_tac >> irule write_effects_sound_memory >>
  qexistsl_tac [`C`, `fuel`, `y`] >> simp[] >>
  `Eff_MEMORY IN read_effects x.inst_opcode \/
   Eff_MEMORY IN write_effects x.inst_opcode` by
    metis_tac[dft_ordinary_no_memory_ranges] >>
  fs[dft_ordinary_swap_pair_def, effects_independent_def,
     DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem dft_ordinary_eval_operands_cong[local]:
  (!op. MEM op ops ==> eval_operand op s = eval_operand op t) ==>
  eval_operands ops s = eval_operands ops t
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt strip_tac >>
  fs[]
QED

Theorem dft_ordinary_ranges_cong:
  inst.inst_opcode <> DRET /\ (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  inst_mem_ranges inst s = inst_mem_ranges inst t
Proof
  strip_tac >>
  `eval_operands inst.inst_operands s = eval_operands inst.inst_operands t` by
    (irule dft_ordinary_eval_operands_cong >> simp[]) >>
  Cases_on `inst.inst_opcode` >>
  asm_rewrite_tac[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       dret_memory_read_ranges_def, opcode_case_def, APPEND] >>
  all_tac
  >~ [`inst.inst_opcode = MLOAD`] >- suspend "mload"
  >~ [`inst.inst_opcode = ILOAD`] >- suspend "iload"
  >~ [`inst.inst_opcode = MCOPY`] >- suspend "mcopy"
  >~ [`inst.inst_opcode = DRET`] >- suspend "dret"
  >~ [`inst.inst_opcode = RETURN`] >- suspend "return"
  >~ [`inst.inst_opcode = REVERT`] >- suspend "revert"
  >~ [`inst.inst_opcode = SHA3`] >- suspend "sha3"
  >~ [`inst.inst_opcode = LOG`] >- suspend "log"
  >~ [`inst.inst_opcode = CALL`] >- suspend "call"
  >~ [`inst.inst_opcode = STATICCALL`] >- suspend "staticcall"
  >~ [`inst.inst_opcode = DELEGATECALL`] >- suspend "delegatecall"
  >~ [`inst.inst_opcode = CREATE`] >- suspend "create"
  >~ [`inst.inst_opcode = CREATE2`] >- suspend "create2"
  >~ [`inst.inst_opcode = MSTORE`] >- suspend "mstore"
  >~ [`inst.inst_opcode = MSTORE8`] >- suspend "mstore8"
  >~ [`inst.inst_opcode = ISTORE`] >- suspend "istore"
  >~ [`inst.inst_opcode = CALLDATACOPY`] >- suspend "calldatacopy"
  >~ [`inst.inst_opcode = RETURNDATACOPY`] >- suspend "returndatacopy"
  >~ [`inst.inst_opcode = DLOADBYTES`] >- suspend "dloadbytes"
  >~ [`inst.inst_opcode = CODECOPY`] >- suspend "codecopy"
  >> suspend "extcodecopy"
QED

Resume dft_ordinary_ranges_cong[mload]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[iload]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[mcopy]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[dret]:
  fs[]
QED
Resume dft_ordinary_ranges_cong[return]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[revert]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[sha3]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[log]:
  Cases_on `inst.inst_operands` >> fs[] >>
  rename1 `hd::rest` >> Cases_on `hd` >> fs[] >>
  Cases_on `LENGTH rest = w2n c + 2` >> simp[] >>
  `!op. MEM op (REVERSE rest) ==> eval_operand op s = eval_operand op t` by
    simp[] >>
  `LENGTH (REVERSE rest) = w2n c + 2` by simp[] >>
  Cases_on `REVERSE rest` >> fs[] >> rename1 `h::tail` >>
  Cases_on `tail` >> fs[] >>
  `eval_operands t' s = eval_operands t' t` by
    (irule dft_ordinary_eval_operands_cong >> simp[]) >>
  simp[]
QED
Resume dft_ordinary_ranges_cong[call]:
  namedCases_on `inst.inst_operands` ["", "o0 l0"] >> fs[] >>
  namedCases_on `l0` ["", "o1 l1"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l1` ["", "o2 l2"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l2` ["", "o3 l3"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l3` ["", "o4 l4"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l4` ["", "o5 l5"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l5` ["", "o6 l6"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `l6` >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED
Resume dft_ordinary_ranges_cong[staticcall]:
  namedCases_on `inst.inst_operands` ["", "o0 l0"] >> fs[] >>
  namedCases_on `l0` ["", "o1 l1"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l1` ["", "o2 l2"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l2` ["", "o3 l3"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l3` ["", "o4 l4"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l4` ["", "o5 l5"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `l5` >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED
Resume dft_ordinary_ranges_cong[delegatecall]:
  namedCases_on `inst.inst_operands` ["", "o0 l0"] >> fs[] >>
  namedCases_on `l0` ["", "o1 l1"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l1` ["", "o2 l2"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l2` ["", "o3 l3"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l3` ["", "o4 l4"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `l4` ["", "o5 l5"] >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `l5` >> fs[DISJ_IMP_THM, FORALL_AND_THM]
QED
Resume dft_ordinary_ranges_cong[create]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[create2]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[mstore]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[mstore8]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[istore]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[calldatacopy]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[returndatacopy]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[dloadbytes]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[codecopy]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Resume dft_ordinary_ranges_cong[extcodecopy]:
  rpt (CASE_TAC >> fs[DISJ_IMP_THM, FORALL_AND_THM])
QED
Finalise dft_ordinary_ranges_cong

Theorem dft_ordinary_observe_indexed:
  dft_ordinary_swap_pair x y /\ step_inst_base y s = OK t ==>
  (!op. MEM op x.inst_operands ==>
    eval_operand op (t with vs_inst_idx := idx) = eval_operand op s) /\
  inst_mem_ranges x (t with vs_inst_idx := idx) = inst_mem_ranges x s /\
  (inst_mem_ranges x s <> [] ==>
    (t with vs_inst_idx := idx).vs_memory = s.vs_memory)
Proof
  strip_tac >>
  `y.inst_opcode <> INVOKE /\ x.inst_opcode <> DRET` by
    (fs[dft_ordinary_swap_pair_def] >>
     metis_tac[is_terminator_def]) >>
  `step_inst 0 ARB y s = OK t` by simp[step_inst_non_invoke] >>
  `!op. MEM op x.inst_operands ==> eval_operand op t = eval_operand op s` by
    metis_tac[dft_ordinary_observe_operand] >>
  `!op. MEM op x.inst_operands ==>
    eval_operand op (t with vs_inst_idx := idx) = eval_operand op s` by
    (rpt strip_tac >> first_x_assum drule >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  conj_tac >- simp[] >>
  conj_tac >- (irule dft_ordinary_ranges_cong >> simp[]) >>
  simp[] >> metis_tac[dft_ordinary_observe_memory]
QED

Theorem dft_ordinary_observe_pair:
  dft_ordinary_swap_pair x y /\
  step_inst_base x s = OK sx /\ step_inst_base y s = OK sy ==>
  (!op. MEM op y.inst_operands ==>
    eval_operand op (sx with vs_inst_idx := idx) = eval_operand op s) /\
  (!op. MEM op x.inst_operands ==>
    eval_operand op (sy with vs_inst_idx := idx) = eval_operand op s) /\
  inst_mem_ranges y (sx with vs_inst_idx := idx) = inst_mem_ranges y s /\
  inst_mem_ranges x (sy with vs_inst_idx := idx) = inst_mem_ranges x s /\
  (inst_mem_ranges y s <> [] ==> sx.vs_memory = s.vs_memory) /\
  (inst_mem_ranges x (sy with vs_inst_idx := idx) <> [] ==>
    sy.vs_memory = s.vs_memory)
Proof
  strip_tac >>
  `dft_ordinary_swap_pair y x` by metis_tac[dft_ordinary_swap_pair_sym] >>
  drule_all dft_ordinary_observe_indexed >>
  disch_then (qspec_then `idx` strip_assume_tac) >>
  qpat_x_assum `step_inst_base x s = OK sx` kall_tac >>
  qpat_x_assum `dft_ordinary_swap_pair y x` kall_tac >>
  drule_all dft_ordinary_observe_indexed >>
  disch_then (qspec_then `idx` strip_assume_tac) >> gvs[]
QED

Theorem dft_occ_ordinary_observe_prefixes:
  dft_ordinary_swap_pair x y /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME x /\
  (dft_occ_oracle_next w C c).dft_occ_core =
    DftOpen (DftAt fn 0 bb sx) stx n /\
  (dft_occ_oracle_next w C' d).dft_occ_core =
    DftOpen (DftAt fn' 0 bb' sy) sty n' ==>
  dft_open_observe fn y sx (dft_occ_oracle_next w C c).dft_occ_core /\
  dft_open_observe fn' x sy (dft_occ_oracle_next w C' d).dft_occ_core /\
  (!op. MEM op y.inst_operands ==> eval_operand op sx = eval_operand op s) /\
  (!op. MEM op x.inst_operands ==> eval_operand op sy = eval_operand op s) /\
  inst_mem_ranges y sx = inst_mem_ranges y s /\
  inst_mem_ranges x sy = inst_mem_ranges x s /\
  (inst_mem_ranges y s <> [] ==> sx.vs_memory = s.vs_memory) /\
  (inst_mem_ranges x sy <> [] ==> sy.vs_memory = s.vs_memory)
Proof
  strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  `?tx. step_inst_base x s = OK tx /\
        sx = tx with vs_inst_idx := SUC s.vs_inst_idx` by
    (irule dft_occ_ordinary_success_inv >> metis_tac[]) >>
  `?ty. step_inst_base y s = OK ty /\
        sy = ty with vs_inst_idx := SUC s.vs_inst_idx` by
    (irule dft_occ_ordinary_success_inv >> metis_tac[]) >>
  gvs[] >> drule_all dft_ordinary_observe_pair >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >>
  simp[dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_occ_ordinary_observe_source_prefix:
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  d.dft_occ_core = DftOpen (DftAt fn' 0 bb' s) stack' n' /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  get_instruction bb' s.vs_inst_idx = SOME y /\
  get_instruction bb' (SUC s.vs_inst_idx) = SOME x /\
  step_inst_base x s = OK sx /\
  step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy ==>
  ?sy.
    dft_open_observe fn y (sx with vs_inst_idx := SUC s.vs_inst_idx)
      (dft_occ_oracle_next w C c).dft_occ_core /\
    dft_open_observe fn' x sy (dft_occ_oracle_next w C' d).dft_occ_core /\
    (!op. MEM op y.inst_operands ==>
      eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s) /\
    (!op. MEM op x.inst_operands ==> eval_operand op sy = eval_operand op s) /\
    inst_mem_ranges y (sx with vs_inst_idx := SUC s.vs_inst_idx) = inst_mem_ranges y s /\
    inst_mem_ranges x sy = inst_mem_ranges x s /\
    (inst_mem_ranges y s <> [] ==> sx.vs_memory = s.vs_memory) /\
    (inst_mem_ranges x sy <> [] ==> sy.vs_memory = s.vs_memory)
Proof
  strip_tac >>
  `x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE /\
   ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode` by
    fs[dft_ordinary_swap_pair_def] >>
  drule_all dft_occ_ordinary_swap_ok >>
  disch_then (qspecl_then [`w`, `C'`, `C`] strip_assume_tac) >>
  `dft_occ_oracle_next w C c = c with
    <| dft_occ_core := DftOpen
       (DftAt fn 0 bb (sx with vs_inst_idx := SUC s.vs_inst_idx))
       (MAP (dft_fill_frame 0) stack) n;
       dft_occ_saved := if stack = [] then [] else c.dft_occ_saved |>` by
    (irule dft_occ_ordinary_next >> metis_tac[]) >>
  `dft_occ_oracle_next w C' d = d with
    <| dft_occ_core := DftOpen
       (DftAt fn' 0 bb' (sb with vs_inst_idx := SUC s.vs_inst_idx))
       (MAP (dft_fill_frame 0) stack') n';
       dft_occ_saved := if stack' = [] then [] else d.dft_occ_saved |>` by
    (irule dft_occ_ordinary_next >> metis_tac[]) >>
  drule_all dft_ordinary_observe_pair >>
  disch_then (qspec_then `SUC s.vs_inst_idx` strip_assume_tac) >>
  qexists_tac `sb with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[dft_open_observe_def] >> metis_tac[]
QED
