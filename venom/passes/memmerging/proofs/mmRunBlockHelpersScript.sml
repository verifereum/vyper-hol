(* Proof-only compatibility with atomic PHI execution.
   The existing memzero WF predicate quantifies over every fresh superset.
   At UNIV this excludes variable operands in non-terminators.  Consequently
   a PHI it admits has no incoming pairs and fails at block entry.  No SSA
   premise is needed: successful admitted blocks have no PHIs. *)
Theory mmRunBlockHelpers
Ancestors
  mmCorrectnessProofs mmTransform mmScan venomExecProofs venomExecSemantics
  venomWf venomInst venomState list rich_list pred_set arithmetic alist

Theorem phi_well_formed_no_vars_empty[local]:
  !ops. phi_well_formed ops /\
    (!x. ~MEM (Var x) ops) ==> ops = []
Proof
  gen_tac >> Cases_on `ops` >- simp[] >>
  rename1 `phi_well_formed (a::rest)` >>
  Cases_on `rest` >- simp[phi_well_formed_def] >>
  rename1 `phi_well_formed (a::b::tail)` >>
  Cases_on `a` >> Cases_on `b` >> simp[phi_well_formed_def] >> metis_tac[]
QED

Theorem memzero_block_wf_phi_empty:
  !dfg bb inst.
    memzero_block_wf dfg bb /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==> inst.inst_operands = []
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `memzero_block_wf _ _` mp_tac >>
  simp[memzero_block_wf_def, LET_THM] >> strip_tac >>
  first_x_assum (qspec_then `UNIV` mp_tac) >>
  simp[EVERY_MEM, MEM_FILTER] >> strip_tac >>
  `memzero_inst_ok
    (nop_ids_of_groups dfg Mem2Mem bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed)
    (rep_map_of_groups bb.bb_instructions
      (scan_block_memzero dfg bb).mz_flushed) UNIV inst` by
    (first_x_assum irule >> simp[is_terminator_def]) >>
  qpat_x_assum `memzero_inst_ok _ _ UNIV inst` mp_tac >>
  qpat_x_assum `inst.inst_opcode = PHI` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[memzero_inst_ok_def, inst_wf_def] >> rpt strip_tac >>
  irule phi_well_formed_no_vars_empty >> simp[]
QED

Theorem dload_pair_wf_phi_ids[local]:
  !dfg dp insts inst.
    dload_pair_wf dfg dp insts /\ MEM inst insts /\
    inst.inst_opcode = PHI ==>
    inst.inst_id <> dp.dp_dload_id /\ inst.inst_id <> dp.dp_mstore_id
Proof
  rpt gen_tac >> strip_tac >>
  fs[dload_pair_wf_def] >>
  qpat_x_assum `MEM inst insts` mp_tac >> simp[MEM_EL] >> strip_tac >>
  rename1 `n < LENGTH insts` >> gvs[] >>
  conj_tac
  >- (strip_tac >> `n = di` by
        (irule all_distinct_inst_id_idx >> qexists_tac `insts` >> simp[]) >>
      gvs[]) >>
  strip_tac >> `n = mi` by
    (irule all_distinct_inst_id_idx >> qexists_tac `insts` >> simp[]) >>
  gvs[]
QED

Theorem transform_block_dload_phi_mem:
  !dfg bb inst.
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI ==>
    MEM inst (transform_block_dload dfg bb).bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM inst.inst_id
    (MAP (\dp. dp.dp_dload_id) (find_dload_pairs dfg bb.bb_instructions))` by
    (simp[MEM_MAP] >> rpt strip_tac >>
     fs[EVERY_MEM] >> res_tac >> drule_all dload_pair_wf_phi_ids >> simp[]) >>
  `ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
    (find_dload_pairs dfg bb.bb_instructions)) inst.inst_id = NONE` by
    (Cases_on `ALOOKUP (MAP (\dp. (dp.dp_mstore_id, dp))
       (find_dload_pairs dfg bb.bb_instructions)) inst.inst_id` >> simp[] >>
     imp_res_tac ALOOKUP_MEM >> fs[MEM_MAP, EVERY_MEM] >> res_tac >>
     drule_all dload_pair_wf_phi_ids >> simp[]) >>
  simp[transform_block_dload_def, MEM_MAP] >>
  qexists_tac `inst` >> fs[MEM_MAP] >> IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem bb_well_formed_head_non_phi:
  !bb inst rest.
    bb_well_formed bb /\ bb.bb_instructions = inst::rest /\
    inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_MEM, MEM_EL] >>
  rpt strip_tac >> Cases_on `n` >> gvs[] >>
  rename1 `(EL k rest).inst_opcode = PHI` >>
  fs[bb_well_formed_def] >>
  first_x_assum (qspecl_then [`0`, `SUC k`] mp_tac) >> simp[]
QED

Theorem mm_run_block_error_or_no_phis:
  !dfg bb fuel ctx s.
    bb_well_formed bb /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    memzero_block_wf dfg (transform_block_dload dfg bb) ==>
    (?e. run_block fuel ctx bb s = Error e) \/
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bb.bb_instructions` >- fs[bb_well_formed_def] >>
  rename1 `bb.bb_instructions = inst::rest` >>
  Cases_on `inst.inst_opcode = PHI`
  >- (DISJ1_TAC >>
      `MEM inst (transform_block_dload dfg bb).bb_instructions` by
        (irule transform_block_dload_phi_mem >> simp[]) >>
      `inst.inst_operands = []` by
        (drule_all memzero_block_wf_phi_empty >> simp[]) >>
      simp[run_block_def, eval_phis_def, eval_one_phi_def, resolve_phi_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >>
      Cases_on `outs` >> simp[] >> Cases_on `s.vs_prev_bb` >> simp[]) >>
  DISJ2_TAC >> drule_all bb_well_formed_head_non_phi >> simp[]
QED

Theorem apply_memzero_inst_no_phis[local]:
  !nop_set rep_map inst.
    inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (apply_memzero_inst nop_set rep_map inst)
Proof
  rpt strip_tac >> rw[apply_memzero_inst_def, LET_THM] >>
  rpt CASE_TAC >> simp[mk_nop_from_def, mk_zero_store_inst_def,
    mk_calldatasize_inst_def, mk_memzero_calldatacopy_def]
QED

Theorem apply_groups_inst_no_phis[local]:
  !mode nop_set rep_map inst.
    inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (apply_groups_inst mode nop_set rep_map inst)
Proof
  rpt strip_tac >> rw[apply_groups_inst_def, LET_THM] >>
  rpt CASE_TAC >>
  simp[mk_nop_from_def, mk_bulk_copy_inst_def, mk_load_inst_def,
    mk_mstore_from_load_def] >> Cases_on `mode` >>
  simp[mode_copy_opcode_def, mode_load_opcode_def]
QED

Theorem transform_block_dload_no_phis[local]:
  !dfg bb.
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> PHI)
      (transform_block_dload dfg bb).bb_instructions
Proof
  simp[transform_block_dload_def, LET_THM, EVERY_MAP] >> simp[EVERY_MEM] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[mk_nop_from_def] >> CASE_TAC >>
  simp[mk_dloadbytes_inst_def] >> res_tac
QED

Theorem transform_block_memzero_no_phis[local]:
  !dfg bb.
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> PHI)
      (transform_block_memzero dfg bb).bb_instructions
Proof
  simp[transform_block_memzero_def, LET_THM, EVERY_FLAT, EVERY_MAP] >>
  rpt strip_tac >> irule EVERY_MONOTONIC >>
  qexists_tac `\i. i.inst_opcode <> PHI` >>
  simp[apply_memzero_inst_no_phis]
QED

Theorem transform_block_mode_no_phis[local]:
  !dfg mode bb.
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> PHI)
      (transform_block_mode dfg mode bb).bb_instructions
Proof
  simp[transform_block_mode_def, LET_THM, EVERY_FLAT, EVERY_MAP] >>
  rpt strip_tac >> irule EVERY_MONOTONIC >>
  qexists_tac `\i. i.inst_opcode <> PHI` >>
  simp[apply_groups_inst_no_phis]
QED

Theorem transform_block_no_phis:
  !dfg bb.
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\i. i.inst_opcode <> PHI) (transform_block dfg bb).bb_instructions
Proof
  simp[transform_block_def] >> rpt strip_tac >>
  rpt (irule transform_block_mode_no_phis) >>
  irule transform_block_memzero_no_phis >>
  irule transform_block_dload_no_phis >> simp[]
QED

(* Lift a zero-index exec_block simulation under the existing WF contract.
   PHIs admitted by that contract fail; non-error blocks are PHI-free. *)
Theorem mm_run_block_from_exec_sim:
  !dfg bb fuel ctx s1 s2 R S T.
    bb_well_formed bb /\
    EVERY (\dp. dload_pair_wf dfg dp bb.bb_instructions)
      (find_dload_pairs dfg bb.bb_instructions) /\
    memzero_block_wf dfg (transform_block_dload dfg bb) ==>
    ((?e. exec_block fuel ctx bb (s1 with vs_inst_idx := 0) = Error e) \/
     lift_result R S T
       (exec_block fuel ctx bb (s1 with vs_inst_idx := 0))
       (exec_block fuel ctx (transform_block dfg bb) (s2 with vs_inst_idx := 0)))
    ==>
    (?e. run_block fuel ctx bb s1 = Error e) \/
    lift_result R S T (run_block fuel ctx bb s1)
      (run_block fuel ctx (transform_block dfg bb) s2)
Proof
  rpt gen_tac >> strip_tac >> disch_tac >>
  drule_all mm_run_block_error_or_no_phis >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s1`] mp_tac) >>
  strip_tac >- simp[] >>
  `EVERY (\i. i.inst_opcode <> PHI)
     (transform_block dfg bb).bb_instructions` by
    (irule transform_block_no_phis >> simp[]) >>
  simp[run_block_no_phis_eq_exec_block]
QED
