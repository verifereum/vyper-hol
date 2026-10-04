(* Block-entry interface for memmerging's existing contracts.
   Their universally quantified freshness condition excludes Var operands.
   Thus a structurally valid PHI at entry has no incoming operands and errors;
   otherwise block entry reduces to the existing exec_block simulation. *)
Theory mmEntryProofs
Ancestors
  mmWfProofs mmCorrectnessProofs mmTransform mmScan
  venomExecProofs venomExecSemantics venomWf venomInst venomState
  list rich_list pred_set

Theorem memzero_block_wf_no_var_operands:
  !dfg bb inst.
    memzero_block_wf dfg bb /\ MEM inst bb.bb_instructions /\
    ~is_terminator inst.inst_opcode ==>
    !x. ~MEM (Var x) inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `memzero_block_wf _ _` mp_tac >>
  simp[Once memzero_block_wf_def, LET_THM] >> strip_tac >>
  qpat_x_assum `!fresh. _ SUBSET fresh ==> EVERY _ _`
    (qspec_then `UNIV` mp_tac) >>
  simp[EVERY_MEM, MEM_FILTER] >>
  disch_then (qspec_then `inst` mp_tac) >> simp[] >>
  disch_then (mp_tac o last o CONJUNCTS o REWRITE_RULE [memzero_inst_ok_def]) >>
  simp[]
QED

Theorem phi_well_formed_no_vars:
  !ops. phi_well_formed ops /\ (!x. ~MEM (Var x) ops) ==> ops = []
Proof
  ho_match_mp_tac phi_well_formed_ind >>
  simp[phi_well_formed_def, MEM] >> metis_tac[]
QED

Theorem memzero_after_dload_phi_empty:
  !fn bb inst.
    wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
    memzero_block_wf (dfg_build_function fn)
      (transform_block_dload (dfg_build_function fn) bb) ==>
    inst.inst_operands = []
Proof
  rpt strip_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  drule_all phi_id_not_in_dload_nops >> strip_tac >>
  qpat_x_assum `!dfg. _`
    (qspec_then `dfg_build_function fn` assume_tac) >>
  drule_all phi_id_not_in_mstore_map >> strip_tac >>
  `MEM inst (transform_block_dload (dfg_build_function fn) bb).bb_instructions` by
    (simp[transform_block_dload_def, LET_THM] >>
     ONCE_REWRITE_TAC[MEM_MAP] >> qexists_tac `inst` >> simp[]) >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> res_tac) >>
  `phi_well_formed inst.inst_operands` by
    (qpat_x_assum `inst_wf inst` mp_tac >>
     ASM_REWRITE_TAC[inst_wf_def, opcode_case_def] >> simp[]) >>
  qspecl_then [`dfg_build_function fn`,
    `transform_block_dload (dfg_build_function fn) bb`, `inst`]
    mp_tac memzero_block_wf_no_var_operands >>
  (impl_tac >- simp[is_terminator_def]) >> strip_tac >>
  irule phi_well_formed_no_vars >> simp[]
QED

Theorem transform_block_dload_no_phis:
  !dfg bb.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (transform_block_dload dfg bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[transform_block_dload_def, LET_THM, EVERY_MAP] >>
  irule EVERY_MONOTONIC >>
  qexists_tac `\inst. inst.inst_opcode <> PHI` >> simp[] >>
  rpt strip_tac >> BasicProvers.every_case_tac >>
  gvs[mk_nop_from_def, mk_dloadbytes_inst_def]
QED

Theorem transform_block_memzero_no_phis:
  !dfg bb.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (transform_block_memzero dfg bb).bb_instructions
Proof
  simp[transform_block_memzero_def, LET_THM, EVERY_FLAT, EVERY_MAP,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> metis_tac[apply_memzero_inst_non_phi]
QED

Theorem transform_block_mode_no_phis:
  !dfg mode bb.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (transform_block_mode dfg mode bb).bb_instructions
Proof
  simp[transform_block_mode_def, LET_THM, EVERY_FLAT, EVERY_MAP,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> metis_tac[apply_groups_inst_non_phi]
QED

Theorem transform_block_no_phis:
  !dfg bb.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (transform_block dfg bb).bb_instructions
Proof
  simp[transform_block_def, LET_THM] >> rpt strip_tac >>
  rpt (irule transform_block_mode_no_phis) >>
  irule transform_block_memzero_no_phis >>
  irule transform_block_dload_no_phis >> simp[]
QED

Theorem eval_one_phi_empty_operands:
  !s inst. inst.inst_operands = [] ==> eval_one_phi s inst = NONE
Proof
  rpt strip_tac >> simp[eval_one_phi_def] >>
  BasicProvers.every_case_tac >> gvs[resolve_phi_def]
QED

Theorem well_formed_non_phi_head:
  !bb head rest.
    bb_well_formed bb /\ bb.bb_instructions = head::rest /\
    head.inst_opcode <> PHI ==>
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions
Proof
  rpt strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  CCONTR_TAC >>
  qspecl_then [`bb`, `n`, `0`] mp_tac phi_before_non_phi >> simp[]
QED
