Theory fmpStageFmpStepsRetpcAnalysis
Ancestors
  fmpStageRel fmpLowerReclaimPlan fmpLedgerProps fmpReclaimDefs
  fmpAnalysisDefs dfAnalyzeDefs venomInst finite_map list

Theorem fmp_retpc_analysis_suc:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  EL k bb.bb_instructions = inst /\ inst.inst_opcode = RETPC_PARAM /\
  df_at NONE states bb.bb_label k = SOME st ==>
  ?st1. df_at NONE states bb.bb_label (SUC k) = SOME st1 /\
        st1.frs_stack = st.frs_stack
Proof
  strip_tac >> drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_parameter]
QED

Theorem fmp_retpc_empty_link:
  fmp_sites_ok sm fmp0 raw0 lo raw_fmp ==>
  fmp_ledger_link sm eb lo []
Proof
  simp[fmp_sites_ok_def, fmp_ledger_link_def] >>
  metis_tac[]
QED
