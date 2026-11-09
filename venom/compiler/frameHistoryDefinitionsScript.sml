Theory frameHistoryDefinitions
Ancestors frameHistoryCompleted frameHistoryInstructions frameHistoryCfg
  frameExecutionHistory frameCfgBoundary contextCodegenRel venomWf venomInstProps
  venomExecProofs venomExecSemantics venomState venomInst list rich_list

Theorem history_available_definition:
  wf_function fn /\ frame_history_cfg fn h /\
  history_instruction_prefix fn h /\ history_completed_blocks fn h /\
  h <> [] /\ LAST h = (inst,s) /\ active_inst fn inst s /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  def_on_all_paths fn bb (SOME inst) v /\
  (!j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst ==>
       j = s.vs_inst_idx) ==>
  (?di ds. MEM (di,ds) (FRONT h) /\ active_inst fn di ds /\
           MEM v di.inst_outputs) \/
  (?db k. MEM db fn.fn_blocks /\ MEM db.bb_label (history_visits h) /\
          k < phi_prefix_length db.bb_instructions /\
          k < LENGTH db.bb_instructions /\
          MEM v (EL k db.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `(?k db di. k < LENGTH (history_visits h) - 1 /\
      MEM db fn.fn_blocks /\ db.bb_label = EL k (history_visits h) /\
      MEM di db.bb_instructions /\ MEM v di.inst_outputs) \/
   (?i j. i < LENGTH bb.bb_instructions /\
      MEM v (EL i bb.bb_instructions).inst_outputs /\
      i < j /\ j < LENGTH bb.bb_instructions /\
      EL j bb.bb_instructions = inst)` by
    (qpat_x_assum `def_on_all_paths _ _ _ _` mp_tac >>
     simp[def_on_all_paths_def] >>
     disch_then (qspec_then `history_visits h` mp_tac) >>
     gvs[frame_history_cfg_def] >> metis_tac[]) >>
  all_tac
  >- (
      `?n. n < LENGTH db.bb_instructions /\ EL n db.bb_instructions = di` by
        metis_tac[MEM_EL] >>
      `MEM db.bb_label (FRONT (history_visits h))` by
        (gvs[frame_history_cfg_def] >>
         simp[MEM_EL] >> qexists `k` >> simp[LENGTH_FRONT] >> sym_tac >> irule EL_FRONT >> simp[LENGTH_FRONT, NULL_EQ]) >>
      Cases_on `n < phi_prefix_length db.bb_instructions`
      >- (disj2_tac >> qexistsl [`db`, `n`] >> simp[] >>
          simp[MEM_EL] >> qexists `k` >> simp[]) >>
      disj1_tac >>
      `?old_inst old_s. MEM (old_inst,old_s) (FRONT h) /\
        active_inst fn old_inst old_s /\ old_inst = EL n db.bb_instructions` by
        (gvs[history_completed_blocks_def] >>
         `phi_prefix_length db.bb_instructions <= n` by decide_tac >>
         metis_tac[]) >>
      metis_tac[]) >>
  `j = s.vs_inst_idx` by metis_tac[] >>
  Cases_on `i < phi_prefix_length bb.bb_instructions`
  >- (disj2_tac >> qexistsl [`bb`, `i`] >> simp[] >>
      gvs[frame_history_cfg_def] >> metis_tac[MEM_LAST_NOT_NIL]) >>
  disj1_tac >>
  gvs[history_instruction_prefix_def] >>
  `phi_prefix_length bb.bb_instructions <= i` by decide_tac >>
  metis_tac[]
QED

Theorem active_instruction_unique_index:
  wf_function fn /\ active_inst fn inst s /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ j < LENGTH bb.bb_instructions /\
  EL j bb.bb_instructions = inst ==> j = s.vs_inst_idx
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (qpat_x_assum `wf_function fn` mp_tac >>
     simp[wf_function_def, fn_inst_ids_distinct_def] >> strip_tac >>
     qpat_x_assum `ALL_DISTINCT (FLAT _)` mp_tac >>
     qpat_x_assum `MEM bb fn.fn_blocks` mp_tac >>
     qspec_tac (`fn.fn_blocks`, `bbs`) >>
     Induct >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  gvs[active_inst_def] >>
  `bb = bb'` by metis_tac[same_label_same_block] >> gvs[] >>
  drule (iffLR ALL_DISTINCT_EL_IMP) >>
  simp[EL_MAP] >> metis_tac[]
QED

Theorem frame_history_active:
  !vs0 ctx stk PG G tn fn inst s hs h.
  frame_history vs0 ctx stk PG G tn fn inst s hs h ==> active_inst fn inst s
Proof
  ho_match_mp_tac frame_history_ind >> simp[]
QED

Theorem frame_history_ordinary_use_definition:
  frame_history vs0 ctx stk PG G tn fn inst s hs h /\
  EVERY wf_function ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands ==>
  (?di ds. MEM (di,ds) (FRONT h) /\ active_inst fn di ds /\
           MEM v di.inst_outputs) \/
  (?db k. MEM db fn.fn_blocks /\ MEM db.bb_label (history_visits h) /\
          k < phi_prefix_length db.bb_instructions /\
          k < LENGTH db.bb_instructions /\
          MEM v (EL k db.bb_instructions).inst_outputs)
Proof
  strip_tac >> drule frame_history_cfg_invariant >> simp[] >> strip_tac >>
  drule_all frame_history_current_instruction_prefix >> strip_tac >>
  drule_all frame_history_current_completed >> strip_tac >>
  drule frame_history_active >> strip_tac >>
  `wf_function fn /\ fn_defs_reach_uses fn` by metis_tac[EVERY_MEM] >>
  `?bb. MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
        MEM inst bb.bb_instructions` by
    (gvs[active_inst_def] >> metis_tac[EL_MEM]) >>
  irule history_available_definition >> goal_assum (drule_at Any) >> simp[] >>
  qexists `bb` >> simp[] >> conj_tac
  >- metis_tac[active_instruction_unique_index] >>
  gvs[fn_defs_reach_uses_def] >> metis_tac[]
QED
