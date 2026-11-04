Theory makeSsaCurrentOrdinaryIds
Ancestors makeSsaCurrentSourceCuts makeSsaCurrentPhaseShape makeSsaCurrentRenameTrace
  makeSsaCurrentFinalBlock makeSsaCurrentTreeTrace makeSsaCurrentCleanupShape
  makeSsaCurrentDefs makeSsaCurrentTreePaths venomInst irSupply list rich_list

(* Cleanup reassigns all positions, but the ordinary suffix stays at the
   same positions, so both its fields and its original IDs are preserved. *)
Theorem current_cleanup_block_ordinary_instruction:
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail ==>
  EL (LENGTH pre + i) (simplify_current_phi_block bb).bb_instructions = EL i tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all current_cleanup_block_ordinary_index >> strip_tac >>
  mp_tac (Q.SPEC `bb` (GEN_ALL simplify_current_phi_block_ids)) >>
  pure_rewrite_tac[block_ir_inst_ids_def] >>
  disch_then (mp_tac o Q.AP_TERM `EL (LENGTH (pre:instruction list) + i)`) >>
  simp[EL_MAP, current_cleanup_block_length, EL_APPEND_EQN] >> strip_tac >>
  gvs[current_inst_no_id_def, instruction_component_equality]
QED

Theorem current_inst_trace_id:
  current_inst_trace anns inst s rs H E inst' s' rs' H' E' ==>
  inst'.inst_id = inst.inst_id
Proof
  simp[current_inst_trace_def] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem current_event_ordinary_instruction:
  current_event_trace A H
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  bb.bb_instructions = pre ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) pre /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH tail /\
  (EL i tail).inst_opcode <> PHI ==>
  EL (LENGTH pre + i)
    (if enabled then simplify_current_phi_block
       (current_replay_edges sm later (bb with bb_instructions := ren))
     else current_replay_edges sm later (bb with bb_instructions := ren)).bb_instructions =
  EL (LENGTH pre + i) ren
Proof
  simp[current_event_trace_def] >> rpt strip_tac >>
  drule current_local_trace_opcodes >> strip_tac >>
  qspecl_then [`later`, `bb with bb_instructions := ren`] assume_tac
    current_replay_edges_shape >>
  drule current_edge_shape_opcodes >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `simplify_current_phi_block rb` >>
  `MAP instruction_inst_opcode rb.bb_instructions =
    MAP instruction_inst_opcode pre ++ MAP instruction_inst_opcode tail` by
    metis_tac[MAP_APPEND] >>
  `?rp rt. rb.bb_instructions = rp ++ rt /\
    MAP instruction_inst_opcode rp = MAP instruction_inst_opcode pre /\
    MAP instruction_inst_opcode rt = MAP instruction_inst_opcode tail` by
    metis_tac[MAP_EQ_APPEND] >>
  fs[MAP_EQ_EVERY2, LIST_REL_EL_EQN] >>
  `EVERY (\inst. inst.inst_opcode = PHI) rp` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `(HD rt).inst_opcode <> PHI /\ i < LENGTH rt` by
    (Cases_on `rt` >> Cases_on `tail` >> gvs[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `i + LENGTH pre < LENGTH ren` by fs[] >>
  `(EL (i + LENGTH pre) ren).inst_opcode <> PHI` by
    (qpat_x_assum `!n. _ ==> (EL n ren).inst_opcode = _`
      (qspec_then `i + LENGTH pre` mp_tac) >> simp[EL_APPEND_EQN]) >>
  `EL (i + LENGTH pre) rb.bb_instructions = EL (i + LENGTH pre) ren` by
    (fs[current_edge_shape_def, LIST_REL_EL_EQN]) >>
  `EL (LENGTH rp + i) (simplify_current_phi_block rb).bb_instructions = EL i rt` by
    (irule current_cleanup_block_ordinary_instruction >> simp[] >> metis_tac[]) >>
  `EL i rt = EL (i + LENGTH pre) ren` by
    (qpat_x_assum `EL _ rb.bb_instructions = _` mp_tac >> simp[EL_APPEND_EQN]) >>
  Cases_on `enabled` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

(* Source-linked suffix position, before ID erasure. The selected source and
   target instructions directly satisfy the interpreter's equal-ID premise. *)
Theorem current_certificate_ordinary_id_position:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  events = before ++ (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after /\
  lookup_block l fn.fn_blocks = SOME old /\
  old.bb_instructions = phis ++ tail /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\
  j < LENGTH tail /\ (EL j tail).inst_opcode <> PHI /\ i = LENGTH phis + j ==>
  ?ip out.
    EVERY (\inst. inst.inst_opcode = PHI) ip /\
    current_edge_shape
      (old with bb_instructions := ip ++ old.bb_instructions) bb /\
    lookup_block l fn'.fn_blocks = SOME out /\
    EL (LENGTH ip + i) out.bb_instructions = EL (LENGTH ip + i) ren /\
    (EL (LENGTH ip + i) out.bb_instructions).inst_id =
      (EL i old.bb_instructions).inst_id
Proof
  strip_tac >> gvs[] >>
  drule current_certificate_source_shape >>
  disch_then (qspecl_then [`old`,
    `(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`] mp_tac) >>
  simp[current_event_label_def, current_event_input_block_def] >> strip_tac >>
  `?bp bt. bb.bb_instructions = bp ++ bt /\
     LENGTH bp = LENGTH pre + LENGTH phis /\ LENGTH bt = LENGTH tail /\
     EVERY (\inst. inst.inst_opcode = PHI) bp /\
     (bt = [] \/ (HD bt).inst_opcode <> PHI) /\ EL j bt = EL j tail` by
    (drule current_edge_shape_ordinary_partition >>
     disch_then (qspecl_then [`tail`, `pre ++ phis`, `j`] mp_tac) >>
     simp[EVERY_APPEND, APPEND_ASSOC]) >> gvs[] >>
  `LENGTH bp + j < LENGTH bb.bb_instructions` by simp[] >>
  `EL (LENGTH bp + j) bb.bb_instructions = EL j tail` by simp[EL_APPEND_EQN] >>
  `?rs E. current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (LENGTH bp + j) rs E` by
    metis_tac[current_source_cut_exists, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  drule_all current_source_cut_step >> strip_tac >>
  drule current_inst_trace_id >> strip_tac >>
  `EL (LENGTH bp + j)
     (if blocks_have_leading_phi fn.fn_blocks then
       simplify_current_phi_block
         (current_replay_edges (current_succ_map fn)
           ((l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after)
           (bb with bb_instructions := ren))
      else current_replay_edges (current_succ_map fn)
           ((l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)::after)
           (bb with bb_instructions := ren)).bb_instructions =
    EL (LENGTH bp + j) ren` by
    (irule current_event_ordinary_instruction >> simp[] >> metis_tac[]) >>
  drule current_structural_certificate_final_event >>
  disch_then (qspecl_then
    [`(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2)`, `eb`, `before`, `after`] mp_tac) >>
  simp[current_event_label_def, current_event_renamed_block_def] >> strip_tac >>
  qexists_tac `pre` >> goal_assum $ drule_at Any >>
  fs[EL_APPEND_EQN, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
