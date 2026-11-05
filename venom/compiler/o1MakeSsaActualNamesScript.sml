Theory o1MakeSsaActualNames
Ancestors
  o1MakeSsaVisitRetention o1MakeSsaVisitNames o1MakeSsaRootedTree
  o1MakeSsaActualMaps o1MakeSsaVisitPaths o1MakeSsaPrefixNames
  o1MakeSsaVisitTrace o1MakeSsaEventFrames o1MakeSsaTraversalFrames
  o1MakeSsaFormats o1MakeSsaPreparation makeSsaCurrentDefs list alist pair o1ContractMakeSsaSrcOpcodes makeSsaCurrentTraceCertificate makeSsaCurrentTreeTrace

(* latest_current_name of the initial rename state is the identity *)
val _ = augment_srw_ss [rewrites [makeSsaCurrentTreeTraceTheory.current_initial_latest]];

Theorem actual_phi_slot_name:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  rename_current_blocks s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn) = (ct,t,final) /\
  block_slot q n j p x bbs /\
  MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) /\
  e.sve_label = p /\ MEM q e.sve_succs ==>
  block_slot q n j p
    (last_name x x (path_pairs
      (e.sve_path ++ [(p,e.sve_before,e.sve_after)]))) final
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_postorder (current_dom_tree fn))` by
    metis_tac[actual_rooted_tree_distinct] >>
  `!l ss. ALOOKUP (current_succ_map fn) l = SOME ss ==> ALL_DISTINCT ss` by
    metis_tac[current_actual_succs_distinct] >>
  `visit_blocks [] s (init_current_rename_state defs) bbs
     (current_succ_map fn) (current_dom_tree fn) =
     ((ct,t,final), SND (visit_blocks [] s (init_current_rename_state defs) bbs
       (current_succ_map fn) (current_dom_tree fn)))` by
    metis_tac[visit_erasure, PAIR] >>
  drule_all visit_slot_retained >>
  drule visit_event_names >> simp[]
QED

Theorem actual_phi_slot_unchanged:
  wf_function fn /\
  rename_current_blocks s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn) = (ct,t,final) /\
  block_slot q n j p x bbs /\
  (!e. MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) ==>
    e.sve_label <> p \/ ~MEM q e.sve_succs) ==>
  block_slot q n j p x final
Proof
  rpt strip_tac >>
  `!l ss. ALOOKUP (current_succ_map fn) l = SOME ss ==> ALL_DISTINCT ss` by
    metis_tac[current_actual_succs_distinct] >>
  `visit_blocks [] s (init_current_rename_state defs) bbs
     (current_succ_map fn) (current_dom_tree fn) =
     ((ct,t,final), SND (visit_blocks [] s (init_current_rename_state defs) bbs
       (current_succ_map fn) (current_dom_tree fn)))` by
    metis_tac[visit_erasure, PAIR] >>
  drule_all visit_slot_unchanged >> simp[]
QED

Theorem visit_local_rename:
  (!tree path s rs bbs sm.
    EVERY (\e. rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
      (e.sve_out,e.sve_supply_out,e.sve_after))
      (SND (visit_blocks path s rs bbs sm tree))) /\
  (!trees path s ctrs stacks bbs sm.
    EVERY (\e. rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
      (e.sve_out,e.sve_supply_out,e.sve_after))
      (SND (visit_children path s ctrs stacks bbs sm trees)))
Proof
  ho_match_mp_tac makeSsaCurrentInductTheory.current_dom_tree_induction >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[Once visit_blocks_def] >> Cases_on `lookup_block lbl bbs` >> simp[] >>
      rpt (pairarg_tac >> gvs[]) >> simp[] >> metis_tac[SND])
  >- simp[visit_blocks_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> simp[Once visit_blocks_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[] >> metis_tac[SND]
QED

Theorem actual_event_operand_name:
  MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) /\
  i < LENGTH e.sve_before /\ (EL i e.sve_before).inst_opcode <> PHI /\
  j < LENGTH (EL i e.sve_before).inst_operands /\
  EL j (EL i e.sve_before).inst_operands = Var x ==>
  EL j (EL i e.sve_after).inst_operands = Var
    (last_name x x (path_pairs e.sve_path ++
      block_output_pairs (TAKE i e.sve_before) (TAKE i e.sve_after)))
Proof
  rpt strip_tac >>
  `rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
    (e.sve_out,e.sve_supply_out,e.sve_after)` by
    (drule (SRULE [EVERY_MEM] (cj 1 visit_local_rename)) >> simp[]) >>
  drule_all block_operand_prefix_name >>
  drule visit_event_names >> simp[last_name_append]
QED

Theorem actual_final_operand_name:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  rename_current_blocks s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn) = (ct,t,final) /\
  MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) /\
  i < LENGTH e.sve_before /\ (EL i e.sve_before).inst_opcode <> PHI /\
  j < LENGTH (EL i e.sve_before).inst_operands /\
  EL j (EL i e.sve_before).inst_operands = Var x ==>
  ?out. lookup_block e.sve_label final = SOME out /\
    EL j (EL i out.bb_instructions).inst_operands = Var
      (last_name x x (path_pairs e.sve_path ++
        block_output_pairs (TAKE i e.sve_before) (TAKE i e.sve_after)))
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_postorder (current_dom_tree fn))` by
    metis_tac[actual_rooted_tree_distinct] >>
  `visit_blocks [] s (init_current_rename_state defs) bbs
     (current_succ_map fn) (current_dom_tree fn) =
     ((ct,t,final), SND (visit_blocks [] s (init_current_rename_state defs) bbs
       (current_succ_map fn) (current_dom_tree fn)))` by
    metis_tac[visit_erasure, PAIR] >>
  `rename_current_block_insts e.sve_supply_in e.sve_in e.sve_before =
    (e.sve_out,e.sve_supply_out,e.sve_after)` by
    (drule (SRULE [EVERY_MEM] (cj 1 visit_local_rename)) >> simp[]) >>
  drule rename_current_block_insts_opcodes >> strip_tac >>
  drule_all (cj 1 visit_event_final_frame) >> strip_tac >>
  drule_all actual_event_operand_name >> strip_tac >>
  `LENGTH e.sve_after = LENGTH e.sve_before` by metis_tac[LENGTH_MAP] >>
  `(EL i e.sve_after).inst_opcode = (EL i e.sve_before).inst_opcode` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `EL i`) >> simp[EL_MAP]) >>
  gvs[indexed_patch_frame_def] >> metis_tac[]
QED

Theorem actual_event_input_frame:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) /\
  lookup_block e.sve_label bbs = SOME bb ==>
  indexed_patch_frame bb (bb with bb_instructions := e.sve_before)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (dom_tree_postorder (current_dom_tree fn))` by
    metis_tac[actual_rooted_tree_distinct] >>
  Cases_on `visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn)` >>
  PairCases_on `q` >> gvs[] >> drule_all (cj 1 visit_event_input_frame) >> simp[]
QED

Theorem actual_prepared_event_positions:
  wf_function fn /\ fn_entry_label fn = SOME entry /\
  add_phi_nodes_supply sp df pm li orig vdefs = (bbs,s) /\
  lookup_block e.sve_label orig = SOME old /\
  MEM e (SND (visit_blocks [] s (init_current_rename_state defs) bbs
    (current_succ_map fn) (current_dom_tree fn))) ==>
  ?pre. EVERY (\i. i.inst_opcode = PHI) pre /\
    LENGTH e.sve_before = LENGTH pre + LENGTH old.bb_instructions /\
    !i. i < LENGTH old.bb_instructions ==>
      (EL (LENGTH pre + i) e.sve_before).inst_opcode =
        (EL i old.bb_instructions).inst_opcode /\
      (EL (LENGTH pre + i) e.sve_before).inst_outputs =
        (EL i old.bb_instructions).inst_outputs /\
      ((EL i old.bb_instructions).inst_opcode <> PHI ==>
        EL (LENGTH pre + i) e.sve_before = EL i old.bb_instructions)
Proof
  rpt strip_tac >> drule_all prepared_add_phi_lookup >> strip_tac >>
  drule_all actual_event_input_frame >>
  simp[indexed_patch_frame_def] >> strip_tac >>
  qexists `pre` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `LENGTH pre + i` mp_tac) >>
  simp[EL_APPEND_EQN]
QED
