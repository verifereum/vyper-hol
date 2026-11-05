Theory o1MakeSsaActualNames
Ancestors
  o1MakeSsaVisitRetention o1MakeSsaVisitNames o1MakeSsaRootedTree
  o1MakeSsaActualMaps o1MakeSsaVisitPaths o1MakeSsaPrefixNames
  o1MakeSsaVisitTrace makeSsaCurrentDefs list alist pair

Theorem initial_current_name[simp]:
  !defs x. latest_current_name (init_current_rename_state defs) x = x
Proof
  Induct >> simp[init_current_rename_state_def, latest_current_name_def] >>
  Cases_on `h` >> simp[] >> rpt gen_tac >> IF_CASES_TAC >> gvs[init_current_rename_state_def, latest_current_name_def]
QED

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
    metis_tac[actual_succ_map_distinct] >>
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
    metis_tac[actual_succ_map_distinct] >>
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
