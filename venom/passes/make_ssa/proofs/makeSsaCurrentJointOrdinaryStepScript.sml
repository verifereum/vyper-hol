Theory makeSsaCurrentJointOrdinaryStep
Ancestors makeSsaCurrentOrdinaryJoint makeSsaCurrentCleanedOrdinary
  makeSsaCurrentOriginalFinalSlots makeSsaCurrentFinalWriteSlots
  makeSsaCurrentInstructionSingleton makeSsaCurrentJointRuntime
  makeSsaCurrentChronologicalTransition makeSsaCurrentAllocation
  makeSsaCurrentValueInvariant makeSsaCurrentRenameTrace
  makeSsaCurrentTreeTrace makeSsaCurrentActualRetention makeSsaCurrentInduct
  makeSsaCurrentSourceCuts venomWf list

Theorem current_original_step_joint_singleton:
  current_inst_trace anns inst s rs H E inst' s' rt H' E' /\
  current_annotations_ok U H anns /\
  current_allocation_consistent U H s rs /\ current_env_realizes H E rs U /\
  current_env_history_owners H E /\ (!v. MEM v D ==> MEM v U) /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  inst = EL i (EL b fn.fn_blocks).bb_instructions /\
  current_history_valid Ufinal Hfinal /\
  LENGTH inst'.inst_outputs = LENGTH inst.inst_outputs /\
  (!k. k < LENGTH inst'.inst_outputs ==>
    current_token_name Hfinal (CurrentOriginal (EL b fn.fn_blocks).bb_label i k) =
      SOME (EL k inst'.inst_outputs)) /\
  current_joint_rel V M N rs
    (venomInst$operand_vars inst.inst_operands ++ current_before_outputs inst.inst_outputs D) st st' /\
  current_singleton_agree (current_instruction_singleton_table fn Hfinal) st st' /\
  step_inst_base inst st = OK after ==>
  current_allocation_consistent U H' s' rt /\ current_env_realizes H' E' rt U /\
  current_env_history_owners H' E' /\
  ?n events after'.
    step_inst_base inst' st' = OK after' /\
    current_indexed_writes inst.inst_outputs events st after /\
    current_indexed_writes inst'.inst_outputs events st' after' /\
    MAP FST events = GENLIST I (LENGTH inst.inst_outputs) /\
    current_joint_rel (current_event_valuation V visit l i n events)
      (current_event_origins inst.inst_outputs M visit l i n events)
      (current_event_origins inst'.inst_outputs N visit l i n events) rt D after after' /\
    current_singleton_agree (current_instruction_singleton_table fn Hfinal) after after'
Proof
  strip_tac >>
  `current_table_final_slots (current_instruction_singleton_table fn Hfinal)
    inst.inst_outputs inst'.inst_outputs` by
    (gvs[] >> irule current_original_output_final_slots >> metis_tac[]) >>
  drule_all current_inst_trace_ordinary_joint >>
  disch_then (qspecl_then [`visit`, `l`, `i`] strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`n`, `events`, `after'`] >> asm_rewrite_tac[] >>
  drule_all current_singleton_agree_final_slots >> simp[]
QED

Theorem current_local_trace_remaining_annotations:
  !annss insts s rs H E insts' s' rt H' E' rest U.
  current_local_trace annss insts s rs H E insts' s' rt H' E' /\
  current_annotations_ok U H (FLAT annss ++ rest) ==>
  current_annotations_ok U H' rest
Proof
  Induct >> simp[current_local_trace_def] >> rpt gen_tac >> strip_tac >>
  `current_annotations_ok U H1 (FLAT annss ++ rest)` by
    (irule current_outputs_trace_remaining >>
     fs[current_inst_trace_def] >> metis_tac[APPEND_ASSOC]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem current_tree_trace_local_entry_owners:
  (!tree A sm s rs bbs H E visited ctrs' s' bbs' H' visited' events.
    current_tree_trace A sm tree s rs bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2).
      current_env_history_owners H0 E0) events) /\
  (!trees A sm s ctrs stacks bbs H E visited ctrs' s' bbs' H' visited' events.
    current_children_trace A sm trees s ctrs stacks bbs H E visited
      ctrs' s' bbs' H' visited' events /\ current_env_history_owners H E ==>
    EVERY (\(l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2).
      current_env_history_owners H0 E0) events)
Proof
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >>
      simp[current_tree_trace_def] >>
      Cases_on `lookup_block lbl bbs` >> simp[] >> strip_tac >> gvs[] >>
      drule_all current_local_trace_history_owners >> strip_tac >>
      first_x_assum drule_all >> simp[]) 
  >- simp[current_tree_trace_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[current_tree_trace_def] >> strip_tac >> gvs[] >>
  `?tail. H1 = H ++ tail` by metis_tac[cj 1 current_tree_trace_history] >>
  `current_env_history_owners H1 E` by metis_tac[current_env_history_owners_append] >>
  last_x_assum drule_all >> strip_tac >>
  last_x_assum drule_all >> simp[]
QED

Theorem current_certificate_local_entry_owners:
  current_structural_certificate s fn fn' s' A H events /\
  MEM (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) events ==>
  current_env_history_owners H0 E0
Proof
  simp[current_structural_certificate_def] >> rpt strip_tac >>
  drule (cj 1 current_tree_trace_local_entry_owners) >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED

Theorem current_source_cut_ready:
  current_event_valid A U
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_env_history_owners H0 E0 /\
  current_source_cut A
    (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) n rs E /\
  n < LENGTH bb.bb_instructions ==>
  ?sm Hm sn rn Hn En.
    current_inst_trace (EL n (A l)) (EL n bb.bb_instructions)
      sm rs Hm E (EL n ren) sn rn Hn En /\
    current_source_cut A
      (l,bb,s0,rs0,H0,E0,ren,s1,rs1,H1,E1,bbs1,bbs2) (SUC n) rn En /\
    current_allocation_consistent U Hm sm rs /\ current_env_realizes Hm E rs U /\
    current_env_history_owners Hm E /\ current_annotations_ok U Hm (EL n (A l))
Proof
  simp[current_event_valid_def, current_source_cut_def] >> rpt strip_tac >>
  `current_annotations_ok U H0 (FLAT ap ++ FLAT aq)` by gvs[] >>
  `current_annotations_ok U H0 (FLAT ap)` by
    (drule_all current_annotations_split >> simp[]) >>
  `current_allocation_consistent U Hm sm rs /\ current_env_realizes Hm E rs U` by
    (irule current_local_trace_preserves >> metis_tac[]) >>
  `current_env_history_owners Hm E` by
    metis_tac[current_local_trace_history_owners] >>
  `current_annotations_ok U Hm (FLAT aq)` by
    (irule current_local_trace_remaining_annotations >>
     goal_assum $ drule_at Any >> simp[] >> metis_tac[]) >>
  `xq <> []` by (strip_tac >> gvs[]) >>
  Cases_on `aq` >> Cases_on `xq` >> Cases_on `yq` >>
  fs[current_local_trace_def] >>
  `current_annotations_ok U Hm h` by metis_tac[current_annotations_split, FLAT] >>
  qexistsl_tac [`sm`, `Hm`, `s1'`, `rs1'`, `H1'`, `E1'`] >>
  simp[EL_APPEND_EQN] >>
  qexistsl_tac [`ap ++ [h]`, `t`, `xp ++ [h']`, `t'`,
    `yp ++ [h'']`, `t''`, `s1'`, `H1'`] >>
  simp[APPEND_ASSOC, current_local_trace_append, current_local_trace_def] >>
  metis_tac[]
QED
