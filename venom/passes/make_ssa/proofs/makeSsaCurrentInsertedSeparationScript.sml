Theory makeSsaCurrentInsertedSeparation
Ancestors makeSsaCurrentInstructionSingleton makeSsaCurrentSingletonSelectors
  makeSsaCurrentMergeSlots makeSsaCurrentReinsertionSlots makeSsaCurrentReinsertionNames
  makeSsaCurrentTokens makeSsaCurrentAllocation makeSsaCurrentCertificate list pair

Theorem current_canonical_instruction_original:
  current_defining_sites fn v = [bi] ==>
  ?l i k. current_canonical_instruction_token fn v bi = CurrentOriginal l i k
Proof
  PairCases_on `bi` >> strip_tac >>
  `MEM (bi0,bi1) (current_defining_sites fn v)` by simp[] >>
  fs[current_defining_sites_member] >>
  drule current_last_matching_slot >> strip_tac >>
  qexistsl_tac [`(EL bi0 fn.fn_blocks).bb_label`, `bi1`, `j`] >>
  simp[current_canonical_instruction_token_def] >>
  irule (SRULE [] (Q.SPECL [`outs`, `0`] current_output_token_last_slot)) >>
  simp[]
QED

Theorem current_inserted_instruction_singleton_separate:
  current_history_valid V H /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  MEM (x,n) (current_instruction_singleton_table fn H) ==> out <> n
Proof
  simp[current_instruction_singleton_member] >> rpt strip_tac >>
  drule current_canonical_instruction_original >> strip_tac >>
  gvs[] >> drule_all current_inserted_name_collision >> simp[]
QED

Theorem current_certificate_inserted_singleton_separate:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  current_token_name H (CurrentInserted v h) = SOME out /\
  MEM (x,n) (current_instruction_singleton_table fn H) ==> out <> n
Proof
  strip_tac >> drule_all current_certificate_events_valid >> strip_tac >>
  metis_tac[current_inserted_instruction_singleton_separate]
QED

Theorem current_event_inserted_singleton_exclude:
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations old pre /\
  k < LENGTH pre /\ (EL k pre).inst_outputs = [v] /\
  current_history_valid V finalH /\
  MEM (x,n) (current_instruction_singleton_table fn finalH) ==>
  ~MEM n (EL k ren).inst_outputs
Proof
  strip_tac >> drule_all current_event_inserted_output_name >> strip_tac >>
  `n' <> n` by metis_tac[current_inserted_instruction_singleton_separate] >>
  simp[] >> metis_tac[]
QED
