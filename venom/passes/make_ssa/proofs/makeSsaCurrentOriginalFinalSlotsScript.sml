Theory makeSsaCurrentOriginalFinalSlots
Ancestors makeSsaCurrentInstructionSingleton
  makeSsaCurrentSingletonSelectors makeSsaCurrentFinalWriteSlots
  makeSsaCurrentOutputNames makeSsaCurrentAllocation makeSsaCurrentTreeTrace
  makeSsaCurrentCertificate venomWf venomInst
  list rich_list pair

Theorem current_indexed_block_label_injective:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\ c < LENGTH fn.fn_blocks /\
  (EL b fn.fn_blocks).bb_label = (EL c fn.fn_blocks).bb_label ==> b = c
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `EL b (MAP (\bb. bb.bb_label) fn.fn_blocks) =
   EL c (MAP (\bb. bb.bb_label) fn.fn_blocks)` by simp[EL_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]
QED

Theorem current_singleton_member_final_site:
  MEM (v,n) (current_instruction_singleton_table fn H) ==>
  ?b i j. b < LENGTH fn.fn_blocks /\
    i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
    current_defining_sites fn v = [(b,i)] /\
    j < LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs /\
    EL j (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs = v /\
    (!k. j < k /\ k < LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs ==>
      EL k (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs <> v) /\
    current_token_name H (CurrentOriginal (EL b fn.fn_blocks).bb_label i j) = SOME n
Proof
  simp[current_instruction_singleton_member] >> strip_tac >> PairCases_on `bi` >>
  `MEM (bi0,bi1) (current_defining_sites fn v)` by simp[] >>
  fs[current_defining_sites_member] >>
  drule current_last_matching_slot >> strip_tac >>
  qexists_tac `j` >> simp[] >>
  `current_canonical_instruction_token fn v (bi0,bi1) =
   CurrentOriginal (EL bi0 fn.fn_blocks).bb_label bi1 j` by
    (simp[current_canonical_instruction_token_def] >>
     drule_all current_output_token_last_slot >> simp[]) >>
  metis_tac[]
QED

Theorem current_original_output_final_slots:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  current_history_valid U H /\
  LENGTH outs' = LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs /\
  (!j. j < LENGTH outs' ==>
    current_token_name H (CurrentOriginal (EL b fn.fn_blocks).bb_label i j) =
      SOME (EL j outs')) ==>
  current_table_final_slots (current_instruction_singleton_table fn H)
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs outs'
Proof
  rpt strip_tac >> simp[current_table_final_slots_def] >>
  qx_gen_tac `v` >> qx_gen_tac `n` >> strip_tac >>
  drule current_singleton_member_final_site >> strip_tac >>
  rename1 `current_defining_sites fn v = [(c,r)]` >>
  `!k. k < LENGTH outs' /\ EL k outs' = n ==>
    b = c /\ i = r /\ k = j` by
    (rpt strip_tac >>
     `CurrentOriginal (EL b fn.fn_blocks).bb_label i k =
      CurrentOriginal (EL c fn.fn_blocks).bb_label r j` by
       (irule current_allocated_name_injective >> simp[] >> metis_tac[]) >>
     gvs[] >> metis_tac[current_indexed_block_label_injective]) >>
  Cases_on `MEM v (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs`
  >- (`MEM (b,i) (current_defining_sites fn v)` by
        simp[current_defining_sites_member] >>
      `b = c /\ i = r` by metis_tac[MEM, PAIR_EQ] >> gvs[] >>
      qexists_tac `j` >> simp[] >>
      metis_tac[]) >>
  disj1_tac >> simp[] >>
  simp[MEM_EL] >> rpt strip_tac >>
  `b = c /\ i = r /\ n' = j` by metis_tac[] >>
  gvs[] >> metis_tac[MEM_EL]
QED

Theorem current_event_original_output_length:
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations old pre /\
  i < LENGTH old.bb_instructions ==>
  LENGTH (EL (LENGTH pre+i) ren).inst_outputs =
    LENGTH (EL i old.bb_instructions).inst_outputs
Proof
  simp[current_event_trace_def, current_event_valid_def] >> strip_tac >> gvs[] >>
  drule_all current_local_trace_output_names >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  `LENGTH pre+i < LENGTH (current_block_annotations old pre)` by
    (simp[NoAsms, current_block_annotations_def, current_inserted_annotations_def] >>
     simp[]) >>
  first_x_assum (qspec_then `LENGTH pre+i` mp_tac) >>
  simp[current_block_annotations_def, current_inserted_annotations_def,
    EL_APPEND_EQN, current_original_annotations_index]
QED

Theorem current_event_original_final_slots:
  wf_function fn /\ b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  current_history_valid U finalH /\
  current_event_trace A finalH
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  current_event_valid A V
    (l,bb,s,rs,H,E,ren,s1,rs1,H1,E1,bbs1,bbs2) /\
  A l = current_block_annotations (EL b fn.fn_blocks) pre ==>
  current_table_final_slots (current_instruction_singleton_table fn finalH)
    (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs
    (EL (LENGTH pre+i) ren).inst_outputs
Proof
  rpt strip_tac >> irule current_original_output_final_slots >>
  `LENGTH (EL (LENGTH pre+i) ren).inst_outputs =
    LENGTH (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs` by
    metis_tac[current_event_original_output_length] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all current_event_original_output_name >> simp[]) >>
  metis_tac[]
QED
