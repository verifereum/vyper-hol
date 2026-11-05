Theory makeSsaCurrentSingletonSelectors
Ancestors makeSsaCurrentInstructionSingleton makeSsaCurrentRuntimeOwners
  makeSsaCurrentAllocation makeSsaCurrentCertificate makeSsaCurrentValueInvariant
  list rich_list alist combin pair

Theorem current_instruction_sites_member:
  MEM (b,i) (current_instruction_sites fn) <=>
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions
Proof
  simp[current_instruction_sites_def, MEM_FLAT, MEM_GENLIST, MEM_MAP,
    PULL_EXISTS] >> metis_tac[]
QED

Theorem current_defining_sites_member:
  MEM (b,i) (current_defining_sites fn v) <=>
  b < LENGTH fn.fn_blocks /\
  i < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  MEM v (EL i (EL b fn.fn_blocks).bb_instructions).inst_outputs
Proof
  simp[current_defining_sites_def, MEM_FILTER, current_instruction_sites_member] >>
  metis_tac[]
QED

Theorem current_last_matching_slot:
  !xs. MEM v xs ==> ?j. j < LENGTH xs /\ EL j xs = v /\
    (!k. j < k /\ k < LENGTH xs ==> EL k xs <> v)
Proof
  Induct >> simp[] >> gen_tac >> disch_tac >> Cases_on `MEM v xs`
  >- (first_x_assum drule >> strip_tac >> qexists_tac `SUC j` >>
      simp[] >> Cases >> simp[] >> metis_tac[]) >>
  `v = h` by metis_tac[] >> gvs[] >> qexists_tac `0` >>
  simp[] >> Cases >> simp[] >> metis_tac[MEM_EL]
QED

Theorem current_original_annotation_vars:
  !insts a. MAP SND (FLAT (current_original_annotations l a insts)) =
    FLAT (MAP (\inst. inst.inst_outputs) insts)
Proof
  Induct >> simp[current_original_annotations_def, GSYM MAP_FLAT]
QED

Theorem current_original_table_vars:
  MAP SND (current_original_table fn) =
    FLAT (MAP (\bb. FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) fn.fn_blocks)
Proof
  simp[current_original_table_def, MAP_FLAT, MAP_MAP_o, o_DEF,
    current_original_annotation_vars]
QED

Theorem current_original_history_name_exists:
  MEM (CurrentOriginal l i j,v,n) H ==>
  ?name. current_token_name H (CurrentOriginal l i j) = SOME name
Proof
  strip_tac >> simp[current_token_name_def] >>
  Cases_on `ALOOKUP H (CurrentOriginal l i j)` >> simp[] >>
  gvs[ALOOKUP_NONE, MEM_MAP] >> metis_tac[FST]
QED

Theorem current_certificate_singleton_coverage:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_defining_sites fn v = [bi] ==>
  ?n. current_token_name H (current_canonical_instruction_token fn v bi) = SOME n /\
    MEM (v,n) (current_instruction_singleton_table fn H)
Proof
  PairCases_on `bi` >> strip_tac >>
  `MEM (bi0,bi1) (current_defining_sites fn v)` by simp[] >>
  fs[current_defining_sites_member] >>
  qmatch_asmsub_abbrev_tac `MEM v inst.inst_outputs` >>
  drule current_last_matching_slot >> strip_tac >>
  qabbrev_tac `bb = EL bi0 fn.fn_blocks` >>
  `MEM bb fn.fn_blocks` by (simp[Abbr `bb`, MEM_EL] >> metis_tac[]) >>
  `MEM v (MAP SND (current_original_table fn))` by
    (rewrite_tac[current_original_table_vars] >>
     simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     qexists_tac `bb` >> simp[] >> qexists_tac `inst` >> simp[] >>
     simp[Abbr `inst`, MEM_EL] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  `current_canonical_instruction_token fn v (bi0,bi1) =
    CurrentOriginal bb.bb_label bi1 j` by
    (simp[current_canonical_instruction_token_def, Abbr `bb`] >>
     irule (SRULE [] (Q.SPECL [`outs`, `0`] current_output_token_last_slot)) >>
     gvs[]) >>
  gvs[Abbr `inst`] >>
  drule_all current_certificate_original_output_history >> strip_tac >>
  drule current_original_history_name_exists >> strip_tac >>
  qexists_tac `name` >> simp[current_instruction_singleton_member]
QED
