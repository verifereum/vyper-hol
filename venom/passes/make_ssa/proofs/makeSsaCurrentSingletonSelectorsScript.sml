Theory makeSsaCurrentSingletonSelectors
Ancestors makeSsaCurrentInstructionSingleton makeSsaCurrentRuntimeOwners
  makeSsaCurrentAllocation makeSsaCurrentCertificate makeSsaCurrentValueInvariant
  list rich_list alist combin pair arithmetic makeSsaCurrentTokens
  makeSsaCurrentOccurrence makeSsaCurrentAvailability makeSsaCurrentExitTokens
  makeSsaCurrentSingleSiteSegment

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

Theorem current_original_scan_final_slot:
  !insts a i j t.
  i < LENGTH insts /\ j < LENGTH (EL i insts).inst_outputs /\
  EL j (EL i insts).inst_outputs = v /\
  (!k. j < k /\ k < LENGTH (EL i insts).inst_outputs ==>
    EL k (EL i insts).inst_outputs <> v) /\
  (!r. i < r /\ r < LENGTH insts ==> ~MEM v (EL r insts).inst_outputs) ==>
  current_original_scan v l a insts t = CurrentOriginal l (a+i) j
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `i` >> simp[] >> strip_tac
  >- (`EVERY (\inst. ~MEM v inst.inst_outputs) insts` by
        (simp[EVERY_EL] >> rpt strip_tac >>
         qpat_x_assum `!r. _ ==> ~MEM _ _` (qspec_then `SUC n` mp_tac) >> simp[]) >>
      simp[current_original_scan_def, current_original_scan_absent] >>
      irule (SRULE [] (Q.SPECL [`outs`, `0`] current_output_token_last_slot)) >>
      simp[]) >>
  simp[current_original_scan_def] >>
  qpat_x_assum `!a i j t. _` (qspecl_then
    [`SUC a`, `n`, `j`, `current_output_token v l a 0 h.inst_outputs t`] mp_tac) >>
  simp[ADD_CLAUSES] >> disch_then irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC r` mp_tac) >> simp[]
QED

Theorem current_singleton_block_token:
  wf_function fn /\ current_defining_sites fn v = [(b,i)] ==>
  current_block_token fn ins v (EL b fn.fn_blocks).bb_label t =
    current_canonical_instruction_token fn v (b,i)
Proof
  strip_tac >>
  `MEM (b,i) (current_defining_sites fn v)` by simp[] >>
  fs[current_defining_sites_member] >>
  qabbrev_tac `bb = EL b fn.fn_blocks` >>
  `MEM bb fn.fn_blocks` by (simp[Abbr `bb`, MEM_EL] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  `!r. i < r /\ r < LENGTH bb.bb_instructions ==>
    ~MEM v (EL r bb.bb_instructions).inst_outputs` by
    (rpt strip_tac >>
     `MEM (b,r) (current_defining_sites fn v)` by
       (simp[current_defining_sites_member] >> gvs[Abbr `bb`]) >>
     gvs[]) >>
  qpat_assum `MEM v (EL i _).inst_outputs`
    (mp_tac o MATCH_MP current_last_matching_slot) >> strip_tac >>
  `current_output_token v bb.bb_label i 0 (EL i bb.bb_instructions).inst_outputs
    (CurrentDefault v) = CurrentOriginal bb.bb_label i j` by
    (irule (SRULE [] (Q.SPECL [`outs`, `0`] current_output_token_last_slot)) >> simp[]) >>
  gvs[Abbr `bb`] >>
  simp[current_block_token_def, current_canonical_instruction_token_def] >>
  irule (SRULE [] (Q.SPECL [`insts`, `0`] current_original_scan_final_slot)) >> simp[]
QED

Theorem current_chain_unchanged:
  !path t. (!l u. MEM l path ==> current_block_token fn ins v l u = u) ==>
    current_chain_token fn ins v path t = t
Proof
  Induct >> simp[current_chain_token_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem current_chain_single_changing_block:
  !path t. MEM d path /\ (!u. current_block_token fn ins v d u = canonical) /\
  (!l u. MEM l path /\ l <> d ==> current_block_token fn ins v l u = u) ==>
  current_chain_token fn ins v path t = canonical
Proof
  Induct >> simp[current_chain_token_def] >> rpt gen_tac >> disch_tac >>
  Cases_on `MEM d path`
  >- (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  gvs[] >> irule current_chain_unchanged >> metis_tac[]
QED

Theorem current_genlist_elements[local]:
  GENLIST (\i. EL i xs) (LENGTH xs) = xs
Proof
  irule LIST_EQ >> simp[]
QED

Theorem current_insts_blocks_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem current_instruction_sites_records:
  MAP (\bi. EL (SND bi) (EL (FST bi) fn.fn_blocks).bb_instructions)
    (current_instruction_sites fn) = fn_insts fn
Proof
  simp[current_instruction_sites_def, MAP_FLAT, MAP_GENLIST, MAP_MAP_o,
    o_DEF, current_genlist_elements, venomInstTheory.fn_insts_def,
    current_insts_blocks_flat] >>
  AP_TERM_TAC >> irule LIST_EQ >> simp[EL_MAP]
QED

Theorem current_filter_map_length[local]:
  !xs. LENGTH (FILTER P (MAP f xs)) = LENGTH (FILTER (\x. P (f x)) xs)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `P (f h)` >> simp[]
QED

Theorem current_defining_sites_count:
  LENGTH (current_defining_sites fn v) =
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn))
Proof
  rewrite_tac[GSYM current_instruction_sites_records,
    current_filter_map_length, current_defining_sites_def] >> simp[]
QED

Theorem current_single_definition_indexed_site:
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM (b,i) (current_defining_sites fn v) ==>
  current_defining_sites fn v = [(b,i)]
Proof
  rewrite_tac[GSYM current_defining_sites_count] >> strip_tac >>
  Cases_on `current_defining_sites fn v` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem current_nonchanging_block_token:
  ~current_changing_site fn ins v l ==>
  current_block_token fn ins v l t = t
Proof
  strip_tac >> Cases_on `lookup_block l fn.fn_blocks`
  >- simp[current_block_token_def] >>
  irule current_no_local_token >>
  gvs[makeSsaCurrentLastSiteTheory.current_changing_site_def, EVERY_MEM] >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
    venomExecPropsTheory.lookup_block_label]
QED

Theorem current_single_definition_chain_token:
  wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
  all_reachable fn /\ first_block_no_preds fn /\ entry_block fn = SOME eb /\
  blocks_have_leading_phi fn.fn_blocks /\
  current_defining_sites fn v = [(b,i)] /\
  LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1 /\
  MEM (EL b fn.fn_blocks).bb_label path ==>
  current_chain_token fn (current_actual_inserted fn) v path t =
    current_canonical_instruction_token fn v (b,i)
Proof
  strip_tac >>
  `MEM (b,i) (current_defining_sites fn v)` by simp[] >>
  fs[current_defining_sites_member] >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks /\
   MEM (EL i (EL b fn.fn_blocks).bb_instructions)
     (EL b fn.fn_blocks).bb_instructions` by metis_tac[MEM_EL] >>
  irule current_chain_single_changing_block >>
  qexists_tac `(EL b fn.fn_blocks).bb_label` >> simp[] >> conj_tac
  >- metis_tac[current_singleton_block_token] >>
  rpt strip_tac >> irule current_nonchanging_block_token >>
  metis_tac[current_single_definition_changing_site_local]
QED

Theorem current_phi_operand_canonical_exit_token:
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\
  entry_block fn = SOME eb /\ first_block_no_preds fn /\
  blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  current_tree_ancestor_path (current_dom_tree fn) p path /\
  lookup_block p fn.fn_blocks = SOME pred /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ MEM (p,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn p succ.bb_label ==>
  ?bi. current_defining_sites fn v = [bi] /\
    current_block_token fn (current_actual_inserted fn) v p
      (current_inherited_token fn (current_actual_inserted fn) v path) =
    current_canonical_instruction_token fn v bi
Proof
  strip_tac >>
  drule_all current_phi_operand_dominating_definition >> strip_tac >>
  `LENGTH (FILTER (\inst. MEM v inst.inst_outputs) (fn_insts fn)) <= 1` by
    (gvs[venomWfTheory.fn_phi_operands_single_def_def] >> metis_tac[]) >>
  `?b. b < LENGTH fn.fn_blocks /\ EL b fn.fn_blocks = db` by metis_tac[MEM_EL] >>
  `?i. i < LENGTH db.bb_instructions /\ EL i db.bb_instructions = di` by
    metis_tac[MEM_EL] >>
  `current_defining_sites fn v = [(b,i)]` by
    (irule current_single_definition_indexed_site >>
     simp[current_defining_sites_member] >> metis_tac[]) >>
  `MEM p (fn_labels fn)` by
    (simp[venomInstTheory.fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
       venomExecPropsTheory.lookup_block_label]) >>
  `MEM db.bb_label (fn_labels fn)` by
    (simp[venomInstTheory.fn_labels_def, MEM_MAP] >> metis_tac[]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label p` by
    metis_tac[makeSsaCurrentDominanceBridgeTheory.current_semantic_dominates] >>
  `current_token_chain (dom_analyze (cfg_analyze fn) fn) eb.bb_label (REVERSE path) p` by
    metis_tac[makeSsaCurrentPathBridgeTheory.current_actual_path_chain] >>
  `MEM db.bb_label (path ++ [p])` by
    (Cases_on `db.bb_label = p` >> simp[] >>
     `strict_dominates (dom_analyze (cfg_analyze fn) fn) db.bb_label p` by
       simp[dominatorDefsTheory.strict_dominates_def] >>
     drule_all makeSsaCurrentGraphCutTheory.current_actual_chain_membership >> simp[]) >>
  qexists_tac `(b,i)` >> simp[] >>
  rewrite_tac[GSYM current_inherited_token_step, current_inherited_token_def] >>
  irule current_single_definition_chain_token >> metis_tac[]
QED

Theorem current_certificate_original_owner_covered:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  current_history_valid V H /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==> MEM v V
Proof
  strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `?j. j < LENGTH inst.inst_outputs /\ EL j inst.inst_outputs = v` by
    metis_tac[MEM_EL] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  gvs[] >> drule_all current_certificate_original_output_history >> strip_tac >>
  fs[current_history_valid_def, EVERY_MEM] >>
  first_x_assum drule >> simp[]
QED

Theorem current_certificate_phi_operand_selector:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\
  entry_block fn = SOME eb /\ first_block_no_preds fn /\
  blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ current_event_label ev = p /\
  lookup_block p fn.fn_blocks = SOME pred /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ MEM (p,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn p succ.bb_label ==>
  MEM (v,latest_current_name (current_event_exit_rs ev) v)
    (current_instruction_singleton_table fn H)
Proof
  strip_tac >>
  drule_all makeSsaCurrentReinsertionSlotsTheory.current_certificate_static_env >> strip_tac >>
  gvs[] >> drule_all current_phi_operand_canonical_exit_token >> strip_tac >>
  drule_all makeSsaCurrentReinsertionNamesTheory.current_certificate_events_valid >> strip_tac >>
  drule_all current_phi_operand_dominating_definition >> strip_tac >>
  `MEM v V` by (irule current_certificate_original_owner_covered >> metis_tac[]) >>
  `current_token_name H (current_event_exit_env ev v) =
    SOME (latest_current_name (current_event_exit_rs ev) v)` by
    (irule (cj 2 makeSsaCurrentTraceCertificateTheory.current_event_names_accessors) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all current_certificate_singleton_coverage >> strip_tac >>
  gvs[]
QED

Theorem current_certificate_phi_operand_agree:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\
  entry_block fn = SOME eb /\ first_block_no_preds fn /\
  blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM ev events /\ current_event_label ev = p /\
  lookup_block p fn.fn_blocks = SOME pred /\
  MEM succ fn.fn_blocks /\ MEM phi succ.bb_instructions /\
  phi.inst_opcode = PHI /\ MEM (p,v) (phi_pairs phi.inst_operands) /\
  fn_cfg_edge fn p succ.bb_label /\
  current_singleton_agree (current_instruction_singleton_table fn H) st st' ==>
  lookup_var v st = lookup_var (latest_current_name (current_event_exit_rs ev) v) st'
Proof
  strip_tac >> drule_all current_certificate_phi_operand_selector >>
  fs[current_singleton_agree_def]
QED
