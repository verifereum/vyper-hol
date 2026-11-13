Theory makeSsaCurrentLastOutput
Ancestors
  makeSsaCurrentTokens makeSsaCurrentRuntime makeSsaCurrentCutTransport
  makeSsaCurrentWfSsa makeSsaCurrentCertificate venomExecProps
  makeSsaCurrentFinalBlock list rich_list arithmetic

Theorem current_output_token_last_slot:
  !outs j k t. k < LENGTH outs /\
    ~MEM (EL k outs) (DROP (SUC k) outs) ==>
    current_output_token (EL k outs) l i j outs t = CurrentOriginal l i (j + k)
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `k`
  >- (simp[current_output_token_def] >> rpt strip_tac >>
      simp[current_output_token_absent]) >>
  simp[current_output_token_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_output_token_last_position:
  MEM v outs ==>
  ?k. k < LENGTH outs /\ EL k outs = v /\ ~MEM v (DROP (SUC k) outs) /\
    current_output_token v l i 0 outs t = CurrentOriginal l i k
Proof
  strip_tac >> drule current_runtime_last_position >> strip_tac >>
  qexists_tac `k` >> simp[] >>
  mp_tac current_output_token_last_slot >>
  disch_then (qspecl_then [`outs`, `0`, `k`, `t`] mp_tac) >> simp[]
QED

Theorem current_precleanup_original_output_slot:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions /\
  k < LENGTH (EL i old.bb_instructions).inst_outputs ==>
  current_token_name H (CurrentOriginal l i k) =
    SOME (EL k (EL (i + LENGTH pre) new.bb_instructions).inst_outputs)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `MEM new renamed /\ new.bb_label = l /\ old.bb_label = l` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev /\
   current_event_valid A (FLAT (MAP block_ir_vars ins)) ev` by
    metis_tac[listTheory.EVERY_MEM] >>
  drule_all current_wf_event_output_relation >> strip_tac >>
  `LENGTH pre + i < LENGTH (current_block_annotations old pre) /\
   k < LENGTH (EL (LENGTH pre + i) (current_block_annotations old pre)) /\
   EL k (EL (LENGTH pre + i) (current_block_annotations old pre)) =
     (CurrentOriginal l i k, EL k (EL i old.bb_instructions).inst_outputs)` by
    metis_tac[current_wf_original_annotation_index] >>
  gvs[current_edge_shape_def, LIST_REL_EL_EQN, EL_MAP] >>
  first_x_assum (qspec_then `LENGTH pre + i` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem current_original_scan_snoc_output:
  !insts j t.
  current_original_scan v l j (insts ++ [inst]) t =
  current_output_token v l (j + LENGTH insts) 0 inst.inst_outputs
    (current_original_scan v l j insts t)
Proof
  Induct >> simp[current_original_scan_def, ADD_CLAUSES]
QED

Theorem current_source_cut_last_output:
  current_source_cut A ev (LENGTH pre + SUC i) rs E /\
  current_event_label ev = old.bb_label /\
  A old.bb_label = current_block_annotations old pre /\
  i < LENGTH old.bb_instructions /\
  MEM v (EL i old.bb_instructions).inst_outputs ==>
  ?k. k < LENGTH (EL i old.bb_instructions).inst_outputs /\
    EL k (EL i old.bb_instructions).inst_outputs = v /\
    ~MEM v (DROP (SUC k) (EL i old.bb_instructions).inst_outputs) /\
    E v = CurrentOriginal old.bb_label i k
Proof
  strip_tac >>
  `SUC i <= LENGTH old.bb_instructions` by decide_tac >>
  drule_all current_wf_source_cut_original_scan >>
  disch_then (qspec_then `v` mp_tac) >>
  `TAKE (SUC i) old.bb_instructions =
    TAKE i old.bb_instructions ++ [EL i old.bb_instructions]` by
    simp[GSYM SNOC_APPEND, SNOC_EL_TAKE] >>
  simp[current_original_scan_snoc_output, LENGTH_TAKE] >> strip_tac >>
  drule current_output_token_last_position >>
  disch_then (qspecl_then [
    `current_original_scan v old.bb_label 0 (TAKE i old.bb_instructions)
      (if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
       then CurrentInserted v old.bb_label else current_event_entry_env ev v)`,
    `old.bb_label`, `i`] strip_assume_tac) >>
  qexists_tac `k` >> simp[] >> metis_tac[]
QED
