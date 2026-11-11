Theory makeSsaCurrentCutTransport
Ancestors
  makeSsaCurrentCarrierOwner makeSsaCurrentWfSsa makeSsaCurrentAllocation
  makeSsaCurrentCertificate makeSsaCurrentFinalBlock makeSsaCurrentTreeTrace
  makeSsaCurrentDemand makeSsaHelper makeSsaCurrentHistoryOwner
  makeSsaCurrentRenameTrace makeSsaCurrentTreePaths makeSsaCurrentTokens
  makeSsaCurrentSourceCuts list rich_list venomInst makeSsaRfAllocation
Theorem current_transport_precleanup_output_names:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions ==>
  LIST_REL (\v n. ?t. MEM (t,v,n) H)
    (EL i old.bb_instructions).inst_outputs
    (EL (i + LENGTH pre) new.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  `MEM new renamed /\ new.bb_label = l` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, lookup_block_label] >>
  drule_all current_wf_precleanup_block_shape >> strip_tac >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `current_event_trace A H ev /\
   current_event_valid A (FLAT (MAP block_ir_vars ins)) ev` by
    metis_tac[listTheory.EVERY_MEM] >>
  drule_all current_wf_event_output_relation >> strip_tac >>
  `LIST_REL (\inst anns. MAP SND anns = inst.inst_outputs)
    (pre ++ old.bb_instructions) (A l)` by
    (mp_tac (Q.INST [`new` |-> `old with bb_instructions := pre ++ old.bb_instructions`]
       current_block_annotations_owners) >> simp[]) >>
  `!t v. MEM (t,v) (FLAT (A l)) ==> !w. t <> CurrentDefault w` by
    (qpat_x_assum `current_event_valid _ _ ev` mp_tac >>
     PairCases_on `ev` >>
     simp[current_event_valid_def, current_annotations_ok_def,
       listTheory.EVERY_MEM, pairTheory.FORALL_PROD] >>
     fs[current_event_label_def] >> metis_tac[]) >>
  gvs[current_edge_shape_def, LIST_REL_EL_EQN, EL_MAP] >>
  `i + LENGTH pre < LENGTH new.bb_instructions` by decide_tac >>
  `MAP SND (EL (i + LENGTH pre) (current_block_annotations old pre)) =
    (EL i old.bb_instructions).inst_outputs` by
    (first_x_assum (qspec_then `i + LENGTH pre` mp_tac) >>
     simp[EL_APPEND_EQN]) >>
  qpat_x_assum `!n. n < LENGTH new.bb_instructions ==> LENGTH _ = _ /\ _`
    (qspec_then `i + LENGTH pre` mp_tac) >>
  simp[arithmeticTheory.ADD_COMM] >> strip_tac >>
  conj_tac >- metis_tac[LENGTH_MAP] >>
  rpt strip_tac >>
  `n < LENGTH (EL (i + LENGTH pre) (current_block_annotations old pre))` by
    metis_tac[LENGTH_MAP] >>
  Cases_on `EL n (EL (i + LENGTH pre) (current_block_annotations old pre))` >>
  rename1 `EL n (EL (i + LENGTH pre) (current_block_annotations old pre)) = (t,v)` >>
  `MEM (t,v) (FLAT (current_block_annotations old pre))` by
    (simp[MEM_FLAT] >> qexists `EL (i + LENGTH pre) (current_block_annotations old pre)` >>
     metis_tac[EL_MEM]) >>
  `current_wf_token_owner fn t v` by
    metis_tac[current_history_block_annotation_token_owner] >>
  `current_token_name H t = SOME (EL n (EL (i + LENGTH pre) new.bb_instructions).inst_outputs)` by
    (first_x_assum (qspec_then `n` mp_tac) >> simp[arithmeticTheory.ADD_COMM]) >>
  `v = EL n (EL i old.bb_instructions).inst_outputs` by
    (qpat_x_assum `MAP SND _ = _` (mp_tac o Q.AP_TERM `EL n`) >>
     simp[EL_MAP]) >>
  qexists `t` >> irule current_history_owned_name_member >> metis_tac[]
QED

Theorem current_transport_precleanup_output_exclusion:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block l fn.fn_blocks = SOME old /\
  lookup_block l renamed = SOME new /\
  A l = current_block_annotations old pre /\ i < LENGTH old.bb_instructions /\
  MEM (t,v,n) H /\ ~MEM v (EL i old.bb_instructions).inst_outputs ==>
  ~MEM n (EL (i + LENGTH pre) new.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all current_transport_precleanup_output_names >>
  rewrite_tac[LIST_REL_EL_EQN] >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM] >> strip_tac >> strip_tac >>
  `?j. j < LENGTH (EL (i + LENGTH pre) new.bb_instructions).inst_outputs /\
    EL j (EL (i + LENGTH pre) new.bb_instructions).inst_outputs = n` by
    metis_tac[MEM_EL] >>
  `?u. MEM (u,EL j (EL i old.bb_instructions).inst_outputs,n) H` by
    metis_tac[] >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ all_reachable fn /\
   ir_supply_covers_fn s fn /\ ir_supply_inst_ok s` by
    fs[current_wf_phi_context_def] >>
  drule_all current_wf_precleanup_names >> strip_tac >>
  `EL j (EL i old.bb_instructions).inst_outputs = v` by
    metis_tac[current_history_name_unique] >>
  metis_tac[EL_MEM]
QED

Theorem current_transport_original_scan_snoc:
  !insts k E. ~MEM v inst.inst_outputs ==>
    current_original_scan v l k (insts ++ [inst]) E =
    current_original_scan v l k insts E
Proof
  Induct >> simp[current_original_scan_def, current_output_token_absent]
QED

Theorem current_transport_source_cut_unaffected:
  current_source_cut A ev (LENGTH pre + i) rs E /\
  current_source_cut A ev (LENGTH pre + SUC i) rs' E' /\
  current_event_label ev = old.bb_label /\
  A old.bb_label = current_block_annotations old pre /\
  i < LENGTH old.bb_instructions /\
  ~MEM v (EL i old.bb_instructions).inst_outputs ==>
  E v = E' v
Proof
  strip_tac >>
  `i <= LENGTH old.bb_instructions /\ SUC i <= LENGTH old.bb_instructions` by decide_tac >>
  `current_original_scan v old.bb_label 0 (TAKE i old.bb_instructions)
    (if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
     then CurrentInserted v old.bb_label else current_event_entry_env ev v) = E v` by
    metis_tac[current_wf_source_cut_original_scan] >>
  `current_original_scan v old.bb_label 0 (TAKE (SUC i) old.bb_instructions)
    (if (?inst. MEM inst pre /\ MEM v inst.inst_outputs)
     then CurrentInserted v old.bb_label else current_event_entry_env ev v) = E' v` by
    metis_tac[current_wf_source_cut_original_scan] >>
  `TAKE (SUC i) old.bb_instructions =
    TAKE i old.bb_instructions ++ [EL i old.bb_instructions]` by
    simp[GSYM SNOC_APPEND, SNOC_EL_TAKE] >>
  drule current_transport_original_scan_snoc >>
  disch_then (qspecl_then [`old.bb_label`, `TAKE i old.bb_instructions`, `0`] mp_tac) >>
  metis_tac[]
QED

Theorem current_transport_source_cut_bound:
  current_source_cut A ev n rs E ==>
  n <= LENGTH (current_event_input_block ev).bb_instructions
Proof
  PairCases_on `ev` >>
  simp[current_source_cut_def, current_event_input_block_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem current_transport_cleanup_ordinary_outputs:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM new renamed /\
  k < LENGTH new.bb_instructions /\
  (EL k new.bb_instructions).inst_opcode <> PHI ==>
  (EL k (simplify_current_phi_block new).bb_instructions).inst_outputs =
  (EL k new.bb_instructions).inst_outputs
Proof
  strip_tac >> drule_all current_wf_phi_context_cleanup_split >> strip_tac >>
  `LENGTH pre <= k` by
    (Cases_on `k < LENGTH pre` >> simp[] >>
     `MEM (EL k pre) pre` by metis_tac[listTheory.EL_MEM] >>
     fs[listTheory.EL_APPEND_EQN, listTheory.EVERY_MEM]) >>
  `k - LENGTH pre < LENGTH tail` by fs[] >>
  `current_inst_no_id (EL (k - LENGTH pre) tail) =
   current_inst_no_id (EL (k - LENGTH pre) tail')` by
    (fs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  fs[listTheory.EL_APPEND_EQN, makeSsaCurrentCleanupShapeTheory.current_inst_no_id_def] >>
  qpat_x_assum `_ with inst_id := 0 = _` (mp_tac o Q.AP_TERM `\inst. inst.inst_outputs`) >>
  simp[]
QED
