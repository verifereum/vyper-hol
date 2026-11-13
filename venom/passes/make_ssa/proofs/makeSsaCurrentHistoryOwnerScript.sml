Theory makeSsaCurrentHistoryOwner
Ancestors
  makeSsaCurrentWfSsa makeSsaCurrentCertificate makeSsaCurrentAllocation
  makeSsaCurrentTreeTrace venomExecProps list rich_list venomInst

Theorem current_history_original_outputs_member[local]:
  !xs j t v. MEM (t,v) (current_original_outputs l i j xs) ==>
    ?k. k < LENGTH xs /\ t = CurrentOriginal l i (j + k) /\ EL k xs = v
Proof
  Induct >> simp[current_original_outputs_def] >> rpt gen_tac >> strip_tac
  >- (qexists `0` >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexists `SUC k` >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_history_original_annotations_member[local]:
  !insts i t v. MEM (t,v) (FLAT (current_original_annotations l i insts)) ==>
    ?k j. k < LENGTH insts /\ j < LENGTH (EL k insts).inst_outputs /\
      t = CurrentOriginal l (i + k) j /\
      EL j (EL k insts).inst_outputs = v
Proof
  Induct >> simp[current_original_annotations_def] >> rpt gen_tac >> strip_tac
  >- (drule current_history_original_outputs_member >> strip_tac >>
      qexistsl [`0`, `k`] >> simp[]) >>
  first_x_assum drule >> strip_tac >> qexistsl [`SUC k`, `j`] >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_history_block_annotation_token_owner:
  lookup_block l fn.fn_blocks = SOME old /\
  MEM (t,v) (FLAT (current_block_annotations old pre)) ==>
  current_wf_token_owner fn t v
Proof
  strip_tac >>
  `old.bb_label = l` by metis_tac[lookup_block_label] >>
  fs[current_block_annotations_def] 
  >- (gvs[current_inserted_annotations_def, MEM_FLAT, MEM_MAP] >>
      gvs[current_wf_token_owner_def]) >>
  drule current_history_original_annotations_member >> strip_tac >>
  gvs[current_wf_token_owner_def] >> metis_tac[]
QED

Theorem current_history_precleanup_annotation_token_owner:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  MEM (t,v) (FLAT (A l)) ==>
  current_wf_token_owner fn t v
Proof
  strip_tac >> drule_all current_wf_precleanup_annotation_lookup >> strip_tac >>
  drule_all current_wf_precleanup_insertion_lookup >> strip_tac >>
  irule current_history_block_annotation_token_owner >> metis_tac[]
QED

Theorem current_history_precleanup_token_owner:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  MEM (t,v,n) H ==> current_wf_token_owner fn t v
Proof
  strip_tac >>
  `?visited. current_wf_history_provenance A visited H` by
    (qpat_x_assum `current_wf_precleanup_certificate _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[current_wf_precleanup_certificate_def] >> strip_tac >>
     drule (cj 1 current_wf_tree_history_provenance) >>
     simp[current_wf_history_provenance_def] >> metis_tac[]) >>
  fs[current_wf_history_provenance_def] >>
  irule current_history_precleanup_annotation_token_owner >> metis_tac[]
QED

Theorem current_history_phi_context_token_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  MEM (t,v,n) H ==> current_wf_token_owner fn t v
Proof
  simp[current_wf_phi_context_def] >>
  metis_tac[current_history_precleanup_token_owner]
QED

Theorem current_history_owned_name_member:
  current_wf_precleanup_certificate s fn renamed s' A H events /\
  (!w. t <> CurrentDefault w) /\ current_wf_token_owner fn t v /\
  current_token_name H t = SOME n ==> MEM (t,v,n) H
Proof
  strip_tac >> drule_all current_token_name_allocated >> strip_tac >>
  drule_all current_history_precleanup_token_owner >> strip_tac >>
  metis_tac[current_wf_token_owner_functional]
QED
