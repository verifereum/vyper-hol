Theory lowerDloadCoverageInvariant
Ancestors
  lowerDloadSharedState lowerDloadFrameCertificate lowerDloadCertificateProbe
  lowerDloadOwnership lowerDloadPairedBoundary lowerDloadAllocation
  venomExecSemantics ptrDiscipline finite_map

(* Data at original-instruction boundaries, NOT the complete coverage
   invariant. Memory, live geometry, control and macro anchors are separate. *)
Definition ld_frame_data_def:
  ld_frame_data V U E L H AP BP AG BH tn un s t <=>
    ld_frame_embedding E L H s t /\
    LIST_REL (ld_owned_selection E) AP BP /\
    (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
    ld_owned_vars U E AG BH tn un s t /\
    (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
    ld_shared_state tn un s t
End

Theorem ld_frame_data_embedding:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_frame_embedding E L H s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_params:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  LIST_REL (ld_owned_selection E) AP BP
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_provenance:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_vars:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_owned_vars U E AG BH tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_definedness:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  !v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_shared:
  ld_frame_data V U E L H AP BP AG BH tn un s t ==>
  ld_shared_state tn un s t
Proof
  simp[ld_frame_data_def]
QED

Theorem ld_frame_data_initial:
  s.vs_allocas = FEMPTY ==>
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s s
Proof
  simp[ld_frame_data_def, ld_frame_embedding_def, ld_erase_def,
       ld_owned_selection_def, ld_owned_empty_initial, ld_shared_state_identity]
QED

(* This is genuinely anchored at source entry. The reflexive second conjunct
   does not identify s1 with the transformed program's entered state. *)
Theorem ld_frame_data_source_entry:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := 0 |>) s1 /\
  s1.vs_allocas = FEMPTY /\ active_inst fn inst s1 ==>
  ld_annotated_reachable vs0 ctx [] 0 FEMPTY [] FEMPTY
    entry_taint fn inst s1 /\
  ld_frame_data V U FEMPTY FEMPTY FEMPTY [] [] FEMPTY FEMPTY
    entry_taint entry_taint s1 s1
Proof
  strip_tac >> conj_tac
  >- (irule ld_annotated_reachable_entry >> simp[] >>
      goal_assum (drule_at Any)) >>
  irule ld_frame_data_initial >> simp[]
QED
