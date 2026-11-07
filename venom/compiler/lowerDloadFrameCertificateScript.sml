Theory lowerDloadFrameCertificate
Ancestors
  lowerDloadFrameLayout lowerDloadPhaseBoundary lowerDloadAllocation
  lowerDloadPairedBoundary lowerDloadOwnership venomExecSemantics
  ptrDiscipline finite_map pred_set list

Definition ld_frame_embedding_def:
  ld_frame_embedding E L H s t <=>
    (!id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)) /\
    ld_erase L = s.vs_allocas /\
    (!id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
      FLOOKUP t.vs_allocas id = SOME (bt,sz))
End

Definition ld_saved_embedded_def:
  ld_saved_embedded V E keys d A f g <=>
    f.lf_inst.inst_outputs = g.lf_inst.inst_outputs /\
    LIST_REL (ld_owned_selection E) f.lf_params g.lf_params /\
    (!v. ld_owned_selection E (FLOOKUP f.lf_prov v) (FLOOKUP g.lf_prov v)) /\
    ld_frame_embedding E f.lf_local g.lf_local f.lf_state g.lf_state /\
    ld_owned_vars V E f.lf_prov g.lf_prov
      (entry_taint with t_var := f.lf_tvar)
      (entry_taint with t_var := g.lf_tvar) f.lf_state g.lf_state /\
    ld_alloc_account keys d A f.lf_state g.lf_state
End

Theorem ld_frame_embedding_selection:
  ld_frame_embedding E L H s t ==>
  !id. ld_owned_selection E (FLOOKUP L id) (FLOOKUP H id)
Proof
  simp[ld_frame_embedding_def]
QED

Theorem ld_frame_embedding_source:
  ld_frame_embedding E L H s t ==> ld_erase L = s.vs_allocas
Proof
  simp[ld_frame_embedding_def]
QED

Theorem ld_frame_embedding_target:
  ld_frame_embedding E L H s t ==>
  !id owner bt sz. FLOOKUP H id = SOME (owner,(bt,sz)) ==>
    FLOOKUP t.vs_allocas id = SOME (bt,sz)
Proof
  simp[ld_frame_embedding_def]
QED

Theorem ld_frame_embedding_merge:
  ld_frame_embedding E L H (merge_callee_state s sc) (merge_callee_state t tc)
  <=> ld_frame_embedding E L H s t
Proof
  simp[ld_frame_embedding_def, merge_callee_state_def]
QED

Theorem ld_frame_embedding_domains:
  ld_frame_embedding E L H s t ==> FDOM H = FDOM s.vs_allocas
Proof
  strip_tac >>
  `FDOM L = FDOM H` by
    (simp[EXTENSION] >> gen_tac >>
     drule ld_frame_embedding_selection >> disch_then (qspec_then `x` mp_tac) >>
     simp[ld_owned_selection_def, FLOOKUP_DEF] >> metis_tac[]) >>
  drule ld_frame_embedding_source >>
  metis_tac[ld_erase_def, FDOM_o_f]
QED

Theorem ld_frame_embedding_account_domain:
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t ==>
  FDOM t.vs_allocas = FDOM H UNION A
Proof
  metis_tac[ld_frame_embedding_domains, ld_alloc_account_domain]
QED

Theorem ld_frame_embedding_account_disjoint:
  ld_frame_embedding E L H s t /\ ld_alloc_account keys d A s t ==>
  DISJOINT (FDOM H) A
Proof
  strip_tac >> drule ld_frame_embedding_domains >>
  drule ld_alloc_account_disjoint >> drule ld_alloc_account_capacity >>
  simp[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
QED

Theorem ld_frame_embedding_scratch_probe:
  !s k b E.
  let src = s with <| vs_allocas := FEMPTY; vs_alloca_next := b |> in
  let tgt = s with <| vs_allocas := FEMPTY |+ (k,(b,32));
                     vs_alloca_next := b+32 |> in
    ld_alloc_account {k} 0 {k} src tgt /\ {k} <> {} /\
    ld_frame_embedding E FEMPTY FEMPTY src tgt /\
    FLOOKUP tgt.vs_allocas k = SOME (b,32)
Proof
  rpt gen_tac >> mp_tac ld_embedded_scratch_probe >>
  disch_then (qspecl_then [`s`,`k`,`b`,`E`] mp_tac) >>
  simp[ld_frame_embedding_def, ld_erase_def]
QED

Theorem ld_saved_embedded_params:
  ld_saved_embedded V E keys d A f g ==>
  LIST_REL (ld_owned_selection E) f.lf_params g.lf_params
Proof
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_prov:
  ld_saved_embedded V E keys d A f g ==>
  !v. ld_owned_selection E (FLOOKUP f.lf_prov v) (FLOOKUP g.lf_prov v)
Proof
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_layout:
  ld_saved_embedded V E keys d A f g ==>
  ld_frame_embedding E f.lf_local g.lf_local f.lf_state g.lf_state
Proof
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_vars:
  ld_saved_embedded V E keys d A f g ==>
  ld_owned_vars V E f.lf_prov g.lf_prov
    (entry_taint with t_var := f.lf_tvar)
    (entry_taint with t_var := g.lf_tvar) f.lf_state g.lf_state
Proof
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_account:
  ld_saved_embedded V E keys d A f g ==>
  ld_alloc_account keys d A f.lf_state g.lf_state
Proof
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_return_layout:
  ld_saved_embedded V E keys d A f g ==>
  ld_frame_embedding E f.lf_local g.lf_local
    (merge_callee_state f.lf_state sc) (merge_callee_state g.lf_state tc)
Proof
  simp[ld_frame_embedding_merge] >>
  metis_tac[ld_saved_embedded_layout]
QED

Theorem ld_saved_embedded_return_account:
  ld_saved_embedded V E keys d A f g ==>
  ld_alloc_account keys d A (merge_callee_state f.lf_state sc)
    (merge_callee_state g.lf_state tc)
Proof
  strip_tac >> irule ld_alloc_account_return >>
  metis_tac[ld_saved_embedded_account]
QED

Theorem ld_saved_embedded_return_vars:
  ld_saved_embedded V E keys d A f g ==>
  ld_owned_vars V E f.lf_prov g.lf_prov
    (entry_taint with t_var := f.lf_tvar)
    (entry_taint with t_var := g.lf_tvar)
    (merge_callee_state f.lf_state sc) (merge_callee_state g.lf_state tc)
Proof
  strip_tac >> irule ld_owned_vars_merge >>
  metis_tac[ld_saved_embedded_vars]
QED

Theorem ld_owned_selection_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !ps pt. ld_owned_selection E ps pt <=> ld_owned_selection E' ps pt
Proof
  simp[ld_owned_selection_def]
QED

Theorem ld_owned_value_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !ps pt Ms Mt x y. ld_owned_value E ps pt Ms Mt x y <=>
                    ld_owned_value E' ps pt Ms Mt x y
Proof
  strip_tac >> Cases >> simp[ld_owned_value_def]
QED

Theorem ld_owned_vars_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !V AG AH tn un s t. ld_owned_vars V E AG AH tn un s t <=>
                      ld_owned_vars V E' AG AH tn un s t
Proof
  strip_tac >> drule ld_owned_value_table_cong >>
  simp[ld_owned_vars_def]
QED

Theorem ld_frame_embedding_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !L H s t. ld_frame_embedding E L H s t <=> ld_frame_embedding E' L H s t
Proof
  strip_tac >> drule ld_owned_selection_table_cong >>
  simp[ld_frame_embedding_def]
QED

Theorem ld_saved_embedded_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !V keys d A f g. ld_saved_embedded V E keys d A f g <=>
                   ld_saved_embedded V E' keys d A f g
Proof
  strip_tac >>
  `ld_owned_selection E = ld_owned_selection E'` by
    (simp[FUN_EQ_THM] >> metis_tac[ld_owned_selection_table_cong]) >>
  drule ld_owned_vars_table_cong >>
  drule ld_frame_embedding_table_cong >>
  simp[ld_saved_embedded_def]
QED

Theorem ld_saved_embedded_stack_shapes:
  (LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g)
    [] gs <=> gs = []) /\
  (LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g)
    (f::fs) (g::gs) <=>
    (?V keys d A. ld_saved_embedded V E keys d A f g) /\
    LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) fs gs)
Proof
  simp[]
QED

Theorem ld_saved_embedded_stack_table_cong:
  (!owner bs bt sz. ld_site_entry E owner bs bt sz <=>
                    ld_site_entry E' owner bs bt sz) ==>
  !fs gs.
    LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) fs gs <=>
    LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E' keys d A f g) fs gs
Proof
  strip_tac >> drule ld_saved_embedded_table_cong >> strip_tac >>
  Induct >> Cases >> simp[]
QED
