Theory lowerDloadFrameRepresentation
Ancestors
  lowerDloadFrameFloor lowerDloadLifetime lowerDloadOwnership lowerDloadTargetGeometry
  venomExecSemantics venomState finite_map pred_set

Theorem ld_representation_empty:
  !owner bs bt sz. owner IN {} /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ (?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz))
Proof
  simp[]
QED

(* The independent floor facts are ld_setup_callee_floor. *)
Theorem ld_representation_enter:
  setup_callee fn args caller = SOME child /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= caller.vs_alloca_next) ==>
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= caller.vs_alloca_next \/
    (?j. j NOTIN keys /\ FLOOKUP child.vs_allocas j = SOME(bt,sz)))
Proof
  metis_tac[]
QED

(* Floor restoration itself is ld_return_floor. No memory restoration. *)
Theorem ld_representation_return:
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    bt+sz <= f \/ (?j. j NOTIN keys /\ FLOOKUP caller.vs_allocas j = SOME(bt,sz))) /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME bound /\
  (!owner bs bt sz. owner IN live' /\ ld_site_entry E' owner bs bt sz ==>
    owner IN live /\ ld_site_entry E owner bs bt sz) ==>
  (!owner bs bt sz. owner IN live' /\ ld_site_entry E' owner bs bt sz ==>
    bt+sz <= f \/
    (?j. j NOTIN keys /\ FLOOKUP (adopt_return_fmp ir bound).vs_allocas j = SOME(bt,sz)))
Proof
  strip_tac >> drule ld_bind_outputs_allocas >> strip_tac >>
  gvs[adopt_return_fmp_allocas, merge_callee_state_def] >> metis_tac[]
QED

Theorem ld_live_call_shape:
  f.lf_local = L /\ f.lf_params = AP /\ f.lf_prov = AG ==>
  (ld_live (f::astk) FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY site <=>
   ld_live astk L AP AG site)
Proof
  strip_tac >> simp[ld_live_def] >>
  metis_tac[ld_call_selected]
QED

Theorem ld_live_call_endpoints:
  ld_frame_embedding E L H s t /\
  LIST_REL (ld_owned_selection E) AP BP /\
  (!v. ld_owned_selection E (FLOOKUP AG v) (FLOOKUP BH v)) /\
  LIST_REL (\f g. ?V keys d A. ld_saved_embedded V E keys d A f g) astk gstk /\
  ld_frame_bound t.vs_alloca_next H BP BH /\
  ld_stack_bound t.vs_alloca_next gstk /\
  f.lf_local = L /\ f.lf_params = AP /\ f.lf_prov = AG ==>
  !owner bs bt sz.
    ld_live (f::astk) FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY (owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz ==> bt+sz <= t.vs_alloca_next
Proof
  strip_tac >> drule_all ld_live_call_shape >>
  disch_then assume_tac >>
  simp[] >> ho_match_mp_tac ld_paired_live_endpoints >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem ld_live_restrict_shape:
  ld_live astk f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) site ==>
  ld_live astk f.lf_local f.lf_params f.lf_prov site
Proof
  simp[ld_live_def] >> metis_tac[ld_restrict_selected]
QED

Theorem ld_live_return_entries:
  (!owner bs sz. ld_live astk f.lf_local f.lf_params f.lf_prov (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  !owner bs bt sz.
    ld_live astk f.lf_local f.lf_params (DRESTRICT f.lf_prov keys) (owner,(bs,sz)) /\
    ld_site_entry E' owner bs bt sz ==>
    ld_live astk f.lf_local f.lf_params f.lf_prov (owner,(bs,sz)) /\
    ld_site_entry E owner bs bt sz
Proof
  rpt strip_tac >> drule ld_live_restrict_shape >> strip_tac >>
  gvs[ld_site_entry_def] >> metis_tac[]
QED
