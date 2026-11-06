Theory lowerDloadReturnSnapshot
Ancestors
  lowerDloadNormalData lowerDloadFrameRepresentation lowerDloadFrameFloor
  lowerDloadLifetime lowerDloadOwnership venomExecSemantics
  ptrDiscipline finite_map pred_set

(* Geometric saved slice only: never a snapshot of bytes or global masks. *)
Theorem ld_return_snapshot_extract:
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk floor ==>
  ?f. lo <= f /\ allocas_from f t /\ f <= t.vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk L AP AG (owner,(bs,sz)) /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP t.vs_allocas j = SOME(bt,sz))
Proof
  strip_tac >> qexists_tac `floor` >>
  drule ld_normal_data_geometry >> strip_tac >> simp[] >> metis_tac[]
QED

Theorem ld_return_snapshot_transport:
  (?f. lo <= f /\ allocas_from f caller /\ f <= caller.vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk L AP AG (owner,(bs,sz)) /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP caller.vs_allocas j = SOME(bt,sz))) /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==>
    FLOOKUP E' owner = FLOOKUP E owner) ==>
  ?f. lo <= f /\ allocas_from f caller /\ f <= caller.vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk L AP AG (owner,(bs,sz)) /\ ld_site_entry E' owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP caller.vs_allocas j = SOME(bt,sz))
Proof
  strip_tac >> qexists_tac `f` >> simp[] >> rpt strip_tac >>
  `ld_site_entry E owner bs bt sz` by
    (fs[ld_site_entry_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_return_snapshot_consume:
  (?f. lo <= f /\ allocas_from f caller /\ f <= caller.vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk L AP AG (owner,(bs,sz)) /\ ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\ FLOOKUP caller.vs_allocas j = SOME(bt,sz))) /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME bound ==>
  ?f. lo <= f /\ allocas_from f (adopt_return_fmp ir bound) /\
    f <= (adopt_return_fmp ir bound).vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk L AP (DRESTRICT AG keep) (owner,(bs,sz)) /\
      ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\
        FLOOKUP (adopt_return_fmp ir bound).vs_allocas j = SOME(bt,sz))
Proof
  strip_tac >> qexists_tac `f` >>
  `allocas_from f (adopt_return_fmp ir bound) /\
   f <= (adopt_return_fmp ir bound).vs_alloca_next` by
    (irule ld_return_floor >> goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> rpt strip_tac >>
  `ld_live astk L AP AG (owner,(bs,sz))` by
    (fs[ld_live_def] >> metis_tac[ld_restrict_selected]) >>
  drule ld_bind_outputs_allocas >> strip_tac >>
  gvs[adopt_return_fmp_allocas, merge_callee_state_def] >> metis_tac[]
QED
