Theory lowerDloadSavedGeometry
Ancestors
  lowerDloadReturnSnapshot lowerDloadOwnership list

(* An ML abbreviation only, with the same shared witnesses as the recursive
   interface. This introduces no HOL constant or definition. *)
val saved_geometry = ``\lo E astk gstk savedkeys.
  !q. q < LENGTH astk ==>
    ?f. lo <= f /\ allocas_from f (EL q gstk).lf_state /\
      f <= (EL q gstk).lf_state.vs_alloca_next /\
      (!owner bs bt sz.
        ld_live (DROP (SUC q) astk) (EL q astk).lf_local
          (EL q astk).lf_params (EL q astk).lf_prov (owner,(bs,sz)) /\
        ld_site_entry E owner bs bt sz ==>
        bt+sz <= f \/ ?j. j NOTIN EL q savedkeys /\
          FLOOKUP (EL q gstk).lf_state.vs_allocas j = SOME(bt,sz))``;

Theorem ld_saved_geometry_push:
  (^saved_geometry) lo E astk gstk savedkeys /\
  (?f. lo <= f /\ allocas_from f g.lf_state /\
    f <= g.lf_state.vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk a.lf_local a.lf_params a.lf_prov (owner,(bs,sz)) /\
      ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\
        FLOOKUP g.lf_state.vs_allocas j = SOME(bt,sz))) ==>
  (^saved_geometry) lo E (a::astk) (g::gstk) (keys::savedkeys)
Proof
  BETA_TAC >> strip_tac >> Cases >> simp[] >> metis_tac[]
QED

Theorem ld_saved_geometry_pop:
  (^saved_geometry) lo E (a::astk) (g::gstk) (keys::savedkeys) ==>
  (^saved_geometry) lo E astk gstk savedkeys
Proof
  BETA_TAC >> strip_tac >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC q` mp_tac) >> simp[]
QED

Theorem ld_saved_geometry_head_consume:
  (^saved_geometry) lo E (a::astk) (g::gstk) (keys::savedkeys) /\
  bind_outputs outs vals (merge_callee_state g.lf_state callee) = SOME bound ==>
  ?f. lo <= f /\ allocas_from f (adopt_return_fmp ir bound) /\
    f <= (adopt_return_fmp ir bound).vs_alloca_next /\
    (!owner bs bt sz.
      ld_live astk a.lf_local a.lf_params (DRESTRICT a.lf_prov keep) (owner,(bs,sz)) /\
      ld_site_entry E owner bs bt sz ==>
      bt+sz <= f \/ ?j. j NOTIN keys /\
        FLOOKUP (adopt_return_fmp ir bound).vs_allocas j = SOME(bt,sz))
Proof
  BETA_TAC >> strip_tac >> irule ld_return_snapshot_consume >>
  goal_assum (drule_at Any) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

Theorem ld_saved_geometry_call_push:
  (^saved_geometry) lo E astk gstk savedkeys /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk floor /\
  a.lf_local = L /\ a.lf_params = AP /\ a.lf_prov = AG /\
  g.lf_state = t ==>
  (^saved_geometry) lo E (a::astk) (g::gstk) (keys::savedkeys)
Proof
  strip_tac >> irule ld_saved_geometry_push >> simp[] >>
  drule ld_return_snapshot_extract >> simp[]
QED

(* Every indexed tail slice selects only roots of the resumed live stack.
   In particular the roots of frames below that index must not be omitted. *)
Theorem ld_saved_geometry_root_inclusion:
  q < LENGTH astk /\
  ld_live (DROP (SUC q) astk) (EL q astk).lf_local
    (EL q astk).lf_params (EL q astk).lf_prov site ==>
  ld_live astk L AP AG site
Proof
  rw[ld_live_def] >- metis_tac[EL_MEM] >>
  gvs[MEM_DROP] >> disj2_tac >> goal_assum (drule_at Any) >>
  metis_tac[EL_MEM]
QED

Theorem ld_saved_geometry_return_tail:
  (^saved_geometry) lo E (a::astk) (g::gstk) (keys::savedkeys) /\
  (!owner bs sz. ld_live astk L AP AG (owner,(bs,sz)) ==> owner IN keep) ==>
  (^saved_geometry) lo (DRESTRICT E keep) astk gstk savedkeys
Proof
  strip_tac >> drule ld_saved_geometry_pop >>
  BETA_TAC >> strip_tac >> rpt strip_tac >>
  irule ld_indexed_saved_geometry_restrict >>
  reverse conj_tac >- simp[] >>
  rpt strip_tac >>
  `ld_live astk L AP AG (owner,(bs,sz))` by
    (irule ld_saved_geometry_root_inclusion >> goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED

Theorem ld_saved_geometry_empty:
  (^saved_geometry) lo E [] gstk savedkeys
Proof
  BETA_TAC >> simp[]
QED
