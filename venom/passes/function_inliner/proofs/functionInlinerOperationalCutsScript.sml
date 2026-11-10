(* Addressed owner-local data storage, separate from operational reachability. *)
Theory functionInlinerOperationalCuts
Ancestors
  functionInlinerReachableCuts functionInlinerStackSupports functionInlinerCuts
  functionInlinerActivation functionInlinerEnvelopes venomState cfgTransform list pred_set

Definition inline_owner_storage_def:
  inline_owner_storage cert entries frame <=>
    inline_address_stack cert entries /\
    inline_addresses_ordered (MAP FST entries) /\
    inline_suspended_observations (inline_erase_addresses entries) frame
End

Theorem inline_owner_storage_static:
  inline_owner_storage cert entries frame ==>
  inline_address_stack cert entries /\ inline_addresses_ordered (MAP FST entries)
Proof simp[inline_owner_storage_def]
QED

Theorem inline_owner_storage_head:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame ==>
  inline_tracked_snapshot a.ia_function a route snap frame /\
  inline_suspended_observations (inline_erase_addresses rest) frame
Proof
  simp[inline_owner_storage_def, inline_erase_addresses_def,
       inline_suspended_observations_def]
QED

Theorem inline_owner_storage_root:
  a.ia_entry.vs_labels = FEMPTY /\
  inline_namespace_leaf_at cert p I a.ia_function ==>
  ?snap frame.
    inline_owner_storage cert [(p,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry
Proof
  strip_tac >>
  drule (inline_tracked_snapshot_identity |> Q.INST [`fn` |-> `a.ia_function`]) >>
  strip_tac >>
  simp[inline_owner_storage_def, inline_erase_addresses_def,
       inline_suspended_observations_def, inline_address_stack_def,
       inline_address_entry_def, inline_address_links_def,
       inline_route_identity_def] >>
  gvs[inline_route_identity_def] >>
  goal_assum (drule_at Any) >> simp[SUBSET_DEF]
QED

Theorem inline_owner_storage_writes:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  INJ route.ir_rename (set (MAP FST writes) UNION snap.ils_defined) UNIV /\
  EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars a.ia_function) /\
                  ~retpc_var a.ia_function x) writes ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state :=
       FOLDL (\s (x,w). update_var x w s) snap.ils_state writes;
       ils_defined := set (MAP FST writes) UNION snap.ils_defined|>)::rest)
    (frame with ipf_state :=
       FOLDL (\s (x,w). update_var (route.ir_rename x) w s) frame.ipf_state writes)
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  `EVERY (\(x,w). MEM x (cfgTransform$fn_all_vars a.ia_function) /\
      ~retpc_var a.ia_function x /\
      (!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> route.ir_rename x)) writes` by
    (gvs[EVERY_MEM, pairTheory.FORALL_PROD] >>
     metis_tac[inline_address_stack_body_protected]) >>
  drule_all inline_tracked_resume_writes >> strip_tac >>
  `EVERY (\(d,w). inline_suspended_avoids (inline_erase_addresses rest) d)
    (MAP (\(x,w). (route.ir_rename x,w)) writes)` by
    (simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD] >> rpt strip_tac >>
     drule inline_address_stack_body_avoids >> disch_then drule >>
     disch_then irule >> gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]) >>
  drule_all inline_suspended_writes >> strip_tac >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def, rich_listTheory.FOLDL_MAP,
      combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
  Cases_on `rest`
  >- (gvs[inline_address_stack_def, inline_address_entry_def, inline_address_links_def,
          SUBSET_DEF, EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
          pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  PairCases_on `h` >>
  gvs[inline_address_stack_def, inline_address_entry_def, inline_address_links_def,
      SUBSET_DEF, EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD,
      pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem inline_owner_storage_opaque_write:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\
  retpc_var a.ia_function x /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV ==>
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := update_var x w snap.ils_state;
       ils_defined := x INSERT snap.ils_defined|>)::rest)
    (frame with ipf_state := update_var (route.ir_rename x) u frame.ipf_state)
Proof
  strip_tac >>
  drule inline_owner_storage_static >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  `!v. v IN snap.ils_protected ==> snap.ils_parent_rename v <> route.ir_rename x` by
    metis_tac[inline_address_stack_body_protected] >>
  drule_all inline_tracked_resume_opaque_write >> strip_tac >>
  `inline_suspended_avoids (inline_erase_addresses rest) (route.ir_rename x)` by
    metis_tac[inline_address_stack_body_avoids] >>
  drule_all inline_suspended_write >> strip_tac >>
  gvs[inline_owner_storage_def, inline_erase_addresses_def,
      inline_suspended_observations_def] >>
  Cases_on `rest`
  >- (gvs[inline_address_stack_def, inline_address_entry_def,
          inline_address_links_def, SUBSET_DEF] >> metis_tac[]) >>
  PairCases_on `h` >>
  gvs[inline_address_stack_def, inline_address_entry_def,
      inline_address_links_def, SUBSET_DEF] >> metis_tac[]
QED
