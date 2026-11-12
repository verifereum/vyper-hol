(* Live machine effects are carried only by the active owner.  Suspended
   owners retain residual bookkeeping and FMP, not shared memory equality. *)
Theory functionInlinerLiveInvariant
Ancestors
  functionInlinerParameterLifecycle functionInlinerOperationalCuts
  functionInlinerFrame functionInlinerReachableCuts functionInlinerOccurrences
  functionInlinerCuts functionInlinerStackSupports functionInlinerActivation
  functionInlinerParameterSavedReads functionInlinerParameterAncestry list pred_set

Definition inline_live_stack_def:
  inline_live_stack C cert root entries frame <=>
    inline_owner_storage cert entries frame /\
    inline_parameter_saved_reads entries /\
    inline_parameter_ancestry C cert root (inline_parameter_owners entries) /\
    entries <> [] /\
    (!p a route snap rest. entries = (p,a,route,snap)::rest ==>
      inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state) /\
    EVERY (\(p,a,route,snap).
      snap.ils_state.vs_fmp = frame.ipf_anchor.vs_fmp /\
      inline_caller_residual snap.ils_state =
        inline_caller_residual frame.ipf_state) entries /\
    frame.ipf_state.vs_fmp = frame.ipf_anchor.vs_fmp
End

(* This is a coordinate package, not a PHI predecessor or reachability claim. *)
Definition inline_live_location_def:
  inline_live_location cert root p a path sp tp counter s t <=>
    inline_routed_leaf cert root p a.ia_function path /\
    inline_path_location path
      (SOME <|il_block := s.vs_current_bb; il_phase := sp; il_counter := 0|>) =
      SOME <|il_block := t.vs_current_bb; il_phase := tp; il_counter := counter|>
End

Theorem inline_live_stack_storage:
  inline_live_stack C cert root entries frame ==>
  inline_owner_storage cert entries frame
Proof simp[inline_live_stack_def]
QED

Theorem inline_live_stack_lifecycle:
  inline_live_stack C cert root entries frame ==>
  inline_parameter_saved_reads entries /\
  inline_parameter_ancestry C cert root (inline_parameter_owners entries) /\
  entries <> []
Proof simp[inline_live_stack_def]
QED

Theorem inline_live_stack_head_shared:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame ==>
  inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state
Proof simp[inline_live_stack_def]
QED

Theorem inline_live_stack_member_fmp:
  inline_live_stack C cert root entries frame /\ MEM (p,a,route,snap) entries ==>
  snap.ils_state.vs_fmp = frame.ipf_anchor.vs_fmp
Proof
  simp[inline_live_stack_def, EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem inline_live_stack_member_residual:
  inline_live_stack C cert root entries frame /\ MEM (p,a,route,snap) entries ==>
  inline_caller_residual snap.ils_state = inline_caller_residual frame.ipf_state
Proof
  simp[inline_live_stack_def, EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem inline_live_stack_physical_fmp:
  inline_live_stack C cert root entries frame ==>
  frame.ipf_state.vs_fmp = frame.ipf_anchor.vs_fmp
Proof simp[inline_live_stack_def]
QED

Theorem inline_live_location_route:
  inline_live_location cert root p a path sp tp counter s t ==>
  inline_routed_leaf cert root p a.ia_function path
Proof simp[inline_live_location_def]
QED

Theorem inline_live_location_coordinates:
  inline_live_location cert root p a path sp tp counter s t ==>
  inline_path_location path
    (SOME <|il_block := s.vs_current_bb; il_phase := sp; il_counter := 0|>) =
    SOME <|il_block := t.vs_current_bb; il_phase := tp; il_counter := counter|>
Proof simp[inline_live_location_def]
QED

Theorem inline_live_transformed_root:
  inline_annotated_origin C n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_function.fn_blocks <> [] /\ a.ia_entry.vs_labels = FEMPTY /\
  ~a.ia_entry.vs_halted /\
  a.ia_entry.vs_current_bb = (HD a.ia_function.fn_blocks).bb_label /\
  a.ia_entry.vs_inst_idx = 0 ==>
  ?path snap frame.
    inline_live_stack C cert root
      [(inline_entry_address cert,a,inline_route_identity a.ia_id,snap)] frame /\
    snap.ils_state = a.ia_entry /\ frame.ipf_state = a.ia_entry /\
    frame.ipf_anchor = a.ia_entry /\
    inline_live_location cert root (inline_entry_address cert) a path
      InlineBeforePhi InlineBeforePhi 0 snap.ils_state frame.ipf_state /\
    root.fn_blocks <> [] /\
    lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks =
      SOME (HD a.ia_function.fn_blocks) /\
    lookup_block frame.ipf_state.vs_current_bb root.fn_blocks =
      SOME (HD root.fn_blocks) /\
    snap.ils_state.vs_inst_idx = 0 /\ frame.ipf_state.vs_inst_idx = 0
Proof
  strip_tac >>
  drule_all inline_owner_transformed_root_control >> strip_tac >>
  `inline_namespace_leaf_at cert (inline_entry_address cert) I a.ia_function` by
    metis_tac[inline_entry_leaf] >>
  drule (inline_tracked_snapshot_identity |> Q.INST [`fn` |-> `a.ia_function`]) >>
  strip_tac >>
  qexistsl [`path`,
    `<|ils_state := a.ia_entry; ils_saved := a.ia_entry;
       ils_entry := a.ia_entry;
       ils_defined := {x | MEM x (cfgTransform$fn_all_vars a.ia_function) /\
                          IS_SOME (lookup_var x a.ia_entry)};
       ils_opaque := retpc_var a.ia_function; ils_protected := {};
       ils_parent_rename := I|>`,
    `<|ipf_state := a.ia_entry; ipf_anchor := a.ia_entry|>`] >>
  gvs[inline_live_stack_def, inline_live_location_def,
      inline_parameter_saved_reads_root, inline_before_phi_location_def] >>
  conj_tac
  >- (simp[inline_owner_storage_def, inline_erase_addresses_def,
           inline_suspended_observations_def, inline_address_stack_def,
           inline_address_entry_def, inline_address_links_def,
           inline_route_identity_def] >>
      gvs[inline_route_identity_def, SUBSET_DEF]) >>
  metis_tac[inline_parameter_ancestry_rules]
QED
