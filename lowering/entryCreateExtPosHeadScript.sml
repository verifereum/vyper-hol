(* Scope the actual positional snapshot, after its guarded VV child. *)
Theory entryCreateExtPosHead
Ancestors
  entryCreateEffectFocus entryCreateNativeFirstExit entryCreateScopedBind
  createSizeConcreteSnapshots createCtorSegmentArrival createSizeRawReplay
  bodyFullExtCallPosList runtimeDefaultRejectCode fragObserverCodeProps
  entryCreateFocusSpec entryCreateCompletedCut createMarkedPath createSizePrefixReplay
  frameGasEvents fragGasOrigin venomExecSemantics venomExecProofs relation

(* A fetched snapshot edge between live states is the actual caller edge.
   GAS is excluded explicitly: an empty gas-readings list is not a counter. *)
Theorem pos_snapshot_segment_edge[local]:
  ~s.vs_halted /\ ~t.vs_halted /\
  ctor_segment_fetch f s = SOME i /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> GAS /\ ctor_segment_next f s i = SOME t ==>
  gas_origin_edge F E C f s [] (OK t)
Proof
  strip_tac >>
  gvs[ctor_segment_fetch_def, ctor_segment_next_def, ctor_segment_entry_def,
      AllCaseEqs()] >>
  simp[gas_origin_edge_def, step_inst_non_invoke, gas_events_step_plain] >>
  metis_tac[eval_phis_preserves_halted]
QED

Theorem pos_snapshot_prefix[local]:
  !s t. RTC (\u v. ~u.vs_halted /\ ~v.vs_halted /\ ~create_operand_at b u /\
       ?i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
           i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
           ctor_segment_next f u i = SOME v) s t ==>
  create_expr_prefix a b E C f s [] t
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[entryCreatePathScopeTheory.create_expr_prefix_nil] >>
  simp[PULL_EXISTS] >> rpt strip_tac >> drule_all pos_snapshot_segment_edge >> strip_tac >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`left` |-> `[]`, `right` |-> `[]`] entryCreatePathScopeTheory.create_expr_prefix_append)) >>
  goal_assum (drule_at Any) >>
  simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
  fs[create_marked_edge_def, create_prefix_step_def, create_operand_at_def,
     ctor_segment_fetch_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem pos_snapshot_scope:
  RTC (\u v. ~u.vs_halted /\ ~v.vs_halted /\ ~create_operand_at b u /\
       ?i. ctor_segment_fetch f u = SOME i /\ i.inst_id IN frag_ids a b /\
           i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
           ctor_segment_next f u i = SOME v) s t /\
  create_operand_at b t ==>
  create_operand_full_scope a b E C f s [] (OK t)
Proof
  strip_tac >> drule_then assume_tac pos_snapshot_prefix >>
  fs[create_operand_full_scope_def, create_operand_at_def]
QED
