(* Captured-array ownership is created before evaluation of the index. *)
Theory bodyIntCallPostProvenanceCaptured
Ancestors
  bodyIntCallPostProvenanceSnapshotPath bodyIntCallPostProvenanceCapture
  bodyIntCallPostProvenanceCallbacks bodyIntCallProducerInterface
  exprSimSubscriptArrayCompose valueEncodingProps loweringPosts context
  compileEnv finite_map vyperState exprSimAbiEncodeArgsMaterializePath exprSimProps

(* A selection inside the snapshot's reserved window retains its owner.
   No representation or well-formedness is inferred from sub_layout. *)
Theorem intcall_fresh_selection_provenance:
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n lb lsz. local_region ce es.scopes s n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand dst s = SOME w /\ b <= w2n w /\
  w2n w + val_footprint tv v <= b + sz ==>
  intcall_vv_provenance ce cx ty sa sb es raw
    (LocatedValue ann (mk_ptr dst LocMemory)) s
Proof
  strip_tac >> simp[intcall_vv_provenance_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]
QED

Theorem intcall_materialize_owned_provenance:
  materialize_owned_post ctx func ce cx e es sa sm sb s0 ee v dst tv s /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  val_wf tv v /\ sa.cs_next_id <= sm.cs_next_id ==>
  intcall_vv_provenance ce cx (lowered_value_type ce e) sa sb ee (Value v)
    (LocatedValue ann (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
  irule intcall_fresh_selection_provenance >>
  goal_assum (drule_at Any) >>
  simp[read_result_def, return_def, val_footprint_le] >>
  qexists_tac `sm.cs_next_id` >> simp[] >>
  drule val_footprint_le >> decide_tac
QED
