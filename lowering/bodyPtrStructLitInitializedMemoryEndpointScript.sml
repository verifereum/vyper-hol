Theory bodyPtrStructLitInitializedMemoryEndpoint
Ancestors bodyPtrStructLitFirstMemoryConsumer bodyPtrStructLitFirstStoreEndpoint
  bodyPtrStructLitMemoryRead bodyPtrStructLitProducerAddress
  typedCopyPtr venomState venomMemProofs finite_map bodyPtrDefs ptrDiscipline

(* A concrete continuation frame, relative to the raw-child endpoint. *)
Theorem structlit_add_load_store_state_frame:
  u = (update_var dst a s with vs_inst_idx := SUC s.vs_inst_idx) /\
  s1 = (update_var load w u with vs_inst_idx := SUC u.vs_inst_idx) /\
  sf = (mstore off w s1 with vs_inst_idx := SUC s1.vs_inst_idx) ==>
  sf.vs_memory = (mstore off w s).vs_memory /\
  mload off sf = w /\ sf.vs_allocas = s.vs_allocas /\
  (!x. x <> dst /\ x <> load ==> lookup_var x sf = lookup_var x s)
Proof
  strip_tac >> gvs[] >>
  `mload off (mstore off w s) = w` by
    simp[venomMemProofsTheory.mload_mstore_same_proof] >>
  fs[mstore_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE, mload_def]
QED

Theorem structlit_clean_word_store_resources:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} /\ ptr_covers G tn root s N /\
  sf = (mstore (w2n a) w s with vs_inst_idx := k) /\
  tnf = step_taint (mk_inst id MSTORE [Var dst;value] []) s
    (mstore (w2n a) w s) tn ==>
  ptr_covers G tnf root sf N /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  gvs[ptr_covers_def, op_taint_def, mstore_def, lookup_var_def] >>
  fs[]
QED
