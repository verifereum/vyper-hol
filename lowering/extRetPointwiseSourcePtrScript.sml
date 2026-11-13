Theory extRetPointwiseSourcePtr
Ancestors bodyPtrDefs abiEncoderSourceProducer abiEncoderSourceAggregate
  abiEncoderOpenInput abiEncoderSourceTransport abiEncoderProps
  vyperABI vyperTyping valueEncoding venomExecSemantics

(* The representation type is uniform; its value representative may depend
   on the memory. No source allocation-capacity bound is asserted here. *)
Theorem ptr_mem_ok_pointwise_open_input:
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  ptr_mem_ok cx ty v op G tn s /\ eval_operand op s = SOME w ==>
  ?ct. source_rep (get_tenv cx) ty ei ct /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
         abi_encoder_open_input ei ct rv (w2n w) (type_memory_size tv) mem
Proof
  strip_tac >> drule (cj 1 abi_encoder_uniform_source) >> strip_tac >>
  qexists `ct` >> simp[] >> rpt strip_tac >>
  irule source_rep_transport >> simp[] >>
  qexists `v` >> simp[] >>
  gvs[ptr_mem_ok_def] >> metis_tac[]
QED

Theorem ptr_val_ok_pointwise_open_input:
  abi_enc_plan (get_tenv cx) ty ei /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) ty v = SOME av /\
  ptr_val_ok cx ty v op G tn s /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  ?ct. source_rep (get_tenv cx) ty ei ct /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    ?rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
         abi_encoder_open_input ei ct rv (w2n w) (type_memory_size tv) mem
Proof
  strip_tac >> irule ptr_mem_ok_pointwise_open_input >>
  gvs[ptr_val_ok_def] >> metis_tac[]
QED

(* Consumer-boundary audit (C1.34.6.72.3.3).
 *
 * Interface                         Premise / conclusion
 * Representation: the theorems above conclude exists ct, forall mem,
 *   exists rv, with source_rep and equal encodings.  They do NOT conclude
 *   exists rv, forall mem.  abiEncoderOpenInput.abi_encoder_open_input
 *   constrains semantic contents and spans relative to cap; cap is not an
 *   allocation witness, an address bound, or a separation assertion.
 * Allocation: bodyPtrDefs.ptr_mem_ok_def retains exactly the implication
 *   val_footprint tv v <> 0 ==>
 *   ?x b sz. op = Var x /\ FLOOKUP G x = SOME (b, sz) /\
 *            b <= w2n w /\ w2n w + val_store_size tv v <= b + sz.
 *   In particular there is no capacity-sized allocation conclusion for
 *   type_memory_size tv, and no coverage conclusion at zero footprint.
 * No-wrap: abiEncoderProps.enc_pre_def requires
 *   src + type_memory_size tv <= lo; enc_scratch bounds its scratch top.
 *   abiEncoderSourceInvoke.enc_pre_source_end_bound consequently gives
 *   src + type_memory_size tv < dimword(:256).  This is a consequence of
 *   enc_pre, NOT of the pointwise open-input conclusion above.
 * Separation: enc_pre also requires each output to be below lo and
 *   regions_disjoint (src,type_memory_size tv) (b,n).  Its scratch invariant
 *   is an additional premise.  Neither is supplied by ptr_mem_ok alone.
 * Shared entry: abi_encoder_source_shared_input takes enc_pre plus plan,
 *   evaluation, typing, ABI conversion and operand evaluation.  It supplies
 *   one ct,rv at this memory, not a memory-uniform rv.  The resulting
 *   abiEncoderSharedContract.abi_encoder_shared_input separately requires
 *   sb+source_cap < dimword(:256), d+output_size < dimword(:256), full
 *   source/output disjointness and both full spans disjoint from child
 *   scratch.  Its lower-level abi_encoder_shared contract STILL takes this
 *   entry predicate, plus budget, fresh variables and code/PC hypotheses.
 * Execution: abi_encoder_source_shared_run concludes an existential
 *   abi_encoder_shared_endpoint, with bytes, registered/scratch effects
 *   and abi_encoder_extend_sim.  It does not conclude gas_path_ptr or
 *   gas_outcome_ptr, nor produce ghosts or taint preservation.
 *
 * Lower-level search: extRetAbiReadCleanPtr.abi_encoder_read_window_clean
 * assumes forall mem', abi_encoder_input ... av ... mem' for a FIXED av;
 * this is stronger than the pointwise representative quantifiers above.
 * extRetAbiReadBoundsPtr.abi_encoder_read_window_covers assumes
 * abi_encoder_input ... cap ... AND ptr_covers ... cap (and allocation
 * end <= dimword).  Thus its read-window conclusion does not remove the
 * capacity-sized coverage premise.  abiEncoderSharedRecursive's complex
 * prepare theorem takes abi_encoder_shared_input; its member execution
 * spine is not a live-only counted pointer consumer.  Existing specialized
 * bytes/static counted leaves and array backedge paths do not supply a
 * general recursive encoder run from the pointwise boundary.
 * No general live-only counted consumer was found in these interfaces.
 * The missing bridge must track actual read coverage/cleanliness, output
 * and scratch separation, and counted ghost/taint execution without
 * inferring full-capacity source bounds.  This audit does not assert that
 * such a bridge follows from open_input or change any protected theory.
 *)
