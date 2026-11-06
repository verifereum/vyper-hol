Theory externalReturnLiveWindowResources
Ancestors
  abiEncoderLiveSource externalReturnSourceWindow abiEncoderWindow
  loweringPosts venomMemDefs

Theorem return_plan_live_window_bounded:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v p mem /\ p + val_footprint tv v <= frontier ==>
  ?at rv cap. cap = val_footprint tv v /\ p + cap <= frontier /\
    abi_encoder_window_input ei at rv p cap mem /\
    enc at rv = enc (vyper_to_abi_type env ty) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound env ty
Proof
  strip_tac >> drule_all abi_encoder_live_source_window >>
  strip_tac >> qexistsl_tac [`at`, `rv`, `val_footprint tv v`] >> simp[]
QED

Theorem expression_live_window_resources:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at ce cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand src s = SOME p /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\ sb.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  abi_enc_plan (get_tenv cx) ty ei /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  val_in_memory tv v (w2n p) s.vs_memory /\
  w2n p + val_footprint tv v <= s.vs_alloca_next ==>
  ?at rv cap. cap = val_footprint tv v /\
    w2n p + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (w2n p,cap) (b,sz) /\
    abi_encoder_window_input ei at rv (w2n p) cap s.vs_memory /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    LENGTH (enc at rv) <= vyper_abi_size_bound (get_tenv cx) ty
Proof
  strip_tac >>
  `venomMemDefs$regions_disjoint
     (w2n p,val_footprint tv v) (b,sz)` by
    (irule expression_source_window_disjoint >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  drule_all return_plan_live_window_bounded >>
  strip_tac >> qexistsl_tac [`at`, `rv`, `cap`] >> gvs[]
QED

(* The resource window is unchanged by wrapping; the tuple encoding is not
   identified with its child's encoding. *)
Theorem return_singleton_live_window_resources:
  abi_encoder_window_input ei at rv p cap mem /\
  p + cap <= frontier /\ venomMemDefs$regions_disjoint (p,cap) (b,sz) /\
  cap <= mem_sz /\ abi_sz = abi_member_head_size at /\
  dyn = is_dynamic at ==>
  abi_encoder_window_input (AbiComplex [(ei,abi_sz,mem_sz,dyn)])
    (Tuple [at]) (ListV [rv]) p cap mem /\
  p + cap <= frontier /\ venomMemDefs$regions_disjoint (p,cap) (b,sz)
Proof
  strip_tac >> gvs[] >> irule abi_encoder_window_singleton >> simp[]
QED
