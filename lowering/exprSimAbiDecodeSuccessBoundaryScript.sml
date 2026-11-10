Theory exprSimAbiDecodeSuccessBoundary
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeValueFrame exprSimAbiDecodeResources exprSimAbiDecodeEntryTyping
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeOblivious
  exprSimAbiDecodeStateFrame freshWrites
  exprBopSimProps exprLoweringProps loweringPosts compileEnv venomState
  abiValidBytesUnwrap abiDecodeUnwrapCase exprSimAbiDecodeEntryLayout
  exprSimAbiDecodeEntryMetadata exprSimAbiDecodeConsumerProbe
  vyperEvalExprPreservesScopesDom vyperTypeSystem vyperTypeInvariants
  exprSimHypsDefs vyperTypeABI arithmetic
  valueTypingMemoryProps valueEncodingProps vyperAST vyperTyping finite_map

(* Compose the decoder frames with the actual post of the unwrapped child.
   The value-specific clauses are discharged by the two callers below. *)
Theorem abi_decode_caller_frames:
  expr_post ctx func ce cx e es sa start s0 es1 child data s /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= start.cs_next_var /\ sa.cs_next_id <= start.cs_next_id /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce dec_ty)
    (abi_static_size ce.ce_struct_fields dec_ty) (abi_size_bound ce.ce_struct_fields dec_ty)
    (type_memory_bytes ce dec_ty) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  abi_decode_immutable_success ce (get_tenv cx) dec_ty dec_tv bs out d start final
    ctx func cx es1 s t /\
  vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) es1 t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  type_memory_size tv <= type_memory_bytes ce dec_ty ==>
  vv_post ctx func ce cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es sa final s0
    es1 (Value v) (LocatedValue ty (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `cs_extends start final` by metis_tac[lower_abi_decode_frag_facts] >>
  `!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)` by
    metis_tac[abi_decode_resources_code_member] >>
  `local_ptrs_reserved ce start` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func ce cx es1 s` by fs[expr_post_def] >>
  `alloca_inv s /\ local_ptrs_rel func ce es1.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `abi_decode_success_closed ce (get_tenv cx) dec_ty dec_tv bs out d start final
    ctx func s t` by fs[abi_decode_immutable_success_def] >>
  `stmt_state_rel ctx func ce cx es1 t` by
    (drule_all abi_decode_success_stmt_state_rel >> simp[]) >>
  `vv_at ce cx ty sa final es1 (Value v) (LocatedValue ty (mk_ptr out LocMemory)) t` by
    (drule_all abi_decode_success_vv_at >> simp[]) >>
  `locals_kept ce es1 es1 s t` by
    (drule_all abi_decode_success_locals_kept >> simp[]) >>
  simp[vv_post_def, expr_type_def] >> rpt conj_tac
  >- simp[contextTheory.mk_ptr_def]
  >- (rpt strip_tac >>
      `not_fresh_at start x` by metis_tac[not_fresh_at_mono] >>
      `lookup_var x s = SOME w` by metis_tac[expr_post_def] >>
      drule_all abi_decode_success_old_var >> simp[])
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME b` by metis_tac[expr_post_def] >>
      drule_all abi_decode_success_old_allocation >> simp[])
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[expr_post_def] >>
      `aid < start.cs_next_id` by decide_tac >>
      `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (drule_all abi_decode_success_old_memory >> simp[]) >>
      metis_tac[expr_post_def]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `s`] >>
  fs[expr_post_def]
QED

Theorem abi_decode_caller_success:
  expr_sim_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_post ctx func ce cx e es sa start s0 es1 (BytesV bs) data s /\
  eval_expr cx e es = (res,es1) /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  abi_decode_immutable_success ce (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
    bs out d start final ctx func cx es1 s t ==>
  ?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
      es1 (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `ann = ty` by metis_tac[abi_decode_pre_target] >>
  qpat_x_assum `ann = ty` SUBST_ALL_TAC >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[eval_expr_preserves_scopes_dom] >>
  `sa.cs_next_var <= start.cs_next_var /\ sa.cs_next_id <= start.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `abi_decode_root_metadata ce (get_tenv cx)` by
    (irule abi_decode_root_metadata_inv >> qexistsl_tac [`env`, `es`] >>
     fs[expr_sim_pre_def]) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    (irule abi_decode_descended_memory_size >>
     qexistsl_tac [`get_tenv cx`, `get_tenv cx`] >> simp[]) >>
  `type_memory_size tv <= type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    simp[abi_decode_output_size] >>
  `evaluate_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) =
    SOME (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)` by
    metis_tac[abi_decode_wrapped_type] >>
  `abi_decode_success_closed ce (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)
    bs out d start final ctx func s t` by fs[abi_decode_immutable_success_def] >>
  `?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    vv_holds ce cx ty (Value v) (LocatedValue ty (mk_ptr out LocMemory)) es1 t /\
    value_has_type tv v` by
    (Cases_on `unwrap /\ needs_external_call_wrap ty`
     >- (gvs[] >> drule_all abi_decode_success_singleton_vv_holds >>
         disch_then (qspec_then `es1` strip_assume_tac) >>
         `value_has_type tv v` by
           (drule_all evaluate_abi_decode_well_typed >> simp[value_has_type_def]) >>
         qexists_tac `v` >> gvs[abi_source_decode_wrapping_iff]) >>
     fs[] >> drule_all abi_decode_success_vv_holds >>
     disch_then (qspec_then `es1` strip_assume_tac) >>
     `value_has_type tv v` by metis_tac[evaluate_abi_decode_well_typed] >>
     qexists_tac `v` >> gvs[abi_source_decode_wrapping_iff]) >>
  qexists_tac `v` >> simp[] >>
  metis_tac[abi_decode_caller_frames]
QED
