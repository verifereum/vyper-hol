Theory exprSimAbiDecodeConsumerProbe
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeEndpointFrame exprLoweringProps compileEnv venomState
  finite_map vyperTypeABI vyperTyping abiBoundaryChecks
  valueTypingMemoryProps exprSimProps

Theorem abi_decode_immutable_separation_frame:
  immutable_alloca_sep func ce cx es s /\
  abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas t /\
  (!name lo sz. local_region ce es.scopes t name lo sz ==>
    local_region ce es.scopes s name lo sz) ==>
  immutable_alloca_sep func ce cx es t
Proof
  strip_tac >>
  match_mp_tac (Q.SPECL [`func`,`ce`,`cx`,`es`,`es`,`s`,`t`]
                  immutable_alloca_sep_frame) >>
  gvs[abi_decode_allocation_floor_def] >> metis_tac[]
QED

(* Project the wrapped value at the existing endpoint, without executing again. *)
Theorem abi_decode_singleton_endpoint_projection:
  evaluate_abi_decode env (TupleT [ty]) bs = INL wrapped /\
  evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv]) /\
  val_in_memory (TupleTV [tv]) wrapped d mem ==>
  ?v. wrapped = ArrayV (TupleV [v]) /\
      value_has_type tv v /\ val_in_memory tv v d mem
Proof
  strip_tac >>
  drule_all evaluate_abi_decode_well_typed >> strip_tac >>
  Cases_on `wrapped` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv] >>
  rename1 `values_have_types [tv] vs` >>
  Cases_on `vs` >> gvs[value_has_type_def] >>
  rename1 `values_have_types [] rest` >>
  Cases_on `rest` >> gvs[value_has_type_def, val_in_memory_singleton_tuple]
QED

Theorem abi_decode_success_memory_bounds:
  evaluate_abi_decode env ty bs = INL v /\
  evaluate_type env ty = SOME tv ==>
  val_wf tv v /\ val_footprint tv v <= type_memory_size tv
Proof
  strip_tac >> drule_all evaluate_abi_decode_well_typed >> strip_tac >>
  drule value_has_type_memory_wf >> strip_tac >>
  simp[val_footprint_le]
QED

(* Consumer audit (not a claim that the full parent boundary is proved).
   At the child endpoint s, with source state es fixed through the decoder:

   stmt_state_rel:
   - alloca_inv, alloca_room, fmp_room, and registered ALLOCA sizes are exactly
     decode_site_effect_resources / decode_site_resources.
   - immutable_alloca_sep uses abi_decode_immutable_separation_frame above.
     The allocation floor supplies old-or-new rows, not local-region transport.
   - immutable_base_zero uses immutable_base_zero_frame: static-frame labels
     and live immutable-base operands must be supplied by entry freshness.
   - state_rel's storage/transient/accounts/logs/call context/outcomes/requests/
     deletions clauses use decode_static_frame (and tolerate rd/prev closure).
     storage_vars_rel/transient_vars_rel do not depend on target state.
   - local_ptrs_rel uses local_ptrs_rel_mem_agree. Its missing caller fact is
       !name b sz. local_region ce es.scopes s name b sz ==>
         mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory.
     This requires decode_protects writes over all live local regions, not just
     output lookup/floor. Also discharge live PtrVar lookup equality from
     entry freshness. The floor supplies new-row backing once these hold.
   - immutables_rel additionally needs memory agreement on immutable regions
     in constructor mode: establish decode_protects writes for those regions.

   vv_post:
   - vv_holds needs eval_operand out t = SOME (n2w d), memory decoding at d,
     evaluated parent type and read_result(Value v); success post supplies
     wrapped memory and source success. Unwrapped branch uses these directly.
     Wrapped branch uses abi_decode_singleton_endpoint_projection at this
     SAME t and evaluate_type wrapped = SOME(TupleTV[tv]); no re-execution.
   - vv_at uses success_memory_bounds above, output allocation lookup,
     sa.next<=outid<sb.next, type_memory_size tv<=outsz, and disjointness of
     the output allocation from every local. The output-size bound also makes
     n2w d unwrapped. Wrapped memory-size equality is
     singleton_tuple_memory_sizes. Output lookup alone gives no disjointness.
   - not_fresh variable frame follows child frame plus decoder live operands.
   - original allocation lookup follows child frame plus site-effect lookup.
   - original allocation memory frame requires protection of each original
     row with aid<sa.next and the vv_post local-disjoint side condition.
   - locals_kept uses locals_kept_regions plus live-local protection, then
     locals_kept_trans with the child. Source scopes are the child's es.scopes.

   Remaining integration boundaries must therefore discharge protection for
   locals, constructor immutables and eligible original allocations from
   actual-site interval separation and entry invariants; freshness/live
   operand facts; and output allocation local-disjointness. No conclusion
   above follows from floor alone, and no new judgment premise is proposed.
*)
