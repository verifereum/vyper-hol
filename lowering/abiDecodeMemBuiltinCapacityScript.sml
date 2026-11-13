(* The existing caller post also supplies the memory judgment's capacity. *)
Theory abiDecodeMemBuiltinCapacity
Ancestors
  exprSimAbiDecodeBodyEntry exprSimAbiDecodeEntryMetadata exprSimAbiDecodeEntryLayout
  exprSimAbiDecodeValueFrame exprSimAbiDecodeStateFrame
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeQuantifiedLift
  exprSimAbiDecodeEndpointFrame abiDecodeUnwrapCase exprSimMemDefs
  exprSimHypsDefs exprLowering loweringPosts abiDecoderSiteEffect actualDecoderSites
  allocaSiteResource localPtrsProps compileEnv context valueEncoding vyperAST
  venomState words arithmetic list

Theorem abi_decode_mem_caller_capacity:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  evaluate_type (get_tenv cx) ty = SOME rtv /\
  vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa fin s0
    ee (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
  abi_decode_immutable_success ce (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [rtv] else rtv)
    bs out d start fin ctx func cx ee s t ==>
  vv_store_bound cx (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty [e]))
    (lowered_value_type ce (TypeBuiltin ann (AbiDecode unwrap) ty [e])) ee
    (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> `ann = ty` by metis_tac[abi_decode_body_target] >>
  qpat_x_assum `ann = ty` SUBST_ALL_TAC >>
  `abi_decode_success_closed ce (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)
    (if unwrap /\ needs_external_call_wrap ty then TupleTV [rtv] else rtv)
    bs out d start fin ctx func s t` by fs[abi_decode_immutable_success_def] >>
  drule abi_decode_success_value >> strip_tac >>
  drule abi_decode_success_address_bound >> strip_tac >>
  drule abi_decode_closed_effect >> strip_tac >>
  rename1 `decode_site_effect ctx func start.cs_next_var writes s middle` >>
  `alloca_inv t` by
    (fs[decode_site_effect_def, decode_site_resources_def] >>
     irule alloca_inv_fields >> qexists_tac `middle` >> simp[]) >>
  `abi_decode_root_metadata ce (get_tenv cx)` by
    (irule abi_decode_root_metadata_inv >> qexistsl_tac [`env`,`es`] >>
     fs[expr_body_pre_def]) >>
  `type_memory_bytes ce ty = type_memory_size rtv` by
    (irule abi_decode_descended_memory_size >>
     qexistsl_tac [`get_tenv cx`,`get_tenv cx`] >> simp[]) >>
  `d+type_memory_size rtv <= t.vs_alloca_next` by
    (qpat_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
     drule_all alloca_site_registered_below >> simp[abi_decode_output_size]) >>
  conj_tac
  >- (mp_tac (Q.INST [
        `e` |-> `TypeBuiltin ty (AbiDecode unwrap) ty [e]`, `cenv` |-> `ce`,
        `vt` |-> `ty`, `p` |-> `mk_ptr out LocMemory`, `sb` |-> `fin`,
        `es'` |-> `ee`, `tv` |-> `Value v`, `ftv` |-> `rtv`, `fw` |-> `n2w d`]
        vv_store_bound_capacity) >>
      (impl_tac >- gvs[expr_type_def, mk_ptr_def, w2n_n2w]) >>
      simp[lowered_value_type_def]) >>
  drule decode_site_effect_frontier >> simp[]
QED
