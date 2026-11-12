(* Bulk reflection with sourceable parent-type premises, including zero capacity. *)
Theory abiMalformedBulkCaller
Ancestors
  abiMalformedBulkIntegration abiUnclampedInhabited abiDecoderBulk
  abiDecoderCoherence abiStaticLayoutProps vyperTypeSystem valueEncoding arithmetic

Theorem abi_malformed_bulk_constructor_parent:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),en) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray ei abi_sz mem_sz F maxn /\ ~dec_info_needs_clamp ei /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= outsz /\
  fn_inst_ids_distinct func ==>
  abi_malformed_constructor env (ArrayT ty (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) ctx func cenv cx es st en
    base_op hi src dst outsz
Proof
  rpt strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  `maxn <> 0 ==> ?a. has_type (vyper_to_abi_type env ty) a` by
    (strip_tac >>
     `type_memory_size tv <= maxn * type_memory_size tv` by
       (Cases_on `maxn` >> fs[MULT_CLAUSES]) >>
     `type_memory_size tv < dimword (:256)` by
       (qpat_x_assum `type_memory_size (ArrayTV _ _) < _` mp_tac >>
        pure_rewrite_tac[type_memory_size_def] >> decide_tac) >>
     irule abi_unclamped_static_inhabited >>
     conj_tac >- fs[assignable_type_def] >>
     qexistsl_tac [`ce`, `sf`, `tv`] >> metis_tac[]) >>
  irule abi_malformed_bulk_constructor >> metis_tac[]
QED
