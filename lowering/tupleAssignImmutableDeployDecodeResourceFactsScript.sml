(* Fresh decoder reservation credit; reentered output sites are not covered. *)
Theory tupleAssignImmutableDeployDecodeResourceFacts
Ancestors
  abiBuiltinSource abiBuiltinAllocation abiDecoderAllocation abiDecoderFrame
  abiBuiltinDecodeEffect abiDecoderReentry loweringStateRelDefs venomState
  finite_map pred_set words arithmetic

Theorem tuple_immutable_decode_fresh_resources:
  FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st mn mx) = NONE /\
  abi_builtin_decode_output_site st mn mx < first /\
  first <= abi_builtin_decode_output_site st mn mx + 2 /\
  (!id. id IN abi_decoder_ids first last ==> FLOOKUP s.vs_allocas id = NONE) /\
  mn <= cnt /\ cnt <= mx /\ mx < dimword (:256) /\
  p + 32 + cnt <= s.vs_alloca_next /\
  s.vs_alloca_next + outsz + 32 * CARD (abi_decoder_ids first last) < dimword (:256) ==>
  abi_builtin_decode_resources st first last mn mx outsz cnt p
    s.vs_alloca_next (s.vs_alloca_next + outsz)
    (32 * CARD (abi_decoder_ids first last)) s
Proof
  strip_tac >>
  `abi_decoder_budget first last (s.vs_alloca_next + outsz)
     (32 * CARD (abi_decoder_ids first last))
     (abi_builtin_allocate_state (abi_builtin_decode_output_site st mn mx) outsz s)` by
    (irule abi_decoder_budget_empty >>
     simp[abi_builtin_allocate_state_def] >> rpt strip_tac >>
     `id <> abi_builtin_decode_output_site st mn mx` by
       (gvs[abi_decoder_ids_def] >> decide_tac) >>
     simp[FLOOKUP_UPDATE]) >>
  simp[abi_builtin_decode_resources_def, abi_footprint_disjoint_def] >>
  decide_tac
QED

(* The effect preserves successful operands only: initial scoped pointer
   coverage is needed to rule out newly appearing final local regions. *)
Theorem tuple_immutable_decode_local_frame:
  abi_builtin_decode_effect first last st final limit_st d outsz b cap s t /\
  local_ptrs_reserved ce st /\
  (!name entry p sz.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    ?w. lookup_var p s = SOME w) /\
  (!name base sz. local_region ce scopes s name base sz ==>
    regions_disjoint d outsz base sz) ==>
  !name base sz. local_region ce scopes t name base sz ==>
    regions_disjoint d outsz base sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!name base sz. local_region _ _ s _ _ _ ==> _` irule >>
  qexists_tac `name` >>
  qpat_x_assum `local_region _ _ t _ _ _` mp_tac >>
  simp[local_region_def] >> strip_tac >>
  `?w0. lookup_var p s = SOME w0` by metis_tac[] >>
  `abi_decoder_operand_live st.cs_next_var (Var p)` by
    (gvs[local_ptrs_reserved_def, not_fresh_at_def,
       abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> metis_tac[]) >>
  `lookup_var p t = SOME w0` by
    (gvs[abi_builtin_decode_effect_def] >>
     first_x_assum (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  gvs[] >> metis_tac[]
QED

Theorem tuple_immutable_decode_local_frame_from_ptrs_rel:
  abi_builtin_decode_effect first last st final limit_st d outsz b cap s t /\
  local_ptrs_reserved ce st /\ local_ptrs_rel func ce scopes s /\
  (!name base sz. local_region ce scopes s name base sz ==>
    regions_disjoint d outsz base sz) ==>
  !name base sz. local_region ce scopes t name base sz ==>
    regions_disjoint d outsz base sz
Proof
  strip_tac >>
  `!name entry p sz.
     lookup_scopes name scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     ?w. lookup_var p s = SOME w` by
    (gvs[local_ptrs_rel_def] >> metis_tac[]) >>
  metis_tac[tuple_immutable_decode_local_frame]
QED
