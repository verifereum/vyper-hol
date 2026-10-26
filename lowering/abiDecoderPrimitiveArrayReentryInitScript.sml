(* Typed primitive-array entry under an enclosing loop's freshness/budget bounds. *)
Theory abiDecoderPrimitiveArrayReentryInit
Ancestors
  abiDecoderArrayInitReentry abiDecoderArrayInit abiDecoderPrimitiveArrayInit
  abiDecoderPrimitiveArrayFacts abiDecoderArrayLoopInit abiDecoderPrimitiveLoopContext
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry
  abiDecoderAllocation abiDecoderLoop abiDecoderContract abiDecoderFrame fragExec
  exprLoweringProps emitHelperProps compileEnv valueEncoding venomState finite_map words list
  arithmetic

Theorem abi_decoder_pre_pruned_operands:
  abi_decoder_pre ce env ty tv di av v st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_pre_def, abi_decoder_ranges_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by simp[abi_decoder_operand_live_def] >>
  metis_tac[abi_decoder_pruned_operand_defined]
QED

Theorem abi_decoder_primitive_array_reentry_pre_facts:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * 32 <= h /\ h < dimword (:256)) /\
  (d + 32 <= b \/ b + cap <= d) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * 32
Proof
  strip_tac >> drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[abi_decoder_prune_eval, Excl "enc_def"] >>
  rename1 `eval_operand hi initial = SOME (n2w h)` >>
  disj2_tac >> qexists_tac `h` >> simp[]
QED

Theorem abi_decoder_primitive_array_reentry_initialize:
  abi_decode_array_loop_init dst src opc hi maxn 32 st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st last src dst opc hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ fn_has_code st loop_st fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot
      [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(slot,32)] /\
    abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared /\
    fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\ mload slot prepared = 0w /\
    prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    b <= slot /\ slot + 32 <= b + cap /\ abi_decoder_budget first last b cap prepared /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op prepared = SOME w) /\
    abi_decode_footprint_frame [(d,32);(b,cap)] initial prepared /\
    abi_decode_footprint_frame [(d,32);(slot,32)] initial prepared /\
    FLOOKUP prepared.vs_allocas (loop_st.cs_next_id - 2) = SOME (slot,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP prepared.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    abi_decode_sim ctx fn initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_reentry_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx fn initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var initial`,
    `t` |-> `prepared:venom_state`] abi_decoder_array_init_memory) >>
  impl_tac >- asm_simp_tac bool_ss [abi_decoder_footprint_prune_before] >> strip_tac >>
  `eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d)`
    by metis_tac[] >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  `abi_decoder_loop_inputs loop_st.cs_next_var (FST setup) src dst sb d slot prepared` by
    (simp_tac bool_ss [abi_decoder_loop_inputs_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  qexistsl_tac [`prepared`, `slot`] >> gvs[Excl "enc_def"]
QED
