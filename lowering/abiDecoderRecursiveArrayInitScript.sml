(* Execute generic dynamic-array initialization and establish recursive loop data. *)
Theory abiDecoderRecursiveArrayInit
Ancestors
  abiDecoderRecursiveArrayFacts abiDecoderRecursiveInitEffect abiDecoderRecursiveLoopContext
  abiDecoderRecursiveArrayIteration abiDecoderArrayInitReentry abiDecoderArrayInitReach
  abiDecoderArrayInitMemory abiDecoderArrayInitExec abiDecoderArrayInvariant
  abiDecoderArrayLoopInit abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect
  abiDecoderReservation abiDecoderReentry abiDecoderAllocation abiDecoderLoop abiDecoderContract
  fragExec exprLoweringProps emitHelperProps compileEnv valueEncoding
  vyperABI vyperValue venomState words list arithmetic

Theorem abi_decoder_recursive_init_data:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_effect first last lo hi_id next limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ next <= loop_next /\
  abi_decoder_operand_live loop_next ip /\ eval_operand ip prepared = SOME (n2w slot) /\
  slot < dimword (:256) /\ mem_word_at d prepared.vs_memory = n2w (LENGTH vs) ==>
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi ip src dst
    sb d slot b cap loop_next prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_effect_ranges >> strip_tac >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial prepared` by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  drule_all abi_decoder_source_frame >> strip_tac >>
  `abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared` by
    (irule abi_decoder_array_memory_init >> metis_tac[]) >>
  asm_simp_tac bool_ss [abi_decoder_recursive_loop_data_def] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decoder_recursive_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= owner_hi /\ owner_hi <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi (FST setup) src dst
      sb d slot b cap loop_st.cs_next_var prepared /\
    abi_decoder_effect first last st.cs_next_id owner_hi st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
    FLOOKUP prepared.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    mload slot prepared = 0w /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_array_init_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  `loop_st.cs_next_id <= last` by decide_tac >>
  drule_all abi_decode_array_loop_init_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  SUBGOAL_THEN ``d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ b + cap <= d`` assume_tac
  >- (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [abi_decoder_ranges_def] >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < owner_hi` by decide_tac >>
  `abi_decoder_effect first last st.cs_next_id owner_hi st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `owner_hi:num`,
      `next` |-> `st.cs_next_var`, `site` |-> `loop_st.cs_next_id-2`,
      `n` |-> `LENGTH (vs:vyperValue$value list)`,
      `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
      abi_decoder_recursive_init_effect) >> asm_simp_tac bool_ss []) >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ prepared` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  drule_all abi_decoder_recursive_init_data >> strip_tac >>
  qexistsl_tac [`prepared`, `slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_ARRAY_INIT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array initialization not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveArrayInit");
