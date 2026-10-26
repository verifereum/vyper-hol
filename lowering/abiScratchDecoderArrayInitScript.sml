(* Actual source-valid array initialization with precise physical scratch effects. *)
Theory abiScratchDecoderArrayInit
Ancestors
  abiScratchDecoderInitReentry abiScratchDecoderRanges abiScratchDecoderTransport
  abiScratchDecoderContract abiScratchEncoderContract abiScratchEffectWiden
  abiDecoderValidArrayInitInputs abiDecoderValidArrayMemory abiDecoderValidContract
  abiDecoderArrayInitReach abiDecoderArrayInitReentry abiDecoderCoherence abiDecoderTypedContract
  abiDecoderAllocation abiDecoderReentry abiDecoderLoop abiDecoderContract
  abiEncoderArrayFrame abiEncoder fragExec compileEnv valueEncoding
  vyperABI vyperValue contractABI venomState words list arithmetic

Theorem abi_scratch_decoder_array_init_inputs:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\ h < dimword (:256)) /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  drule abi_decoder_valid_array_pre_observations >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_init_inputs >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Once type_memory_bytes_def] >>
  `abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac (srw_ss()) []) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src dst opc hi sb d first last b cap actual /\
    abi_decoder_valid_array_memory opc bs tv vs sb d 0 actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\
    abi_decoder_operand_live loop_st.cs_next_var (FST setup) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_array_init_inputs >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_scratch_decoder_init_from_state >>
    disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  disch_then (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Once type_memory_bytes_def] >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (mp_tac (Q.INST [`child_lo` |-> `st.cs_next_id`, `child_hi` |-> `loop_st.cs_next_id`,
       `child_next` |-> `st.cs_next_var`, `child_d` |-> `d:num`, `child_sz` |-> `32:num`,
       `lo` |-> `st.cs_next_id`, `hi` |-> `loop_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_effect_widen) >>
     asm_simp_tac (srw_ss()) []) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap actual` by
    (mp_tac (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`,
       `v` |-> `ArrayV (DynArrayV vs)`, `lo` |-> `st.cs_next_id`,
       `hi_id` |-> `loop_st.cs_next_id`, `next` |-> `st.cs_next_var`, `hi_op` |-> `hi:operand`]
       abi_scratch_decoder_input_effect) >> asm_simp_tac (srw_ss()) []) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) loop_st src dst opc hi sb d first last b cap actual` by
    (irule abi_scratch_decoder_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source opc actual) = bs` by
    fs[abi_scratch_decoder_input_def] >>
  `abi_decoder_valid_array_memory opc bs tv vs sb d 0 actual` by
    (irule abi_decoder_valid_array_memory_init >> asm_simp_tac bool_ss []) >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  qexistsl_tac [`actual`, `slot`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_ARRAY_INIT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical source-valid array initializer not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderArrayInit");
