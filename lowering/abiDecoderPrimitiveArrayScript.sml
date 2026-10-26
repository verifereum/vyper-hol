(* Typed execution of complete primitive-array decoders, with and without clamps. *)
Theory abiDecoderPrimitiveArray
Ancestors
  abiDecoderPrimitiveArrayCode abiDecoderPrimitiveArrayInit abiDecoderPrimitiveArrayFacts
  abiDecoderBulkExecute
  abiDecoderPrimitiveLoopEntry abiDecoderPrimitiveLoopInvariant abiDecoderPrimitiveLoopContext
  abiDecoderArrayInitMemory abiDecoderArrayInitExec abiDecoderArrayLoopInit
  abiDecoderCoherence abiDecoderTypedContract abiDecoderReentry abiDecoderLoop
  abiDecoderAllocation abiDecoderContract abiDecoderFrame fragExec
  exprLoweringProps compileEnv valueEncoding venomState words list arithmetic

Theorem abi_decoder_loop_frame_to_arena:
  abi_decode_footprint_frame [(d,outsz);(slot,32)] s t /\
  b <= slot /\ slot + 32 <= b + cap ==>
  abi_decode_footprint_frame [(d,outsz);(b,cap)] s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d,outsz);(slot,32)]` >> simp[] >> rw[]
  >- (qexistsl_tac [`d`, `outsz`] >> simp[]) >>
  qexistsl_tac [`b`, `cap`] >> simp[]
QED

Theorem abi_decoder_clamped_array:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  dec_info_needs_clamp (DecPrimWord clamp) /\ fn_has_code st end_st fn /\
  (!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) end_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~t.vs_halted /\
    abi_decode_sim ctx fn initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_pre_ranges >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_dynarray_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_primitive_array_code >> strip_tac >>
  drule_all abi_decoder_primitive_array_initialize >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`limit_st` |-> `end_st:compile_state`] abi_decoder_primitive_dyn_loop)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_assum `abi_decoder_loop_rel _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_rel_def]) >>
  `abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t` by
    (drule_all abi_decoder_budget_transport >> simp[]) >>
  `!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[] >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial prepared` by (drule_all abi_decoder_array_init_frame_widen >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    prepared t` by (drule_all abi_decoder_loop_frame_to_arena >> simp[]) >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial t` by
    (irule abi_decode_footprint_frame_trans >> qexists_tac `prepared` >> simp[]) >>
  `abi_decode_sim ctx fn initial t` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]) >>
  qexists_tac `t` >> simp[abi_decoder_post_def]
QED

Theorem abi_decoder_primitive_array:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) st = ((),end_st) /\
  fn_has_code st end_st fn /\
  (dec_info_needs_clamp (DecPrimWord clamp) ==>
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray (DecPrimWord clamp) 32 32 F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st end_st.cs_next_id src dst opc hi sb d b cap initial /\
  abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) end_st d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    abi_decoder_budget st.cs_next_id end_st.cs_next_id b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~t.vs_halted /\
    abi_decode_sim ctx fn initial t
Proof
  Cases_on `dec_info_needs_clamp (DecPrimWord clamp)`
  >- (strip_tac >>
      `!bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      drule_all abi_decoder_clamped_array >> disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  strip_tac >> drule_all abi_decoder_bulk_execute >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_ARRAY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive array decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveArray");
