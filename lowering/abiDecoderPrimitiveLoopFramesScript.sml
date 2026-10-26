(* Widen each primitive store to the enclosing array and scratch footprint. *)
Theory abiDecoderPrimitiveLoopFrames
Ancestors
  abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopInvariant
  abiDecoderArrayAdvance abiDecoderFrameCompose abiDecoderFrame
  abiDecoderReentry abiDecoderContract compileEnv valueEncoding words list arithmetic

Theorem abi_decoder_footprint_member_frame:
  abi_decode_footprint_frame [(d,sz)] s t /\ MEM (d,sz) fp ==>
  abi_decode_footprint_frame fp s t
Proof
  strip_tac >> irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d,sz)]` >> simp[] >>
  qexistsl_tac [`d`, `sz`] >> simp[]
QED

Theorem abi_decoder_frame_in_footprint:
  abi_decode_frame d sz s t /\ MEM (d,sz) fp ==>
  abi_decode_footprint_frame fp s t
Proof
  strip_tac >> irule abi_decoder_footprint_member_frame >>
  qexistsl_tac [`d`, `sz`] >> simp[GSYM abi_decode_frame_footprint]
QED

Theorem abi_decoder_primitive_cell_frame:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  j < LENGTH vs /\ abi_decode_frame (d + 32 + j * 32) 32 s t ==>
  abi_decode_footprint_frame fp s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  mp_tac (Q.SPECL [`j`, `LENGTH (vs:vyperValue$value list)`, `maxn`, `d`]
    abi_decoder_array_cell_bound) >> impl_tac >- simp[] >> strip_tac >>
  `abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s t` by
    (irule abi_decode_frame_widen >>
     qexistsl_tac [`d + 32 + j * 32`, `32`] >>
     asm_simp_tac bool_ss [] >>
     pure_rewrite_tac [GSYM ADD_ASSOC] >> irule LESS_EQ_ADD) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  irule abi_decoder_frame_in_footprint >>
  qexistsl_tac [`d`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_primitive_body_rel:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  j < LENGTH vs /\ first <= next /\ fresh_vars_wrt limit_st t /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_frame (d + 32 + j * 32) 32 s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_halted = s.vs_halted ==>
  abi_decoder_loop_rel first limit_st fp s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_cell_frame >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `next:num`] abi_decoder_loop_rel_intro) >>
  simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_PRIMITIVE_LOOP_FRAMES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI primitive loop frame not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderPrimitiveLoopFrames");
