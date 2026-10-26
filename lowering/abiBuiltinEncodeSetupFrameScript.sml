(* Exact allocator metadata and memory frame for a method-ID setup store.
   write_size records the full store width independently of returned prefix size. *)
Theory abiBuiltinEncodeSetupFrame
Ancestors
  abiBuiltinAllocationState abiEncoderInputFrame abiEncoderInput abiDecoderArrayInitExec
  abiDecoderAllocation abiDecoderContract abiDecoderFrameCompose abiDecoderReentry
  compileEnv venomState finite_map words list arithmetic

Definition abi_builtin_encode_setup_frame_def:
  abi_builtin_encode_setup_frame next site outsz p write_size s t <=>
    (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    abi_decode_frame (p+32) write_size s t /\ t.vs_halted = s.vs_halted /\
    t.vs_allocas = (abi_builtin_allocate_state site outsz s).vs_allocas /\
    t.vs_alloca_next = (abi_builtin_allocate_state site outsz s).vs_alloca_next
End

Theorem abi_builtin_encode_setup_frame_compose:
  abi_builtin_allocation_frame next site outsz initial addressed /\
  abi_decode_frame (p+32) write_size addressed prepared /\
  prepared.vs_allocas = addressed.vs_allocas /\ prepared.vs_alloca_next = addressed.vs_alloca_next /\
  prepared.vs_halted = addressed.vs_halted /\
  (!op w. abi_decoder_operand_live child_next op /\ eval_operand op addressed = SOME w ==>
    eval_operand op prepared = SOME w) /\ next <= child_next ==>
  abi_builtin_encode_setup_frame next site outsz p write_size initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  `abi_decode_frame (p+32) write_size initial prepared` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >>
     asm_simp_tac bool_ss [abi_decode_frame_def]) >>
  asm_simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> rpt strip_tac >>
  `eval_operand op addressed = SOME w` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `!op w. abi_decoder_operand_live child_next op /\ _ ==> _` irule >>
  asm_simp_tac bool_ss [] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `next` >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_setup_frame_budget:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  (abi_decoder_budget first last b cap t <=>
    abi_decoder_budget first last b cap (abi_builtin_allocate_state site outsz s))
Proof
  simp_tac bool_ss [abi_builtin_encode_setup_frame_def] >> strip_tac >>
  irule abi_decoder_budget_transport >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_setup_frame_input:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  abi_encoder_input ei at av sb source_cap s.vs_memory /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) ==>
  abi_encoder_input ei at av sb source_cap t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  `mem_bytes_at sb source_cap s.vs_memory = mem_bytes_at sb source_cap t.vs_memory` by
    (irule EQ_SYM >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_SETUP_FRAME_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder setup frame not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeSetupFrame");
