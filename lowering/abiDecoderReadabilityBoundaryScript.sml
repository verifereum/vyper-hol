(* The former zero-array boundary now executes successfully for every unused
   payload offset. The old readable-type exclusion is still exhibited below. *)
Theory abiDecoderReadabilityBoundary
Ancestors
  abiDecoderReadableTypes abiDecoderMemberSetup abiDecoderContract abiEncoder
  vyperCompiler compileEnv exprLowering exprLoweringProps vyperABI vyperValue vyperTypeSystem
  contractABI venomState venomExecSemantics words list finite_map
Libs
  wordsLib

Theorem zero_fixed_array_member_source:
  let ty = TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)] in
  let bs = word_to_bytes (4096w:256 word) T in
  evaluate_type FEMPTY ty =
    SOME (TupleTV [ArrayTV (BaseTV (BytesT (Dynamic 1))) (Fixed 0)]) /\
  assignable_type FEMPTY ty /\
  evaluate_abi_decode FEMPTY ty bs = INL (ArrayV (TupleV [ArrayV (SArrayV [])])) /\
  ~abi_decoder_readable_type FEMPTY ty
Proof
  EVAL_TAC >> simp[dimword_def, type_slot_size_def] >> EVAL_TAC
QED

Theorem zero_fixed_array_member_descriptor:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 1))) (Fixed 0)]) =
  DecComplex T [(DecComplex T [],32,0)]
Proof
  simp[type_to_abi_dec_info_def, is_abi_dynamic_def, abi_embedded_static_size_def,
    abi_static_size_def, type_memory_bytes_def]
QED

Theorem zero_fixed_array_member_executes:
  !payload:bytes32.
  let start = initial_compile_state "entry" in
  let end_st = SND (compile_abi_decode_to_buf (Lit 256w) (Lit 32w) MLOAD (Lit 64w)
    (DecComplex T [(DecComplex T [],32,0)]) start) in
  ?actual. run_inst_seq (emitted_insts start end_st)
    (mstore 32 payload (init_venom_state "entry")) = OK actual /\
    actual.vs_memory = (mstore 32 payload (init_venom_state "entry")).vs_memory
Proof
  simp_tac bool_ss [LET_THM] >> qx_gen_tac `payload` >>
  CONV_TAC (BINDER_CONV (LAND_CONV (LAND_CONV EVAL))) >> simp[] >>
  CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_READABILITY_BOUNDARY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder readability boundary not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReadabilityBoundary");

