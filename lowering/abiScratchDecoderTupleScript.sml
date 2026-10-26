(* Tuple decoding follows arbitrary source-valid member offsets and payloads. *)
Theory abiScratchDecoderTuple
Ancestors
  abiScratchDecoderContract abiScratchDecoderLeaves abiDecoderValidTuple
  abiDecoderValidContract abiScratchDecoderTupleInputs abiScratchDecoderComplexExecute
  abiDecoderValidLeaves abiDecoderMemberInfos abiDecoderMembers abiDecoderCoherence
  abiDecoderEffect abiDecoderReentry abiDecoderTypedContract abiDecoderContract
  fragExec compileEnv valueEncoding valueEncodingProps vyperABI vyperValue
  contractABI venomState words list

Theorem abi_scratch_decoder_tuple:
  LIST_REL (abi_scratch_decoder ce env sf) tys tvs ==>
  abi_scratch_decoder ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_tuple_inputs >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_scratch_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem abi_scratch_decoder_base_tuple:
  !bts. abi_scratch_decoder ce env sf
    (TupleT (MAP BaseT bts)) (TupleTV (MAP BaseTV bts))
Proof
  gen_tac >>
  `LIST_REL (abi_scratch_decoder ce env sf) (MAP BaseT bts) (MAP BaseTV bts)` by
    (Induct_on `bts` >> simp[abi_scratch_decoder_base]) >>
  `EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) (MAP BaseT bts)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `bt` >> strip_tac >>
     MATCH_ACCEPT_TAC (Q.SPEC `bt` abi_decoder_valid_base_member_nonempty)) >>
  irule abi_scratch_decoder_tuple >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_TUPLE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical tuple decoder not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderTuple");

