(* Tuple decoding follows arbitrary source-valid member offsets and payloads. *)
Theory abiDecoderValidTuple
Ancestors
  abiDecoderValidContract abiDecoderValidTupleInputs abiDecoderValidComplexExecute
  abiDecoderValidLeaves abiDecoderMemberInfos abiDecoderMembers abiDecoderCoherence
  abiDecoderEffect abiDecoderReentry abiDecoderTypedContract abiDecoderContract
  fragExec compileEnv valueEncoding valueEncodingProps vyperABI vyperValue
  contractABI venomState words list

Theorem abi_decoder_valid_correct_tuple:
  LIST_REL (abi_decoder_valid_correct ce env sf) tys tvs ==>
  abi_decoder_valid_correct ce env sf (TupleT tys) (TupleTV tvs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_tuple_inputs >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_decoder_valid_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [val_in_memory_tuple]
QED

Theorem abi_decoder_valid_base_member_nonempty:
  !bt. is_dynamic (vyper_to_abi_type env (BaseT bt)) ==>
    !elem. vyper_to_abi_type env (BaseT bt) <> Array (SOME 0) elem
Proof
  Cases >> simp[vyper_to_abi_type_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >> simp[]
QED

Theorem abi_decoder_valid_correct_base_tuple:
  !bts. abi_decoder_valid_correct ce env sf
    (TupleT (MAP BaseT bts)) (TupleTV (MAP BaseTV bts))
Proof
  gen_tac >>
  `LIST_REL (abi_decoder_valid_correct ce env sf) (MAP BaseT bts) (MAP BaseTV bts)` by
    (Induct_on `bts` >> simp[abi_decoder_valid_correct_base]) >>
  `EVERY (\ty. is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) (MAP BaseT bts)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `bt` >> strip_tac >>
     MATCH_ACCEPT_TAC (Q.SPEC `bt` abi_decoder_valid_base_member_nonempty)) >>
  irule abi_decoder_valid_correct_tuple >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_TUPLE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI actual-source tuple decoder not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidTuple");
