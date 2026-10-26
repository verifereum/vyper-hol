(* Actual source validity supplies the emitted aggregate head-window guard. *)
Theory abiScratchDecoderComplexInputs
Ancestors
  abiScratchDecoderContract
  abiDecoderMemberInfos abiDecoderMembers abiValidMembers abiDecodeRanges
  abiDecoderTypedContract abiDecoderContract abiEncoder compileEnv valueEncoding
  vyperABI contractABI venomState words list arithmetic

Theorem abi_scratch_decoder_complex_guard_inputs:
  abi_decoder_members ce env sf tys tvs avs vs /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_scratch_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (SUM (MAP (type_memory_bytes ce) tys)) first last b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= hb /\
    hb < dimword (:256))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_members_relations >> strip_tac >>
  drule abi_decoder_member_infos_layout >> strip_tac >>
  drule abi_valid_members_view >> strip_tac >>
  `FOLDR (\(_,asz,_) acc. asz + acc) 0 (abi_decoder_member_infos sf ce tys) <= LENGTH bs`
    by (asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  asm_simp_tac bool_ss [] >> Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `eval_operand hi initial = SOME (n2w hb)` >>
  qexists_tac `hb` >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_COMPLEX_INPUTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical aggregate guard inputs not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderComplexInputs");

