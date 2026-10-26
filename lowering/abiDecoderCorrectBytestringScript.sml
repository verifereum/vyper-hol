(* Bytes and String satisfy the recursive decoder contract without allocation. *)
Theory abiDecoderCorrectBytestring
Ancestors
  abiDecoderCorrect abiDecoderCorrectWord abiDecoderReentryBytestring
  abiDecoderEffect abiDecoderProtectedScratch abiDecoderCoherence abiDecoderTypedContract
  abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec compileEnv emitHelperProps valueEncoding venomState words list

Theorem abi_decoder_correct_bytestring:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==> abi_decoder_correct ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[Excl "enc_def"] >>
  (qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_output_separated >> disch_then assume_tac >>
  drule_all abi_decoder_bytestring_reentry_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `start.cs_next_var`,
    `sz` |-> `type_memory_bytes ce ty`] abi_decoder_scratch_free_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CORRECT_BYTESTRING_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI bytestring recursive correctness not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCorrectBytestring");
