(* Recursive dynamic-array correctness, including both bulk and loop branches. *)
Theory abiDecoderCorrectArray
Ancestors
  abiDecoderCorrect abiDecoderRecursiveArrayExecute abiDecoderCorrectPrimitiveArray abiDecoderRecursiveArrayCode
  abiDecoderBulkReentry abiDecoderEffect abiDecoderAllocation abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderContract
  exprLowering compileEnv valueEncoding vyperABI vyperValue venomState words list

Theorem abi_decoder_correct_array:
  abi_decoder_correct ce env sf ty tv ==>
  abi_decoder_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_decoder_recursive_pre_def, abi_decoder_pre_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gvs[Excl "enc_def"] >>
  (`type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn`
    by simp[Once type_to_abi_dec_info_def] >>
  gvs[Excl "enc_def"] >>
  ASM_CASES_TAC ``is_abi_dynamic ce.ce_struct_fields ty \/
    dec_info_needs_clamp (type_to_abi_dec_info
      (sf:string |-> (string # vyperAST$type # num) list) ce ty)``
  >- (`abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
      drule_all abi_decoder_recursive_array_adds_blocks >> strip_tac >>
      `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
      drule_all abi_decoder_recursive_array_execute >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  gvs[Excl "enc_def"] >>
  drule_all abi_decoder_bulk_reentry_protected >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  gvs[abi_decoder_effect_def, abi_decoder_scratch_frame_def, abi_decoder_ids_def,
    Excl "enc_def"] >> metis_tac[])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CORRECT_ARRAY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array correctness not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCorrectArray");
