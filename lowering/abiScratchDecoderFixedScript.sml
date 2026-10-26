(* Actual-source fixed arrays execute the shared member decoder and recover sparse values. *)
Theory abiScratchDecoderFixed
Ancestors
  abiScratchDecoderContract abiScratchDecoderLeaves
  abiDecoderValidContract abiScratchDecoderFixedInputs abiDecoderFixedMemory abiScratchDecoderComplexExecute
  abiDecoderMemberInfos abiDecoderEffect abiDecoderCoherence abiDecoderReentry
  abiDecoderTypedContract abiDecoderContract fragExec compileEnv valueEncoding
  vyperABI vyperValue venomState words list rich_list

Theorem abi_scratch_decoder_fixed_array:
  abi_scratch_decoder ce env sf ty tv /\
  (0 < n /\ is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_decoder_fixed_array_inputs >> strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  (`LIST_REL (abi_scratch_decoder ce env sf) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)`
    by simp[LIST_REL_REPLICATE_same] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
  mp_tac (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
    (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `tys` |-> `REPLICATE (LENGTH vs) ty`,
      `tvs` |-> `REPLICATE (LENGTH vs) tv`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
      abi_scratch_decoder_complex_execute)) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_MEM, MEM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
    Cases_on `vs` >> gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]) >> strip_tac >>
  rename1 `tuple_in_memory vs (REPLICATE (LENGTH vs) tv) d actual.vs_memory` >>
  `val_in_memory (ArrayTV tv (Fixed (LENGTH vs)))
    (ArrayV (SArrayV (enumerate_static_array (default_value tv) 0 vs))) d actual.vs_memory`
    by (irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_FIXED_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical fixed-array correctness not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderFixed");

