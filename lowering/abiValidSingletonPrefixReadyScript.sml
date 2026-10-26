(* Transport an arbitrary singleton child window through its emitted prefix. *)
Theory abiValidSingletonPrefixReady
Ancestors
  abiValidSingletonPrefixInput abiDecoderPrefixPre abiDecoderArrayChildSource
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiCanonicalArrayLoad abiCanonicalLoad compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_decoder_suffix_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap s /\ offset <= len /\
  eval_operand childsrc s = SOME (n2w (sb + offset)) /\
  eval_operand childdst s = SOME (n2w d) ==>
  abi_decoder_ranges opc hi childsrc childdst (sb + offset) (len - offset)
    d outsz b cap s
Proof
  strip_tac >> irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `len`, `outsz`, `sb`, `src`] >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED

Theorem abi_valid_singleton_prefix_child_pre:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap before /\
  abi_decoder_address_frame st.cs_next_var before after /\
  st.cs_next_var <= ready.cs_next_var /\
  abi_decoder_reservation ready.cs_next_id last b cap before /\
  abi_decoder_operand_live ready.cs_next_var childsrc /\
  abi_decoder_operand_live ready.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_head_word bs)) /\
  eval_operand childdst after = SOME (n2w d) ==>
  abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
    ready last childsrc childdst opc hi (sb + abi_head_word bs) d b cap
    (abi_decoder_prune_vars ready.cs_next_var after)
Proof
  simp_tac bool_ss [abi_valid_singleton_prefix_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_decoder_ranges_def] >>
  drule_all abi_valid_singleton_dynamic_load >> strip_tac >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_reservation >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
     (abi_decode_source opc after) = DROP (abi_head_word bs) bs` by
    asm_simp_tac bool_ss [] >>
  `abi_decoder_ranges opc hi childsrc childdst (sb + abi_head_word bs)
     (LENGTH (DROP (abi_head_word bs) bs)) d (type_memory_bytes ce ty) b cap after` by
    (simp_tac bool_ss [LENGTH_DROP] >> irule abi_decoder_suffix_ranges >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dst`, `src`] >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     asm_simp_tac bool_ss []) >>
  drule_all abi_decoder_recursive_pre_from_prefix >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_SINGLETON_PREFIX_READY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid singleton child input not kernel closed: " ^ n)
  end) (DB.thms "abiValidSingletonPrefixReady");
