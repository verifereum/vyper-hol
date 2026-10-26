(* Pure input observations for a dynamic singleton whose child has a canonical
   prefix. The enclosing singleton's offset may be any source-valid value. *)
Theory abiValidSingletonPrefixInput
Ancestors
  abiValidSingletonArray abiValidSingletonSetup abiDecoderPrefixPre
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiCanonicalArrayLoad abiCanonicalLoad abiDecoderArrayInitReentry
  compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Definition abi_valid_singleton_prefix_pre_def:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    is_dynamic (vyper_to_abi_type env ty) /\
    valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
    dec (Tuple [vyper_to_abi_type env ty]) bs = ListV [av] /\
    abi_head_word bs <= LENGTH bs /\
    abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap s /\
    mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH (DROP (abi_head_word bs) bs) /\
    TAKE (LENGTH (enc (vyper_to_abi_type env ty) av)) (DROP (abi_head_word bs) bs) =
      enc (vyper_to_abi_type env ty) av /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var hi
End

Theorem abi_valid_singleton_dynamic_load:
  is_dynamic at /\ valid_enc (Tuple [at]) bs /\ dec (Tuple [at]) bs = ListV [av] /\
  abi_head_word bs <= LENGTH bs /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  32 <= LENGTH bs /\ abi_decode_load opc (n2w sb:bytes32) s = n2w (abi_head_word bs) /\
  sb + abi_head_word bs < dimword (:256) /\
  mem_bytes_at (sb + abi_head_word bs) (LENGTH (DROP (abi_head_word bs) bs))
    (abi_decode_source opc s) = DROP (abi_head_word bs) bs
Proof
  strip_tac >> drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (irule abi_decode_source_prefix_window >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes] >> conj_tac
  >- decide_tac >>
  mp_tac (Q.INST [`off` |-> `abi_head_word bs`,
    `n` |-> `LENGTH (DROP (abi_head_word bs) bs)`] abi_decode_source_window) >>
  simp[LENGTH_DROP]
QED

Theorem abi_valid_singleton_prefix_setup_pre:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap s ==>
  abi_valid_singleton_setup_pre st src dst opc hi sb d (abi_head_word bs)
    (abi_decoder_prune_vars st.cs_next_var s)
Proof
  simp_tac bool_ss [abi_valid_singleton_prefix_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_valid_singleton_dynamic_load >> strip_tac >>
  asm_simp_tac bool_ss [abi_valid_singleton_setup_pre_def, abi_decoder_prune_fresh,
    abi_decoder_prune_eval, abi_decoder_prune_load] >>
  Cases_on `hi = Lit 0w` >- simp[] >>
  qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `h` >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_SINGLETON_PREFIX_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid singleton prefix input not kernel closed: " ^ n)
  end) (DB.thms "abiValidSingletonPrefixInput");
