(* Actual singleton prefix execution establishes the recursive child's input. *)
Theory abiValidSingletonPrefixEntry
Ancestors
  abiValidSingletonPrefixInput abiValidSingletonPrefixReady abiValidSingletonReentry
  abiValidSingletonCode abiDecoderSingletonSetup abiDecoderArrayBody
  abiDecoderDynamicLoopSetup abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiDecoderAllocation abiDecoderArrayInitExec abiDecoderReentry abiDecoderLoop
  abiEncoder fragExec compileEnv valueEncoding vyperABI contractABI
  venomState venomExecSemantics words list pair arithmetic

Theorem abi_valid_singleton_prefix_entry:
  abi_decode_singleton_setup dst src opc hi st = ((childsrc,childdst),ready) /\
  fn_has_code st ready func /\
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
      ready last childsrc childdst opc hi (sb + abi_head_word bs) d b cap
      (abi_decoder_prune_vars ready.cs_next_var prepared) /\
    abi_decoder_budget first last b cap prepared /\ first <= ready.cs_next_id /\
    fresh_vars_wrt limit_st prepared /\
    abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by
    fs[abi_valid_singleton_prefix_pre_def, abi_decoder_ranges_def,
       Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  drule abi_valid_singleton_setup_live >> simp_tac bool_ss [FST, SND] >> strip_tac >>
  `first <= ready.cs_next_id` by decide_tac >>
  `abi_decoder_reservation ready.cs_next_id last b cap initial` by
    (drule_all abi_decoder_budget_child_reservation >> simp[]) >>
  drule_all abi_valid_singleton_prefix_setup_pre >> strip_tac >>
  drule_all abi_valid_singleton_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_valid_singleton_prefix_child_pre >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (qpat_assum `abi_decoder_address_frame _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
     drule_all abi_decoder_budget_transport >> simp[]) >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_SINGLETON_PREFIX_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid singleton prefix entry not kernel closed: " ^ n)
  end) (DB.thms "abiValidSingletonPrefixEntry");
