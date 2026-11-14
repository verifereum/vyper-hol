(* Exact successful arbitrary-calldata word decoder execution. *)
Theory defaultWordDecodeExec
Ancestors
  calldataExact calldataWordLive calldataSourceWord abiDecoderWordOutcome
  calldataRegistration calldataSourceCorrespondence calldataReconstruction calldataWordLeaf
  abiDecoderCoherence abiDecoderContract abiDecoderClamp exprLoweringProps
  fragExecMem vyperValue vyperCalldata valueEncodingTyping
  venomState venomExecSemantics compileEnv words list arithmetic

Theorem default_word_decode_exact_sequence:
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  compile_abi_decode_to_buf (Var dstvar) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) sa = ((),sb) /\
  cd_decode F s.vs_call_ctx.cc_calldata tv (w2n sw) = SOME x /\
  eval_operand src s = SOME sw /\ eval_operand (Var dstvar) s = SOME (n2w d) /\
  abi_decoder_operand_live sa.cs_next_var src /\
  abi_decoder_operand_live sa.cs_next_var (Var dstvar) /\
  d+32 <= s.vs_alloca_next /\ d+32 < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    val_in_memory tv x d t.vs_memory /\ value_has_type tv x /\ val_wf tv x /\
    abi_decode_frame d 32 s t /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|> /\
    inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp` by
    metis_tac[word_type_decoder_primitive] >>
  drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `!cd pos. cd_decode F cd tv pos = cd_word_value tv (cd_word cd pos)` by
    (qpat_x_assum `evaluate_type env ty = SOME tv` mp_tac >>
     qpat_x_assum `is_word_type ty` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `ty` >> simp[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[is_word_type_def, cd_decode_def]) >>
  `cd_word_value tv (abi_decode_load CALLDATALOAD sw s) = SOME x` by
    metis_tac[calldata_decode_load_word] >>
  `abi_clamp_ok clamp (abi_decode_load CALLDATALOAD sw s)` by
    metis_tac[calldata_coherent_word_accepts, optionTheory.NOT_SOME_NONE] >>
  `value_has_type tv x /\ typed_val_to_w256 tv x = abi_decode_load CALLDATALOAD sw s` by
    metis_tac[calldata_coherent_word_value] >>
  `d < dimword (:256)` by decide_tac >>
  `val_wf tv x` by metis_tac[value_has_type_val_wf] >>
  `compile_abi_decode_to_buf (Var dstvar) src CALLDATALOAD (Lit 0w) (Lit 0w)
     (DecPrimWord clamp) sa = ((),sb)` by metis_tac[] >>
  drule_all calldata_word_accepted_live >> strip_tac >>
  `val_in_memory tv x d t.vs_memory` by
    (irule calldata_word_representation >> simp[] >> metis_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_opcodes >> strip_tac >>
  drule_all abi_word_sequence_static >> strip_tac >>
  drule_all calldata_word_opcodes >> strip_tac >>
  mp_tac (calldata_word_prefix_live |> Q.INST
    [`dst` |-> `Var dstvar`, `p` |-> `sw`, `st` |-> `sa`, `last` |-> `sb`]) >>
  (impl_tac >- simp[]) >> disch_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (match_mp_tac run_inst_seq_mem_ok_of_prefix_safe >> simp[] >>
     gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >- metis_tac[abi_decoder_word_inst_extends] >>
  conj_tac >- metis_tac[abiDecoderClampedWordTheory.abi_decoder_clamped_word_shape] >>
  gvs[listTheory.EVERY_MEM, abi_word_opcode_def] >> rpt strip_tac >>
  qpat_x_assum `!i. MEM i _ ==> _ \/ _` (qspec_then `i` mp_tac) >> simp[]
QED
