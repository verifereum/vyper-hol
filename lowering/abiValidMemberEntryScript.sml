(* Actual emitted member setup establishes typed, source-valid child inputs.
   Dynamic zero-length fixed arrays are explicit; their offsets are not bounded
   by validity alone. Recursive child execution is proved separately. *)
Theory abiValidMemberEntry
Ancestors
  abiValidMemberWindows abiValidMembers abiValidDecodedMetadata
  abiDecoderMemberSetup abiDecoderMemberCode abiDecoderDynamic abiDecoderCoherence
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderArrayChildSource
  abiDecoderTypedContract abiDecoderContract abiDecoderReentry abiDecodeRanges
  abiEncoder compileEnv valueEncoding vyperABI contractABI fragExec
  venomState venomExecSemantics emitHelperProps words list arithmetic

Theorem abi_valid_member_child_ranges:
  abi_decoder_ranges opc hi src dst sb len d outsz b cap before /\
  abi_decoder_address_frame next before after /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\
  off + childlen <= len /\ vo + childsz <= outsz /\
  eval_operand childsrc after = SOME (n2w (sb + off)) /\
  eval_operand childdst after = SOME (n2w (d + vo)) ==>
  abi_decoder_ranges opc hi childsrc childdst (sb + off) childlen (d + vo) childsz b cap after
Proof
  strip_tac >> drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  irule abi_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `len`, `outsz`, `sb`, `src`] >>
  asm_simp_tac arith_ss [] >> decide_tac
QED

Theorem abi_valid_member_entry:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. valid_enc at childbs /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec at childbs) v /\
    abi_decoder_ranges opc hi (FST ops) (SND ops) (sb + off) (LENGTH childbs)
      (d + vo) (type_memory_bytes ce ty) b cap prepared /\
    mem_bytes_at (sb + off) (LENGTH childbs) (abi_decode_source opc prepared) = childbs /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  SUBGOAL_THEN ``is_dynamic (vyper_to_abi_type env ty) ==>
    abi_decode_load opc (n2w (sb + SUM (MAP abi_member_head_size pre)):bytes32) initial =
      n2w (abi_decode_member_offset (vyper_to_abi_type env ty) bs
        (SUM (MAP abi_member_head_size pre))) /\
    sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre)) < dimword (:256)`` assume_tac
  >- (strip_tac >> asm_simp_tac bool_ss []) >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`ao` |-> `SUM (MAP abi_member_head_size pre)`,
    `dyn` |-> `is_dynamic (vyper_to_abi_type env ty)`, `st'` |-> `ready`,
    `payload_off` |-> `abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))`] abi_decode_member_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb +
     abi_decode_member_offset (vyper_to_abi_type env ty) bs (SUM (MAP abi_member_head_size pre))))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[abi_decode_member_offset_def, Excl "valid_enc_def", Excl "dec_def", Excl "enc_def"]) >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  drule_all abi_valid_member_child_ranges >> strip_tac >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_MEMBER_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid member entry not kernel closed: " ^ n)
  end) (DB.thms "abiValidMemberEntry");
