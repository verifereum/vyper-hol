(* The emitted heterogeneous member prefix establishes the child's physical input. *)
Theory abiScratchDecoderMemberEntry
Ancestors
  abiScratchDecoderContract abiScratchDecoderRanges abiScratchDecoderSubwindow
  abiScratchDecoderTransport abiScratchAddressEffect abiScratchEncoderContract
  abiDecoderValidMemberInput abiValidMemberWindows abiValidMembers abiDecoderValidContract
  abiDecoderMemberSetup abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecodeRanges abiEncoder
  fragExec compileEnv valueEncoding vyperABI contractABI venomState words list arithmetic

Theorem abi_scratch_decoder_member_entry:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi
    (abi_decoder_dynamic (type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_scratch_decoder_input ce env sf ty tv childbs v ready
      (FST ops) (SND ops) opc hi (sb + off) (d + vo) first last b cap prepared /\
    abi_scratch_effect first last st.cs_next_id ready.cs_next_id st.cs_next_var
      limit_st d outsz b cap initial prepared /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_ranges_point >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST
    [`b` |-> `initial.vs_alloca_next`, `cap` |-> `0:num`] abi_decoder_valid_member_entry)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `sb + LENGTH bs < dimword (:256)` by
    (qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
     asm_simp_tac bool_ss []) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_member_window) >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_x_assum `abi_decoder_valid_pre`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_assum `abi_decoder_ranges opc hi (FST ops) (SND ops) _ _ _ _ _ _ prepared`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  `abi_scratch_effect first last st.cs_next_id ready.cs_next_id st.cs_next_var
    limit_st d outsz b cap initial prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `lo` |-> `st.cs_next_id`,
      `hi` |-> `ready.cs_next_id`, `sz` |-> `outsz:num`, `actual` |-> `prepared:venom_state`]
      abi_scratch_address_effect) >> asm_simp_tac bool_ss []) >>
  `abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap prepared` by
    (mp_tac (Q.INST [`hi_op` |-> `hi:operand`, `lo` |-> `st.cs_next_id`,
      `hi_id` |-> `ready.cs_next_id`, `next` |-> `st.cs_next_var`,
      `len` |-> `LENGTH (bs:word8 list)`, `sz` |-> `outsz:num`,
      `actual` |-> `prepared:venom_state`]
      abi_scratch_decoder_ranges_effect) >> asm_simp_tac bool_ss []) >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  irule abi_scratch_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`, `outsz`, `sb`, `src`] >>
  asm_simp_tac arith_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_MEMBER_ENTRY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical member prefix not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderMemberEntry");
