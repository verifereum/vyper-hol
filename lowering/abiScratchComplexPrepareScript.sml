(* Establish the complex member invariant using the real cursor initializer.
   TOP-LEVEL: abi_scratch_complex_prepare derives the registered head-length
   cursor while preserving complete source data and physical root separation. *)
Theory abiScratchComplexPrepare
Ancestors
  abiScratchMembersBoundary abiScratchMembersState abiScratchMembersPre
  abiScratchOwnedPrefix abiScratchPrefixEffect abiScratchEncoderContract
  abiEncoderComplexPrefix abiEncoderComplexLayout abiEncoderMembersDefs abiEncoderInput
  abiDecoderAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop
  compileEnv valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_complex_prepare:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot.
    abi_scratch_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_scratch_owned_prefix_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  mp_tac (Q.INST [`site` |-> `st.cs_next_id`, `stop` |-> `prepared.cs_next_id`,
    `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_scratch_prefix_effect) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `prepared.cs_next_id`,
    `so` |-> `0:num`, `sz` |-> `output_size:num`, `actual` |-> `ready:venom_state`]
    abi_scratch_members_pre_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`prepared` |-> `prepared:compile_state`, `s` |-> `ready:venom_state`,
    `so` |-> `0:num`, `sz` |-> `output_size:num`] abi_scratch_members_pre_mono) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  `fresh_vars_wrt limit_st ready /\ abi_decoder_budget first last b cap ready` by
    fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `st.cs_next_id`, `lo` |-> `st.cs_next_id`,
    `st` |-> `prepared`, `initial` |-> `ready:venom_state`, `hl` |-> `head_lengths tys 0`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- (gvs[Excl "enc_def"] >> decide_tac) >> disch_tac >>
  qexistsl_tac [`ready`, `slot`] >> full_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_COMPLEX_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complex initialization not kernel closed: " ^ n)
  end) (DB.thms "abiScratchComplexPrepare");
