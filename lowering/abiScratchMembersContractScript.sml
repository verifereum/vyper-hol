(* Recursive execution interface for actual complex member lists.
   TOP-LEVEL: abi_scratch_members_correct, its empty case and application rule.
   The contract requires child encoder induction hypotheses and pure resources. *)
Theory abiScratchMembersContract
Ancestors
  abiScratchMembersState abiScratchMembersPre abiScratchEncoderContract
  abiScratchAddressEffect abiEncoderMembersContract abiEncoderInput abiEncoder
  abiDecoderDynamicLoopSetup abiDecoderLoop abiDecoderReentry abiDecoderContract
  compileEnv valueEncoding contractABI venomState words list arithmetic

Definition abi_scratch_members_correct_def:
  abi_scratch_members_correct infos <=>
    !tys avs pre pvs active dyn_ptr site slot first last lo st end_st limit_st src dst sb so ho d hl
      output_size b cap initial out func ctx.
    EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
    compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
    fn_has_code st end_st func /\
    (st.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_scratch_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
      src dst sb so ho d hl output_size b cap initial /\
    end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
    ?t. abi_scratch_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
        end_st limit_st src dst sb (so+abi_encoder_member_span infos)
        (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
      abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
        limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
End

Theorem abi_scratch_members_correct_empty:
  abi_scratch_members_correct []
Proof
  simp_tac bool_ss [abi_scratch_members_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_members_empty_types >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >>
  gvs[Excl "enc_def"] >>
  `abi_decoder_address_frame end_st.cs_next_var initial initial` by simp[abi_decoder_address_frame_def] >>
  `abi_scratch_effect first last lo end_st.cs_next_id end_st.cs_next_var
    limit_st d output_size b cap initial initial` by
    (drule_all abi_scratch_address_effect >> simp[]) >>
  qexists_tac `initial` >>
  asm_simp_tac (srw_ss()) [abi_encoder_member_span_def, abi_decode_sim_refl]
QED

Theorem abi_scratch_members_run:
  abi_scratch_members_correct infos /\ EVERY (\(ei,_,_,_). abi_scratch_encoder ei) infos /\
  compile_abi_encode_complex_elems dst src infos so ho dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_members_inv infos tys avs pre pvs active dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap initial /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. abi_scratch_members_inv [] [] [] (pre++tys) (pvs++avs) active dyn_ptr site slot first last lo
      end_st limit_st src dst sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,abi_sz,_,_). abi_sz) infos)) d hl output_size b cap t /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `abi_scratch_members_correct _`
    (mp_tac o PURE_REWRITE_RULE [abi_scratch_members_correct_def]) >>
  disch_then (qspecl_then [`tys`, `avs`, `pre`, `pvs`, `active`, `dyn_ptr`, `site`, `slot`,
    `first`, `last`, `lo`, `st`, `end_st`, `limit_st`, `src`, `dst`, `sb`, `so`, `ho`, `d`, `hl`,
    `output_size`, `b`, `cap`, `initial`, `out`, `func`, `ctx`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_MEMBERS_CONTRACT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch recursive members interface not kernel closed: " ^ n)
  end) (DB.thms "abiScratchMembersContract");
