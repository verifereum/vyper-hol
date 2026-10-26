(* Load the completed parent's cursor without changing the encoded bytes. *)
Theory abiEncoderComplexFinish
Ancestors
  abiEncoderLoadReach abiEncoderMembersBoundary abiEncoderMembersContract abiEncoderMembersDefs
  abiDecoderEffect abiDecoderDynamicLoopSetup abiDecoderProtectedScratch abiDecoderIndexInit
  abiDecoderAllocation abiDecoderContract fragExec emitHelperProps compileEnv valueEncoding
  contractABI venomState words list arithmetic pred_set

Theorem abi_encoder_complex_finish:
  abi_encoder_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\ fn_has_code st end_st func /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_members_final_output >> strip_tac >>
  qpat_assum `abi_encoder_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `slot < dimword (:256)` by decide_tac >>
  mp_tac (Q.INST [`src` |-> `dyn_ptr`, `p` |-> `n2w slot:bytes32`,
    `w` |-> `n2w (LENGTH (enc (Tuple tys) (ListV avs))):bytes32`, `st'` |-> `end_st`,
    `initial` |-> `encoded:venom_state`] abi_encoder_load_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w] >> strip_tac >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`s` |-> `encoded:venom_state`, `t` |-> `actual:venom_state`,
    `next` |-> `st.cs_next_var`, `child_next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`,
    `sz` |-> `output_size:num`] abi_decoder_address_effect) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex finish not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexFinish");
