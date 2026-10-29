(* Invoke the shared encoder on an encoding-equivalent typed source window. *)
Theory abiEncoderSourceInvoke
Ancestors
  abiEncoderSourceProducer abiEncoderSharedRecursive abiEncoderEntry
  abiEncoderExitPhi abiEncoderAdmissible abiEncoderSharedContract
  abiEncoderSourceBridge
  abiEncoderResourceAdapter abiEncoderProps abiDecoderReentry words list

Theorem abi_encoder_source_shared_input:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  enc_pre st st' [dst;src] lo top tv v (w2n sw)
    [(w2n dw,LENGTH (enc (vyper_to_abi_type env ty) av))] s /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_shared_input (ei,ct,rv) (st,src,dst)
      (w2n sw,type_memory_size tv) (w2n dw,LENGTH (enc ct rv))
      (st.cs_next_id,st'.cs_next_id,lo,top-lo) s
Proof
  rpt strip_tac >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by fs[enc_pre_def] >>
  drule_all abi_encoder_source_window >> strip_tac >>
  qexistsl_tac [`ct`,`rv`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [abi_encoder_shared_input_def] >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    (conj_tac >> irule abi_encoder_pre_operand_live >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule abi_encoder_pre_memory_bounds >> strip_tac >>
  `enc_scratch (frag_ids st st') lo top s /\
   w2n sw + type_memory_size tv <= lo /\
   w2n dw + LENGTH (enc (vyper_to_abi_type env ty) av) <= lo` by
    fs[enc_pre_def] >>
  `abi_footprint_disjoint (w2n sw) (type_memory_size tv)
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id)
        lo (top-lo) s)` by (irule abi_encoder_scratch_footprint >> simp[]) >>
  `abi_footprint_disjoint (w2n dw) (LENGTH (enc ct rv))
      (abi_decoder_child_scratch (abi_decoder_ids st.cs_next_id st'.cs_next_id)
        lo (top-lo) s)` by (irule abi_encoder_scratch_footprint >> simp[]) >>
  gvs[enc_pre_def]
QED

Theorem abi_encoder_source_shared_run:
  compile_abi_encode_to_buf dst src ei st = (out,st') /\
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
  enc_pre st st' [dst;src] lo top tv v (w2n sw)
    [(w2n dw,LENGTH (enc (vyper_to_abi_type env ty) av))] s /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ct rv actual. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_shared_endpoint (ctx,func) (st,st',out,st')
      (st.cs_next_id,st'.cs_next_id,lo,top-lo) (ct,rv,w2n dw)
      (abi_decoder_prune_vars st.cs_next_var s) actual
Proof
  rpt strip_tac >>
  drule_all abi_encoder_pruned_entry >> strip_tac >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_shared_input (ei,ct,rv) (st,src,dst)
      (w2n sw,type_memory_size tv) (w2n dw,LENGTH (enc ct rv))
      (st.cs_next_id,st'.cs_next_id,lo,top-lo)
      (abi_decoder_prune_vars st.cs_next_var s)` by
    (irule abi_encoder_source_shared_input >> metis_tac[]) >>
  `abi_encoder_shared ei` by
    (irule abi_encoder_shared_admissible >> irule (cj 1 abi_enc_plan_admissible) >>
     goal_assum (drule_at Any)) >>
  `st.cs_blocks = st'.cs_blocks \/
    (!bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0)` by
    (drule_all abi_encoder_core_containing_exit_phi >> simp[]) >>
  `?actual. abi_encoder_shared_endpoint (ctx,func) (st,st',out,st')
      (st.cs_next_id,st'.cs_next_id,lo,top-lo) (ct,rv,w2n dw)
      (abi_decoder_prune_vars st.cs_next_var s) actual` by
    (irule abi_encoder_shared_run >>
     gvs[abi_decoder_prune_vars_def] >> metis_tac[]) >>
  metis_tac[]
QED

val _ = List.app (fn th =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms andalso null (Thm.hyp th)
    then () else raise Fail "source invocation admission, axiom or hypothesis"
  end) [abi_encoder_source_shared_input, abi_encoder_source_shared_run];
