(* Actual final stores preserve the recursively encoded tail and update its head/cursor. *)
Theory abiEncoderDynamicChildFinish
Ancestors
  abiEncoderChildSuffixReach abiEncoderChildEffect abiEncoderChildCode abiDecoderEffect
  abiDecoderProtectedScratch abiDecoderAllocation abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec compileEnv venomExecSemantics venomState finite_map pred_set
  words list arithmetic

Theorem abi_encoder_dynamic_child_finish:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\ fn_has_code st st' func /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  mem_bytes_at (d+off) len initial.vs_memory = bytes /\
  d <= h /\ h+32 <= d+off /\ off+len <= output_size /\
  d+output_size < dimword (:256) /\ (d+output_size <= b \/ b+cap <= d) /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < last /\
  lo <= site /\ site < hi /\ FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. mem_bytes_at (d+off) len t.vs_memory = bytes /\
    mem_word_at h t.vs_memory = n2w off /\ mem_word_at slot t.vs_memory = n2w (off+len) /\
    eval_operand out t = SOME (n2w len) /\
    abi_decode_footprint_frame [(h,32);(slot,32)] initial t /\
    FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  `h < dimword (:256) /\ slot < dimword (:256) /\ h+32 <= d+output_size` by decide_tac >>
  mp_tac (Q.INST [`p` |-> `slot:num`] abi_encode_child_suffix_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`q` |-> `d+off`, `offset` |-> `off:num`] abi_encoder_child_suffix_output) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  mp_tac (Q.INST [`sz` |-> `output_size:num`, `off` |-> `off:num`]
    abi_encoder_child_suffix_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_encoder_child_suffix_post_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_DYNAMIC_CHILD_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic child finish not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderDynamicChildFinish");
