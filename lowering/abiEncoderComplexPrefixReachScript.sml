(* Parent cursor initialization reaches its actual endpoint in the containing CFG. *)
Theory abiEncoderComplexPrefixReach
Ancestors
  abiEncoderComplexPrefix abiEncoderComplexCode abiDecoderAllocation abiDecoderContract
  abiDecoderFrame abiDecoderReentry abiDecoderLoop fragExec instIdxIndep
  emitHelperProps compileEnv venomState words list rich_list arithmetic

Definition abi_encoder_complex_prefix_post_def:
  abi_encoder_complex_prefix_post (infos:(abi_enc_info # num # num # bool) list)
    dyn_ptr next site limit_st first last b cap initial actual <=>
    ?slot. eval_operand dyn_ptr actual = SOME (n2w slot) /\
      mload slot actual = n2w (SUM (MAP (\(_,asz,_,_). asz) infos)) /\
      b <= slot /\ slot+32 <= b+cap /\
      abi_decoder_budget first last b cap actual /\ fresh_vars_wrt limit_st actual /\
      (!op. abi_decoder_operand_live next op ==> eval_operand op actual = eval_operand op initial) /\
      abi_decode_frame slot 32 initial actual /\
      FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
      (!id. id <> site ==> FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      actual.vs_halted = initial.vs_halted
End

Theorem abi_encoder_complex_prefix_post_inst_idx[simp]:
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial
    (actual with vs_inst_idx := ix) <=>
  abi_encoder_complex_prefix_post infos dyn_ptr next site limit_st first last b cap initial actual
Proof
  simp[abi_encoder_complex_prefix_post_def, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_decode_frame_def, abi_decoder_budget_def, abi_decoder_missing_def, mload_def]
QED

Theorem abi_encoder_complex_prefix_from_state:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial) (K F)
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encoder_complex_prefix_sequence >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_encoder_complex_prefix_post_inst_idx] >>
  PURE_REWRITE_TAC [abi_encoder_complex_prefix_post_def] >> qexists_tac `slot` >>
  qpat_assum `dyn_ptr = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_prefix_reach:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\ fn_has_code st st' func /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_complex_prefix_post infos dyn_ptr st.cs_next_var st.cs_next_id
      limit_st first last b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_prefix_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_encoder_complex_prefix_post_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_COMPLEX_PREFIX_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder complex prefix reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderComplexPrefixReach");
