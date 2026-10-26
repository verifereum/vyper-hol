(* Execute the dynamic child's address setup inside its containing function. *)
Theory abiEncoderChildPrefixReach
Ancestors
  abiEncoderChildPrefix abiEncoderChildCode abiBuiltinPrefix abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec instIdxIndep compileEnv
  emitHelperProps venomExecSemantics venomState words list rich_list

Theorem abi_encode_child_prefix_from_state:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') /\
  eval_operand dst initial = SOME (n2w db) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (\t. eval_operand (FST ops) t = SOME (n2w (db+head_offset)) /\
      eval_operand (FST (SND ops)) t = SOME (n2w off) /\
      eval_operand (SND (SND ops)) t = SOME (n2w (db+off)) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t) (K F)
Proof
  strip_tac >> drule abi_encode_child_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st st' limit_st initial actual` >> qexists_tac `actual` >>
  gvs[abi_builtin_prefix_def, abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_child_prefix_reach:
  abi_encode_child_prefix dst head_offset dyn_ptr st = (ops,st') /\ fn_has_code st st' func /\
  eval_operand dst initial = SOME (n2w db) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (db+head_offset)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w off) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (db+off)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var initial t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_prefix_from_state >> disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `~actual.vs_halted` by fs[abi_decoder_address_frame_def] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CHILD_PREFIX_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder child prefix reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderChildPrefixReach");
