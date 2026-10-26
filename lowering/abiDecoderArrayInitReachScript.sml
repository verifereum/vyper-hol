(* Package actual array initialization as an executable compiler fragment. *)
Theory abiDecoderArrayInitReach
Ancestors
  abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderAllocation
  abiDecoderContract abiDecoderFrame abiDecoderReentry fragExec instIdxIndep
  exprLoweringProps emitHelperProps compileEnv venomState words list arithmetic

Theorem abi_decoder_emitted_every_append:
  inst_extends st middle /\ inst_extends middle st' /\
  EVERY P (emitted_insts st middle) /\ EVERY P (emitted_insts middle st') ==>
  EVERY P (emitted_insts st st')
Proof
  strip_tac >>
  `emitted_insts st st' = emitted_insts st middle ++ emitted_insts middle st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >> simp[]
QED

Theorem abi_decode_array_loop_init_shape:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc ==>
  loop_st.cs_current_bb = st.cs_current_bb /\ loop_st.cs_blocks = st.cs_blocks /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  inst_extends st loop_st /\ st.cs_next_var <= loop_st.cs_next_var /\
  st.cs_next_id <= loop_st.cs_next_id /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st loop_st)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st header_st /\ inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st header_st)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `guard_st` >> fs[EVERY_CONJ]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st loop_st)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `header_st` >> simp[]) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- fs[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> decide_tac
QED

Definition abi_decoder_array_init_post_def:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial t <=>
    ?p. eval_operand (FST setup) t = SOME (n2w p) /\
      eval_operand (SND setup) t = SOME (n2w n) /\ mload p t = 0w /\
      mem_word_at d t.vs_memory = n2w n /\ b <= p /\ p + 32 <= b + cap /\
      abi_decoder_budget first last b cap t /\ fresh_vars_wrt limit_st t /\
      (!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op t = SOME w) /\
      abi_decode_footprint_frame [(d,32);(b,cap)] initial t /\
      abi_decode_footprint_frame [(d,32);(p,32)] initial t /\
      FLOOKUP t.vs_allocas site = SOME (p,32) /\
      (!id. id <> site ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      t.vs_halted = initial.vs_halted
End

Theorem abi_decoder_array_init_post_inst_idx[simp]:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial (t with vs_inst_idx := ix) <=>
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial t
Proof
  simp[abi_decoder_array_init_post_def, fresh_vars_wrt_def, eval_op_inst_idx,
       abi_decode_footprint_frame_def, abi_decoder_budget_def, abi_decoder_missing_def,
       mload_def]
QED

Theorem abi_decode_array_loop_init_from_state:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  (d + 32 <= b \/ b + cap <= d) /\ fresh_vars_wrt st initial ==>
  frag_exec ctx st loop_st (\s. s = initial)
    (abi_decoder_array_init_post setup st.cs_next_var loop_st (loop_st.cs_next_id - 2)
      first last b cap d n initial) (K F)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >>
  drule_all abi_decode_array_loop_init_sequence >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `p` >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_INIT_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI array initialization fragment not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayInitReach");
