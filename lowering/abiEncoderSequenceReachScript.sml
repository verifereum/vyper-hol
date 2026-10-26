(* Lift a proved straight-line execution to its exact containing-function endpoint. *)
Theory abiEncoderSequenceReach
Ancestors
  abiBuiltinPrefix abiDecoderLoop abiDecoderDynamicLoopSetup abiDecoderReentryAddress
  abiDecoderReentry abiDecoderContract fragExec instIdxIndep compileEnv
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst words list rich_list

Theorem abi_encoder_run_sequence_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = OK encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> qexists_tac `encoded` >> simp[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem abi_builtin_emit_mul:
  emit_op MUL [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME (a*b) /\ abi_builtin_prefix st st' limit_st s t
Proof
  strip_tac >> drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] abi_decoder_binary_reentry)) >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a*b) s` >>
  fs[abi_builtin_prefix_def, abi_decoder_address_frame_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_SEQUENCE_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder sequence reach not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderSequenceReach");
