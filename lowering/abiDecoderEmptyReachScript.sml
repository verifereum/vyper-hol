(* TOP-LEVEL: execute an empty child at an inline head pointer, including
   repeated execution and continuation simulation of the actual code. *)
Theory abiDecoderEmptyReach
Ancestors
  abiDecoderEmpty abiDecoderComplexGuard abiDecoderReentry abiDecoderContract
  abiDecoderLoop abiEncoder compileEnv fragExec venomState venomExecSemantics words list

Theorem abi_decode_empty_complex_reentry:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] abi_decoder_complex_guard_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]
QED

Theorem abi_decode_empty_complex_reach:
  compile_abi_decode_to_buf dst src opc hi (DecComplex dynamic []) st = ((),st') /\
  fn_has_code st st' func /\ eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [abi_decode_empty_complex_phases] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`head_sz` |-> `0:num`] abi_decode_complex_head_guard_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_EMPTY_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI empty decoder execution fact not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderEmptyReach");
