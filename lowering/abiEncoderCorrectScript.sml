(* Recursive encoder contract: pure incoming data and allocator resources.
   Constructor correctness is proved separately; this definition is not a proof. *)
Theory abiEncoderCorrect
Ancestors
  abiEncoderInput abiDecoderCorrectWord abiDecoderEffect abiDecoderAllocation abiDecoderLoop
  abiDecoderReentry abiDecoderContract abiEncoder compileEnv valueEncoding fragExec
  venomState venomExecSemantics words list arithmetic

Definition abi_encoder_pre_def:
  abi_encoder_pre ei at av st src dst sb source_cap d b cap s <=>
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+source_cap < dimword (:256) /\ d+LENGTH (enc at av) < dimword (:256) /\
    (sb+source_cap <= d \/ d+LENGTH (enc at av) <= sb) /\
    (sb+source_cap <= b \/ b+cap <= sb) /\
    (d+LENGTH (enc at av) <= b \/ b+cap <= d)
End

Definition abi_encoder_correct_def:
  abi_encoder_correct ei <=>
    !dst src start end_st out func ctx first last b cap limit_st initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
    fn_has_code start end_st func /\
    (start.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
    abi_decoder_budget first last b cap initial /\
    first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
    end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
    initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
    ?t. mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
      eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
      abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
        limit_st d (LENGTH (enc at av)) b cap initial t /\
      t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
      ~t.vs_halted /\ abi_decode_sim ctx func initial t
End

Theorem abi_encoder_correct_run:
  abi_encoder_correct ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  strip_tac >> qpat_x_assum `abi_encoder_correct _` (mp_tac o PURE_REWRITE_RULE [abi_encoder_correct_def]) >>
  disch_then (qspecl_then [`dst`, `src`, `start`, `end_st`, `out`, `func`, `ctx`, `first`, `last`,
    `b`, `cap`, `limit_st`, `initial`, `at`, `av`, `sb`, `source_cap`, `d`] mp_tac) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder correctness contract not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderCorrect");
