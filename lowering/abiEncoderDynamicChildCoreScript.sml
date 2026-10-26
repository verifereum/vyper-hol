(* Recursive core execution preserves the child's saved head/offset and parent cursor. *)
Theory abiEncoderDynamicChildCore
Ancestors
  abiEncoderCorrect abiDecoderEffect abiDecoderAllocation abiDecoderReentry abiDecoderContract
  abiDecoderLoop fragExec compileEnv valueEncoding venomState finite_map words list

Theorem abi_encoder_effect_operand:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
  eval_operand op t = SOME w
Proof
  simp_tac bool_ss [abi_decoder_effect_def] >> strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_encoder_dynamic_child_core:
  abi_encoder_correct ei /\ compile_abi_encode_to_buf dst src ei start = (out,end_st) /\
  fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre ei at av start src dst sb source_cap d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_decoder_operand_live start.cs_next_var head /\ abi_decoder_operand_live start.cs_next_var offset /\
  abi_decoder_operand_live start.cs_next_var dyn_ptr /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand offset initial = SOME (n2w off) /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\
  first <= site /\ site < last /\ site < start.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (LENGTH (enc at av)) b cap initial t /\
    eval_operand head t = SOME (n2w h) /\ eval_operand offset t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot initial /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_correct_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  mp_tac (Q.INST [`lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `LENGTH (enc at av)`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decoder_effect_protected_slot) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  imp_res_tac abi_encoder_effect_operand >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> fs[abi_decoder_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ENCODER_DYNAMIC_CHILD_CORE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI encoder dynamic child core not kernel closed: " ^ n)
  end) (DB.thms "abiEncoderDynamicChildCore");
