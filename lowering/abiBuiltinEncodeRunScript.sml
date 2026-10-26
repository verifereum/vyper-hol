(* Complete actual lower_abi_encode for either optional method-ID choice. *)
Theory abiBuiltinEncodeRun
Ancestors
  abiBuiltinEncodeMethodCorrect abiBuiltinEncodeCorrect abiBuiltinEncodeInput
  abiBuiltinEncodeMethodReach abiBuiltinEncodeEffect abiDecoderEffect abiDecoderFrame
  abiDecoderContract abiDecoderLoop fragExec builtinAbi exprLowering compileEnv valueEncoding
  venomState venomExecSemantics words list arithmetic

Definition abi_builtin_encode_prefix_def:
  abi_builtin_encode_prefix NONE = [] /\
  abi_builtin_encode_prefix (SOME mid) = abi_builtin_encode_method_bytes mid
End

Theorem abi_builtin_encode_effect_no_method:
  fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  abi_decode_footprint_frame [(p,outsz);(b,cap)] s t /\ t.vs_halted = s.vs_halted /\
  (!id. id < st.cs_next_id \/ final.cs_next_id <= id ==>
    FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) ==>
  abi_builtin_encode_effect first last st final limit_st p outsz 0 b cap s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_body_footprint >> disch_then (qspec_then `0` assume_tac) >>
  asm_simp_tac bool_ss [abi_builtin_encode_effect_def] >> first_assum ACCEPT_TAC
QED

Theorem lower_abi_encode_run:
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av start method_id_opt src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)))))
      (vyperValue$BytesV (abi_builtin_encode_prefix method_id_opt ++ enc at av)) p actual.vs_memory /\
    abi_builtin_encode_effect first last start final limit_st p
      (maxlen+32+LENGTH (abi_builtin_encode_prefix method_id_opt))
      (case method_id_opt of NONE => 0 | SOME _ => 32) b cap initial actual /\
    FLOOKUP actual.vs_allocas start.cs_next_id =
      SOME (p,maxlen+32+LENGTH (abi_builtin_encode_prefix method_id_opt)) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `method_id_opt` >>
  simp_tac (srw_ss()) [abi_builtin_encode_prefix_def, abi_builtin_encode_method_bytes_length,
    abi_builtin_encode_pre_none, GSYM ADD_ASSOC, ADD_COMM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (drule_all lower_abi_encode_no_method >> disch_then (qspec_then `ctx` strip_assume_tac) >>
      rename1 `abi_decode_sim ctx func initial actual` >>
      `actual.vs_halted = initial.vs_halted` by simp[] >>
      `abi_builtin_encode_effect first last start final limit_st p (maxlen+32) 0 b cap initial actual` by
        (drule_all abi_builtin_encode_effect_no_method >> simp[]) >>
      qexists_tac `actual` >> asm_simp_tac (srw_ss()) [ADD_COMM]) >>
  drule_all lower_abi_encode_method >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [ADD_COMM] >>
  first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ADD_COMM])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder run not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeRun");
