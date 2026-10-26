(* Complete lower_abi_encode with a method ID, from pure input/resources. *)
Theory abiBuiltinEncodeMethodCorrect
Ancestors
  abiBuiltinEncodeInput abiBuiltinEncodeMethodSetup abiBuiltinEncodeMethodValue
  abiBuiltinEncodeMethodReach abiBuiltinEncodeEffect abiBuiltinEncodeSetupFrame abiBuiltinEncodeOwnership
  abiBuiltinEncodeBody abiBuiltinEncodeContext abiBuiltinEncodeCode
  abiEncoderCorrect abiEncoderInput abiDecoderEffect abiDecoderAllocation abiDecoderContract
  abiDecoderLoop fragExec builtinAbi exprLowering compileEnv valueEncoding
  venomState venomExecSemantics words list arithmetic

Theorem lower_abi_encode_method:
  lower_abi_encode ensure (SOME mid) src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av start (SOME mid) src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+4) /\
    mem_bytes_at (p+32) (4+LENGTH (enc at av)) actual.vs_memory =
      abi_builtin_encode_method_bytes mid ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+4))))
      (vyperValue$BytesV (abi_builtin_encode_method_bytes mid ++ enc at av)) p actual.vs_memory /\
    abi_builtin_encode_effect first last start final limit_st p (maxlen+36) 32 b cap initial actual /\
    FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+36) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_builtin_encode_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss())
      [abi_builtin_encode_pre_def, LET_THM, GSYM ADD_ASSOC]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ maxlen+36 < dimword (:256) /\
   p+32 < dimword (:256) /\ first <= ready.cs_next_id` by (asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_builtin_encode_method_setup_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_builtin_encode_method_ready >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AC ADD_COMM ADD_ASSOC]) >>
  drule_all (SIMP_RULE (srw_ss()) [AC ADD_COMM ADD_ASSOC]
    (Q.INST [`mid_size` |-> `4:num`] abi_builtin_encode_body_finish)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid` by
    asm_simp_tac bool_ss [] >>
  drule_all abi_builtin_encode_method_value >> disch_then (qspec_then `maxlen` strip_assume_tac) >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (maxlen+36) b cap prepared actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`, `ready.cs_next_var`,
       `LENGTH (enc at av)+36`] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC, asm_simp_tac (srw_ss()) [] >> decide_tac]) >>
  `start.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id` by decide_tac >>
  `FLOOKUP prepared.vs_allocas start.cs_next_id = SOME (p,maxlen+36)` by
    (drule_all abi_builtin_encode_setup_frame_row >> simp[]) >>
  `FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+36)` by
    (mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `lo` |-> `ready.cs_next_id`,
      `next` |-> `ready.cs_next_var`, `d` |-> `p:num`,
      `sz` |-> `maxlen+36:num`, `outsz` |-> `maxlen+36:num`,
      `hi` |-> `final.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_body_allocation_row) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  drule_all abi_builtin_encode_effect_compose >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_METHOD_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin method-ID correctness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeMethodCorrect");
