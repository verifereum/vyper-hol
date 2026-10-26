(* End-to-end lower_abi_encode without a method ID: actual setup, every
   translated recursive descriptor, and the final length word. *)
Theory abiBuiltinEncodeCorrect
Ancestors
  abiBuiltinEncodePre abiBuiltinEncodeSetup abiBuiltinEncodeBody abiBuiltinEncodeContext
  abiBuiltinEncodeCode abiBuiltinAllocation abiBuiltinDecodeEffect abiBuiltinEncodeOwnership
  abiEncoderCorrect abiEncoderInput abiDecoderEffect abiDecoderAllocation abiDecoderContract
  abiDecoderLoop fragExec builtinAbi exprLowering compileEnv valueEncoding valueEncodingProps
  venomState venomExecSemantics words list arithmetic

Theorem lower_abi_encode_no_method:
  lower_abi_encode ensure NONE src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_no_method_pre (type_to_abi_enc_info sf ce ty) at av start src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic maxlen))) (vyperValue$BytesV (enc at av)) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+32) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(p,maxlen+32);(b,cap)] initial actual /\
    (!id. id < start.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_builtin_encode_no_method_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_no_method_pre_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ maxlen+32 < dimword (:256) /\
   first <= ready.cs_next_id` by (asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_builtin_encode_setup_none_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_builtin_encode_no_method_ready >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`mid_size` |-> `0:num`] abi_builtin_encode_body_finish)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (maxlen+32) b cap prepared actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`, `ready.cs_next_var`,
       `32+LENGTH (enc at av)`] >> asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `start.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id` by decide_tac >>
  `FLOOKUP prepared.vs_allocas start.cs_next_id = SOME (p,maxlen+32)` by
    (drule_all abi_builtin_allocation_frame_row >> simp[]) >>
  `FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+32)` by
    (mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `lo` |-> `ready.cs_next_id`,
      `next` |-> `ready.cs_next_var`, `d` |-> `p:num`,
      `sz` |-> `maxlen+32:num`, `outsz` |-> `maxlen+32:num`,
      `hi` |-> `final.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_body_allocation_row) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`st` |-> `start`, `site` |-> `start.cs_next_id`, `outsz` |-> `maxlen+32:num`,
      `d` |-> `p:num`] abi_builtin_decode_effect_compose)) >> strip_tac >>
  qpat_assum `abi_builtin_decode_effect _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_effect_def]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload] >>
  first_assum ACCEPT_TAC
QED
