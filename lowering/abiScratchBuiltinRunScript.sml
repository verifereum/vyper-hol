(* Complete actual lower_abi_encode through its precise recursive core.
   TOP-LEVEL: lower_abi_encode_scratch covers both method-ID choices, exact
   returned Bytes, complete source preservation and physical write ownership. *)
Theory abiScratchBuiltinRun
Ancestors
  abiScratchBuiltinPre abiScratchBuiltinSetup abiScratchBuiltinBody abiScratchBuiltinEffect
  abiScratchEncoderContract abiScratchEffectWiden abiBuiltinEncodeContext abiBuiltinEncodeCode
  abiBuiltinEncodeRun abiBuiltinEncodeMethodReach abiEncoderMemory abiEncoderInput
  abiDecoderAllocation abiDecoderFootprint abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec builtinAbi exprLowering compileEnv valueEncoding valueEncodingProps contractABI
  venomState words list arithmetic

Theorem abi_scratch_builtin_prefix_length:
  LENGTH (abi_builtin_encode_prefix method_id_opt) =
    (case method_id_opt of NONE => 0 | SOME _ => 4)
Proof
  Cases_on `method_id_opt` >> simp[abi_builtin_encode_prefix_def]
QED

Theorem abi_scratch_builtin_value:
  mload p s = n2w (LENGTH bytes+LENGTH prefix) /\
  mem_bytes_at (p+32) (LENGTH prefix) s.vs_memory = prefix /\
  mem_bytes_at (p+32+LENGTH prefix) (LENGTH bytes) s.vs_memory = bytes ==>
  mem_bytes_at (p+32) (LENGTH (prefix++bytes)) s.vs_memory = prefix++bytes /\
  val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH prefix))))
    (vyperValue$BytesV (prefix++bytes)) p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at (p+32) (LENGTH (prefix++bytes)) s.vs_memory = prefix++bytes` by
    (simp_tac bool_ss [LENGTH_APPEND] >> ONCE_REWRITE_TAC [abi_encoder_mem_split] >> simp[]) >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload, ADD_COMM]
QED

Theorem lower_abi_encode_scratch:
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_builtin_pre (type_to_abi_enc_info sf ce ty) at av start method_id_opt src sb source_cap
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
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
      (case method_id_opt of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >> drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_scratch_builtin_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_builtin_pre_def, LET_THM]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ first <= ready.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_scratch_builtin_setup_reach) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all (Q.INST [`st` |-> `start`, `dst` |-> `SND (ops:operand # operand)`]
    abi_scratch_builtin_ready) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  drule_all (Q.INST [`dst` |-> `SND (ops:operand # operand)`, `buf` |-> `FST (ops:operand # operand)`,
    `initial` |-> `prepared:venom_state`, `len_op` |-> `len:operand`,
    `mid_size` |-> `case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4`]
    abi_scratch_builtin_body_finish) >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var limit_st p
    (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) b cap prepared actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `outsz` |-> `maxlen+32+
    (case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`,
    `write_size` |-> `case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 32`]
    abi_scratch_builtin_effect_compose) >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  drule_all abi_scratch_builtin_source >> disch_tac >>
  mp_tac (Q.INST [`bytes` |-> `enc at av`, `prefix` |-> `abi_builtin_encode_prefix method_id_opt`,
    `s` |-> `actual:venom_state`] abi_scratch_builtin_value) >>
  impl_tac >- gvs[abi_scratch_builtin_prefix_length, Excl "enc_def"] >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [LENGTH_APPEND, abi_scratch_builtin_prefix_length, ADD_COMM]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch complete builtin execution not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinRun");
