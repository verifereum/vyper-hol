(* Word staging establishes full encoder input; future resources depend only
   on numeric bounds and the pure metadata update of its one allocation. *)
Theory abiBuiltinEncodeWordPrepare
Ancestors
  abiBuiltinEncodeWordStageReach abiBuiltinEncodeWordStageCode abiBuiltinEncodeResources
  abiBuiltinEncodeInput abiBuiltinAllocationState abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec compileEnv exprLowering venomState venomExecSemantics finite_map words byte list arithmetic

Theorem abi_builtin_encode_word_prepare:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,32)) /\
  eval_operand value_op initial = SOME w /\ abi_decoder_operand_live st.cs_next_var value_op /\
  is_word_type ty /\ has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ LENGTH (enc at av) <= maxlen /\
  abi_builtin_encode_resources (st with cs_next_id := st.cs_next_id+2)
    method_id_opt sb 32 p maxlen first last b cap (abi_builtin_allocate_state st.cs_next_id 32 initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_builtin_encode_pre (type_to_abi_enc_info sf ce ty) at av staged method_id_opt
      buf.buf_operand sb 32 p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb 32 initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  `sb < dimword (:256)` by decide_tac >>
  drule_all abi_builtin_encode_word_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb 32 actual.vs_memory` by
    (drule_all abi_builtin_encode_staged_word_input >> simp[]) >>
  `abi_builtin_encode_resources staged method_id_opt sb 32 p maxlen first last b cap actual` by
    (mp_tac (Q.INST [`st` |-> `st with cs_next_id := st.cs_next_id+2`, `ready` |-> `staged`,
      `source_cap` |-> `32:num`, `s` |-> `abi_builtin_allocate_state st.cs_next_id 32 initial`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_resources_transport) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_builtin_encode_pre_resources] >>
  first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_PREPARE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word preparation not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordPrepare");
