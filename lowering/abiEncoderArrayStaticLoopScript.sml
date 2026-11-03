(* Execute the entire actual static-element loop, including initialization and entry. *)
Theory abiEncoderArrayStaticLoop
Ancestors
  abiEncoderArrayRound abiEncoderArrayLoopRun abiEncoderArrayLoopCode abiEncoderArrayMemory
  abiEncoderMembersDefs abiEncoderAdmissible abiDecoderEffect abiDecoderContract
  abiDecoderReentry abiDecoderLoop fragExec compileEnv valueEncoding contractABI venomState
  venomInst words list arithmetic

Theorem abi_encoder_array_static_loop:
  abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_encoder_array_memory ei asz msz F ty avs start src dst sb source_cap d output_size b cap 0 initial /\
  abi_decoder_operand_live start.cs_next_var count_op /\
  eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual.
    mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `active` |-> `F`, `j` |-> `0:num`]
    abi_encoder_array_index_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> asm_simp_tac bool_ss []) >>
  `abi_encoder_cursor F (Lit 0w) 0 0 first start.cs_next_id owner_st
    (LENGTH avs*abi_member_head_size ty) ready` by simp[abi_encoder_cursor_def] >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `start.cs_next_id`,
    `cursor_site` |-> `0:num`, `cursor_slot` |-> `0:num`, `initial` |-> `ready:venom_state`]
    abi_encoder_array_loop_run) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  `abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >>
     asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss []
QED
