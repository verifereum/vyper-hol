Theory abiScratchArrayStaticLoop
Ancestors
  abiScratchArrayLoopEntry abiScratchArrayStaticFiniteLoop abiScratchArrayStaticExit
  abiScratchArrayLoopInvariant abiScratchEncoderContract abiEncoderArrayLoopCode
  abiEncoderMembersDefs abiEncoderArrayPrefix abiDecoderLoop abiDecoderReentry
  abiDecoderContract compileEnv valueEncoding contractABI venomState venomExecSemantics words
  list arithmetic abiScratchArrayInitEffects abiScratchEffect venomInst

(* ===== Run ===== *)

(* Compose the actual entry, finite static iterations and count-reload exit.
   TOP-LEVEL: abi_scratch_array_static_loop_run returns exact ABI bytes/length
   and the physical effect from the original loop state. *)

Theorem abi_scratch_array_static_loop_result:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_array_loop_inv ei asz msz F ty avs owner_st limit_st src dst ip dyn_ptr
    site slot cursor_site cursor_slot first last hi sb source_cap d output_size b cap count_op (FST labels) i origin initial ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap origin actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_static_finite_loop >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >>
  `owner_st.cs_next_var <= exit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`initial` |-> `prepared:venom_state`, `label` |-> `SND (SND (labels:string # string # string))`,
    `st` |-> `exit_st`] abi_scratch_array_static_scalar_exit) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> simp[]
QED

Theorem abi_scratch_array_static_loop_run:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz body_st = (idx,body_end) /\
  abi_encoder_array_loop_code func owner_st body_st body_end exit_st ip count_op labels /\
  abi_encode_array_static_exit src asz exit_st = (out,final) /\ fn_has_code exit_st final func /\
  body_end.cs_next_id+3 <= hi /\ hi <= last /\
  body_end.cs_next_var+1 <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first site owner_st 0 initial /\
  abi_decoder_operand_live owner_st.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial /\
  initial.vs_current_bb = owner_st.cs_current_bb /\ initial.vs_inst_idx = LENGTH owner_st.cs_current_insts /\
  ~initial.vs_halted ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last site hi owner_st.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `cursor_site` |-> `0:num`,
    `cursor_slot` |-> `0:num`] abi_scratch_array_loop_enter) >>
  impl_tac >- asm_simp_tac bool_ss [abi_encoder_cursor_def] >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `0:num`, `origin` |-> `initial:venom_state`, `dyn_ptr` |-> `Lit 0w`,
    `cursor_site` |-> `0:num`, `cursor_slot` |-> `0:num`,
    `initial` |-> `jump_to (FST (labels:string # string # string)) initial`]
    abi_scratch_array_static_loop_result) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >>
  qexists_tac `jump_to (FST (labels:string # string # string)) initial` >> simp[]
QED

(* ===== Scratch Array Static Loop ===== *)

(* The actual full static-element loop preserves complete physical resources.
   TOP-LEVEL: abi_scratch_array_static_loop composes real index initialization,
   entry, all static child/backedge iterations and the exact count-reload exit. *)

Theorem abi_scratch_array_static_loop:
  abi_encoder_static_leaf ei /\
  compile_abi_encode_dyn_static_loop dst src ei asz msz count_op start = (out,final) /\
  fn_has_code start final func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    start src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs 0 d initial.vs_memory /\
  abi_decoder_operand_live start.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  final.cs_next_id <= hi /\ hi <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) actual.vs_memory = enc (Array NONE ty) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Array NONE ty) (ListV avs)))) /\
    abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_loop_code >> strip_tac >>
  `owner_st.cs_next_id <= last /\ owner_st.cs_next_id <= hi /\ owner_st.cs_next_var <= limit_st.cs_next_var /\
   body_end.cs_next_id+3 <= hi /\ body_end.cs_next_var+1 <= limit_st.cs_next_var /\
   start.cs_next_var <= owner_st.cs_next_var` by
    (qpat_assum `abi_encoder_array_loop_code _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_loop_code_def]) >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `st'` |-> `owner_st`, `index_ptr` |-> `ip:operand`, `active` |-> `F`]
    abi_scratch_array_index_prepare) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  rename1 `abi_encoder_cursor T ip start.cs_next_id slot first start.cs_next_id owner_st 0 ready` >>
  qpat_assum `abi_scratch_effect _ _ _ _ _ _ _ _ _ _ initial ready`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_effect_def]) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by
    (qpat_assum `!op w. _` irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live owner_st.cs_next_var count_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `initial` |-> `ready:venom_state`]
    abi_scratch_array_static_loop_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial ready` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `owner_st.cs_next_id`, `start.cs_next_id`, `start.cs_next_var`, `output_size`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap ready actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `hi`, `start.cs_next_id`, `owner_st.cs_next_var`, `output_size`] >> simp[]) >>
  `abi_scratch_effect first last start.cs_next_id hi start.cs_next_var limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >>
     qexists_tac `ready` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED
