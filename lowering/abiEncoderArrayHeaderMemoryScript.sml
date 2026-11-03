Theory abiEncoderArrayHeaderMemory
Ancestors
  abiEncoderArrayHeader abiDecoderLoopRegisters abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderEffect abiDecoderAllocation abiDecoderContract compileEnv venomState
  venomExecSemantics words arithmetic abiEncoderMembersDefs abiEncoderDynamic
  abiDecoderProtectedScratch finite_map abiEncoderArrayMemory abiDecoderArrayBackedge
  abiDecoderLoop valueEncoding contractABI list

(* Repeated encoder headers overwrite only their three generated registers. *)
Theorem abi_encode_array_header_registers:
  next+3 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (abi_encode_array_header_state
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) i n s)
Proof
  strip_tac >> `next < limit_st.cs_next_var /\ next+1 < limit_st.cs_next_var /\
    next+2 < limit_st.cs_next_var` by decide_tac >>
  asm_simp_tac bool_ss [abi_encode_array_header_state_def, abi_decoder_generated_update_fresh]
QED

Theorem abi_encode_array_header_address_frame:
  abi_decoder_address_frame next s (jump_to lbl (abi_encode_array_header_state
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) i n s))
Proof
  simp_tac bool_ss [abi_decoder_address_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `next <= next+1 /\ next <= next+2` by simp[] >>
      imp_res_tac abi_decoder_operand_live_mono >>
      asm_simp_tac bool_ss [abi_decoder_operand_jump, abi_encode_array_header_state_def,
        abi_decoder_generated_update_operand]) >>
  simp[abi_encode_array_header_state_def, jump_to_def, update_var_def]
QED

Theorem abi_encode_array_header_effect:
  next+3 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s
    (jump_to lbl (abi_encode_array_header_state
      (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
      (STRING #"%" (toString (next+2))) i n s))
Proof
  strip_tac >> drule_all abi_encode_array_header_registers >> disch_tac >>
  irule abi_decoder_address_effect >> asm_simp_tac bool_ss [abi_decoder_fresh_jump] >>
  qexists_tac `next` >> simp[abi_encode_array_header_address_frame]
QED

(* Stable cursor observations at a loop's compiler entry, across recursive bodies. *)
Theorem abi_encoder_cursor_bounds:
  abi_encoder_cursor T cursor_op site slot first lo st off s /\
  abi_decoder_budget first last b cap s /\ st.cs_next_id <= last ==>
  first <= site /\ site < last /\ b <= slot /\ slot+32 <= b+cap /\ slot < dimword (:256)
Proof
  simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `site < last` by decide_tac >> `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  qpat_assum `abi_decoder_budget _ _ _ _ _`
    (assume_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_mono:
  abi_encoder_cursor active cursor_op site slot first lo st off s /\
  st.cs_next_var <= prepared.cs_next_var /\ st.cs_next_id <= prepared.cs_next_id ==>
  abi_encoder_cursor active cursor_op site slot first lo prepared off s
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live prepared.cs_next_var cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_encoder_cursor_effect_registered:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  mload slot actual = n2w next_off ==>
  abi_encoder_cursor active cursor_op site slot first lo st next_off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encoder_cursor_effect_protected:
  abi_encoder_cursor active cursor_op site slot first lo st off initial /\
  abi_decoder_effect first last owned_lo owned_hi next limit_st d sz b cap initial actual /\
  st.cs_next_var <= next /\ site < last /\ (site < owned_lo \/ owned_hi <= site) ==>
  abi_encoder_cursor active cursor_op site slot first lo st off actual
Proof
  Cases_on `active` >> simp_tac bool_ss [abi_encoder_cursor_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`lo` |-> `owned_lo:num`, `hi` |-> `owned_hi:num`,
    `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_decoder_effect_protected_slot) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decoder_operand_live next cursor_op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand cursor_op actual = SOME (n2w slot)` by
    (imp_res_tac abi_encoder_effect_operand >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

(* The actual header preserves complete source/prefix data and both loop cursors. *)
Theorem abi_encoder_array_header_memory:
  lookup_block hdr func.fn_blocks = SOME <|bb_label := hdr; bb_instructions :=
    abi_encode_array_header_insts id ip count_op (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2)))
      body_lbl exit_lbl|> /\
  lookup_block body_lbl func.fn_blocks = SOME body_bb /\
  lookup_block exit_lbl func.fn_blocks = SOME exit_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\ phi_prefix_length exit_bb.bb_instructions = 0 /\
  initial.vs_current_bb = hdr /\ initial.vs_inst_idx = 0 /\ ~initial.vs_halted /\
  abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k initial /\
  abi_encoder_cursor T ip site slot first lo st j initial /\
  abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off initial /\
  abi_decoder_operand_live st.cs_next_var count_op /\ eval_operand count_op initial = SOME (n2w (LENGTH avs)) /\
  j <= LENGTH avs /\ st.cs_next_id <= last /\ st.cs_next_var+3 <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_decoder_budget first last b cap initial ==>
  ?ready. abi_encoder_array_memory ei asz msz active ty avs st src dst sb source_cap d output_size b cap k ready /\
    abi_encoder_cursor T ip site slot first lo st j ready /\
    abi_encoder_cursor active dyn_ptr cursor_site cursor_slot first lo st off ready /\
    eval_operand count_op ready = SOME (n2w (LENGTH avs)) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial ready /\
    ready.vs_current_bb = (if j < LENGTH avs then body_lbl else exit_lbl) /\
    ready.vs_inst_idx = 0 /\ ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_array_memory_typed >> strip_tac >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  mp_tac (Q.INST [`cursor_op` |-> `ip:operand`, `off` |-> `j:num`, `s` |-> `initial:venom_state`]
    abi_encoder_cursor_bounds) >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `count_op <> Var (STRING #"%" (toString st.cs_next_var))` by
    (mp_tac (Q.INST [`first` |-> `st.cs_next_var`, `next` |-> `st.cs_next_var`, `op` |-> `count_op:operand`]
      abi_decoder_live_excludes_output) >> asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  qabbrev_tac `ready = jump_to (if j < LENGTH avs then body_lbl else exit_lbl)
    (abi_encode_array_header_state (STRING #"%" (toString st.cs_next_var))
      (STRING #"%" (toString (st.cs_next_var+1))) (STRING #"%" (toString (st.cs_next_var+2)))
      j (LENGTH avs) initial)` >>
  `abi_decoder_address_frame st.cs_next_var initial ready` by
    simp[Abbr`ready`, abi_encode_array_header_address_frame] >>
  mp_tac (Q.INST [`prepared` |-> `st`, `dyn` |-> `active:bool`, `j` |-> `k:num`,
    `actual` |-> `ready:venom_state`] abi_encoder_array_memory_address) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`prepared` |-> `st`, `active` |-> `T`, `dyn_ptr` |-> `ip:operand`,
    `off` |-> `j:num`, `actual` |-> `ready:venom_state`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`prepared` |-> `st`, `site` |-> `cursor_site:num`, `slot` |-> `cursor_slot:num`,
    `actual` |-> `ready:venom_state`] abi_encoder_cursor_address) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st d output_size b cap initial ready` by
    (simp_tac bool_ss [Abbr`ready`] >> irule abi_encode_array_header_effect >> asm_simp_tac bool_ss []) >>
  `eval_operand count_op ready = SOME (n2w (LENGTH avs))` by fs[abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `n` |-> `LENGTH (avs:abi_value list)`, `i` |-> `j:num`,
    `p` |-> `n2w slot:bytes32`, `iv` |-> `STRING #"%" (toString st.cs_next_var)`,
    `cmp` |-> `STRING #"%" (toString (st.cs_next_var+1))`,
    `done` |-> `STRING #"%" (toString (st.cs_next_var+2))`] abi_encode_array_header_sim) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> disch_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  simp[Abbr`ready`, jump_to_def, abi_encode_array_header_state_def, update_var_def]
QED
