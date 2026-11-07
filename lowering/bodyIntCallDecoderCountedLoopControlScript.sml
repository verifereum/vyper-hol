(* Physical loop control at the endpoints of the counted control paths. *)
Theory bodyIntCallDecoderCountedLoopControl
Ancestors
  bodyIntCallDecoderCountedControl abiScratchDecoderLoopInvariant abiScratchDecoderLoopControl
  abiScratchEncoderContract abiScratchEffect abiScratchLeafEffect abiDecoderFrame
  abiDecoderLoopRegisters abiDecoderExecution abiDecoderContract abiDecoderAllocation
  abiDecoderValidArrayMemory abiDecoderValidArrayBackedge abiDecoderArrayBackedge
  abiDecoderDynamicLoopSetup abiDecoderReentry compileEnv valueEncoding venomState
  words list arithmetic

Theorem intcall_scratch_decoder_loop_header:
  abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d outsz slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  first <= lo /\ hi <= last /\
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc base_op first_var /\
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ LENGTH vs < dimword (:256) /\ slot < dimword (:256) /\
  B + sb + LENGTH bs < dimword (:256) /\
  abi_decode_source_opcode opc /\ next <= first_var /\
  first_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next ip /\
  abi_decoder_operand_live next base_op /\ eval_operand base_op initial = SOME (n2w B) /\
  eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) ==>
  ?h. abi_scratch_decoder_loop_inv opc bs tv vs (B + sb) d outsz slot site
    first last lo hi next limit_st b cap initial
    (if j < LENGTH vs then body_lbl else exit_lbl) j h /\ gas_path ctx fn s 0 (OK h)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  `fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s`
    by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb) /\
   eval_operand base_op s = SOME (n2w B)` by
    (fs[abi_scratch_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  drule_all abi_decoder_valid_array_memory_count >> strip_tac >>
  `abi_decode_position_loop_ready hdr ip src opc base_op B sb (n2w slot) (LENGTH vs) j s` by
    fs[abi_decode_position_loop_ready_def, abi_decoder_valid_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `abi_decoder_operand_live first_var src /\ abi_decoder_operand_live first_var base_op` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `src <> Var (STRING #"%" (toString first_var)) /\
   base_op <> Var (STRING #"%" (toString first_var))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >> qexists_tac `first_var` >> simp[]) >>
  qabbrev_tac `h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_position_header_state base_op first_var B sb j (LENGTH vs) s)` >>
  `gas_path ctx fn s 0 (OK h)` by
    (drule_all intcall_decode_position_ready_header_path >> simp[Abbr`h`]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_scratch_decoder_header_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial h` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  qexists_tac `h` >> Cases_on `base_op = Lit 0w` >>
  asm_simp_tac (srw_ss()) [abi_scratch_decoder_loop_inv_def, Abbr`h`,
    abi_decode_mload_jump, abi_decode_position_header_state_def, abi_decode_load_update, Excl "enc_def"] >>
  gvs[jump_to_def, update_var_def, abi_decoder_valid_array_memory_def, mload_def,
    abi_decode_source_def, Excl "enc_def"]
QED

Theorem intcall_scratch_decoder_loop_backedge:
  lookup_block block_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString nv_counter)) ip hdr /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  u.vs_current_bb = block_lbl /\ u.vs_inst_idx = LENGTH prefix /\ ~u.vs_halted /\
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) u /\ all_have_type tv vs /\
  abi_scratch_effect first last lo hi next limit_st d outsz b cap initial u /\
  FLOOKUP u.vs_allocas site = SOME (slot,32) /\
  first <= site /\ site < last /\ lo <= site /\ site < hi /\ first <= lo /\ hi <= last /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) /\
  abi_decode_source_opcode opc /\
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH bs <= slot \/ slot + 32 <= sb) /\
  eval_operand (Var iv) u = SOME (n2w j) /\ eval_operand ip u = SOME (n2w slot) /\
  abi_decoder_operand_live next ip /\ next <= nv_counter /\ nv_counter < limit_st.cs_next_var ==>
  ?v. abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ gas_path ctx fn u 0 (OK v)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt limit_st u /\ abi_decoder_budget first last b cap u`
    by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`first` |-> `next:num`, `next` |-> `nv_counter:num`,
    `s` |-> `u:venom_state`, `fuel` |-> `0:num`] abi_decoder_valid_array_backedge) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_footprint_frame [(slot,32)] u v` >>
  `v.vs_halted = u.vs_halted` by simp[] >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap u v` by
    (irule abi_scratch_single_write >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`site`, `slot`] >> gvs[Excl "enc_def"]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial v` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  `ip <> Var (STRING #"%" (toString nv_counter))` by
    (mp_tac (Q.INST [`first` |-> `next:num`, `next` |-> `nv_counter:num`,
       `op` |-> `ip:operand`] abi_decoder_live_excludes_output) >> simp[]) >>
  `gas_path ctx fn u 0 (OK v)` by
    (qpat_assum `v = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule intcall_decode_backedge_path >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [abi_scratch_decoder_loop_inv_def]
QED
