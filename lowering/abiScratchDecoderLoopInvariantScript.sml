(* Loop state permits recursive children to extend the shared allocation map. *)
Theory abiScratchDecoderLoopInvariant
Ancestors
  abiScratchDecoderContract abiScratchDecoderArrayMemory abiScratchDecoderLoopControl
  abiScratchEncoderContract abiScratchEffect abiScratchFootprint abiEncoderArrayFrame
  abiDecoderEffect abiDecoderValidArrayMemory abiDecoderValidArrayScratch abiDecoderArrayScratch
  abiDecoderPrimitiveLoopHeader abiDecoderValidArrayBackedge abiDecoderArrayBackedge
  abiDecoderLoopRegisters abiDecoderExecution abiDecoderLoop abiDecoderReentry
  abiDecoderContract abiDecoderAllocation abiDecoderFrame abiDecoderDynamicLoopSetup compileEnv
  valueEncoding vyperABI venomState words list arithmetic finite_map

Definition abi_scratch_decoder_loop_inv_def:
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
      first last lo hi next limit_st b cap initial hdr j s <=>
    abi_decoder_valid_array_memory opc bs tv vs sb d j s /\
    abi_scratch_effect first last lo hi next limit_st d outsz b cap initial s /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\ mload slot s = n2w j /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted
End

Theorem abi_scratch_decoder_loop_inv_init:
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  FLOOKUP s.vs_allocas site = SOME (slot,32) /\ mload slot s = 0w /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap s hdr 0 s
Proof
  simp[abi_scratch_decoder_loop_inv_def, abi_scratch_effect_refl]
QED

Theorem abi_scratch_decoder_loop_header:
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial hdr j s /\
  first <= lo /\ hi <= last /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc
    (STRING #"%" (toString first_var)) (STRING #"%" (toString (first_var+1)))
    (STRING #"%" (toString (first_var+2))) (STRING #"%" (toString (first_var+3))) /\
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\ LENGTH vs < dimword (:256) /\ slot < dimword (:256) /\
  sb + LENGTH bs < dimword (:256) /\
  abi_decode_source_opcode opc /\ next <= first_var /\ first_var + 4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) ==>
  ?h. abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial
    (if j < LENGTH vs then body_lbl else exit_lbl) j h /\ abi_decode_sim ctx fn s h
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  `fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s`
    by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (fs[abi_scratch_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  drule_all abi_decoder_valid_array_memory_count >> strip_tac >>
  `abi_decode_loop_ready hdr ip src opc (n2w slot) (n2w sb) (LENGTH vs) j s` by
    fs[abi_decode_loop_ready_def, abi_decoder_valid_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `abi_decoder_operand_live first_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >>
  `src <> Var (STRING #"%" (toString first_var))` by
    (mp_tac (Q.INST [`first` |-> `first_var:num`, `next` |-> `first_var:num`, `op` |-> `src:operand`]
      abi_decoder_live_excludes_output) >> simp[]) >>
  `STRING #"%" (toString (first_var:num)) <> STRING #"%" (toString (first_var+1))` by simp[] >>
  qabbrev_tac `h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first_var))
      (STRING #"%" (toString (first_var+1))) (STRING #"%" (toString (first_var+2)))
      (STRING #"%" (toString (first_var+3))) j (LENGTH vs) s)` >>
  `abi_decode_sim ctx fn s h` by
    (drule_all abi_decode_ready_header_sim >> simp[Abbr`h`]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_scratch_decoder_header_effect >> simp[]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial h` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  qexists_tac `h` >>
  asm_simp_tac (srw_ss()) [abi_scratch_decoder_loop_inv_def, Abbr`h`,
    abi_decode_mload_jump, abi_decode_header_state_def, abi_decode_load_update, Excl "enc_def"] >>
  simp[jump_to_def, update_var_def]
QED

Theorem abi_scratch_decoder_child_advance:
  abi_scratch_decoder_loop_inv opc bs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial body_lbl j s /\ j < LENGTH vs /\
  all_have_type tv vs /\
  val_in_memory tv (EL j vs) (d + 32 + j * type_memory_size tv) t.vs_memory /\
  abi_scratch_effect first last child_lo child_hi child_next limit_st
    (d + 32 + j * type_memory_size tv) (type_memory_size tv) b cap s t /\
  lo <= child_lo /\ child_hi <= hi /\ next <= child_next /\
  first <= site /\ site < last /\ (site < child_lo \/ child_hi <= site) /\
  d + 32 + j * type_memory_size tv + type_memory_size tv <= d + outsz /\
  first <= lo /\ hi <= last /\
  abi_scratch_decoder_ranges opc hi_op src dst sb (LENGTH bs) d outsz first last b cap s ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) t /\
  abi_scratch_effect first last lo hi next limit_st d outsz b cap initial t /\
  FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = n2w j /\ ~t.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_loop_inv_def]) >>
  `abi_decoder_budget first last b cap s` by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  `first <= child_lo /\ child_hi <= last` by decide_tac >>
  `abi_decoder_valid_array_memory opc bs tv vs sb d (SUC j) t` by
    (drule_all abi_scratch_decoder_array_child_advance >> simp[]) >>
  `abi_footprint_disjoint (d + 32 + j * type_memory_size tv) (type_memory_size tv)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
     irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `outsz`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `site IN abi_decoder_ids first last /\ ~(site IN abi_decoder_ids child_lo child_hi)` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FLOOKUP t.vs_allocas site = SOME (slot,32) /\ mload slot t = mload slot s` by
    (drule_all abi_scratch_effect_slot >> simp[]) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap s t` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d + 32 + j * type_memory_size tv`, `child_hi`, `child_lo`,
       `child_next`, `type_memory_size tv`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_scratch_effect first last lo hi next limit_st d outsz b cap initial t` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  `~t.vs_halted` by fs[abi_scratch_effect_def, Excl "enc_def"] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_loop_backedge:
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
    first last lo hi next limit_st b cap initial hdr (SUC j) v /\ abi_decode_sim ctx fn u v
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
  `abi_decode_sim ctx fn u v` by
    (qpat_assum `v = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule abi_decode_backedge_sim >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [abi_scratch_decoder_loop_inv_def]
QED
