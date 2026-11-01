Theory abiDecoderPrimitiveLoopFinite
Ancestors
  abiDecoderPrimitiveLoopInvariant abiDecoderLoopRegisters abiDecoderArrayInvariant
  abiDecoderArrayBackedge abiDecoderReentry abiDecoderExecution abiDecoderLoop abiDecoderFrame
  abiDecoderContract emitHelperProps exprLoweringProps compileEnv venomState words arithmetic
  abiDecoderPrimitiveLoopReach abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopFrames
  valueEncoding venomExecSemantics venomInst list
Libs
  Omega

(* The generated header preserves the full loop invariant and selects its edge. *)
Theorem abi_decoder_footprint_frame_jump[simp]:
  abi_decode_footprint_frame fp s (jump_to lbl t) <=> abi_decode_footprint_frame fp s t
Proof
  simp[abi_decode_footprint_frame_def, jump_to_def]
QED

Theorem abi_decoder_loop_rel_header:
  first + 4 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  abi_decoder_loop_rel first limit_st fp s
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) i ncount s))
Proof
  strip_tac >> drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `h = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
    (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
    (STRING #"%" (toString (first+3))) i ncount s)` >>
  `fresh_vars_wrt limit_st h` by simp[Abbr`h`] >>
  `!op. abi_decoder_operand_live first op ==> eval_operand op h = eval_operand op s` by
    asm_simp_tac bool_ss [Abbr`h`, abi_decoder_operand_jump] >>
  `h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
   h.vs_halted = s.vs_halted` by
    simp[Abbr`h`, jump_to_def, abi_decode_header_state_def, update_var_def] >>
  `abi_decode_footprint_frame fp s h` by
    (simp_tac bool_ss [Abbr`h`, abi_decoder_footprint_frame_jump] >>
     irule (cj 1 abi_decode_header_observations)) >>
  asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >> metis_tac[]
QED

Theorem abi_decoder_primitive_loop_header:
  abi_decoder_primitive_loop_inv opc aty avs tv vs sb d slot first limit_st fp initial hdr j s /\
  abi_decode_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  LENGTH avs = LENGTH vs /\ LENGTH vs < dimword (:256) /\ slot < dimword (:256) /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) /\
  abi_decode_source_opcode opc /\ first + 4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first ip /\
  eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) ==>
  ?h. abi_decoder_primitive_loop_inv opc aty avs tv vs sb d slot first limit_st fp
      initial (if j < LENGTH vs then body_lbl else exit_lbl) j h /\ abi_decode_sim ctx fn s h
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_inv_def]) >>
  `fresh_vars_wrt limit_st s` by fs[abi_decoder_loop_rel_def] >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    metis_tac[abi_decoder_loop_rel_eval] >>
  drule_all abi_decoder_array_memory_count >> strip_tac >>
  `abi_decode_loop_ready hdr ip src opc (n2w slot) (n2w sb) (LENGTH vs) j s` by
    fs[abi_decode_loop_ready_def, abi_decoder_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `src <> Var (STRING #"%" (toString first))` by
    (mp_tac (Q.INST [`next` |-> `first:num`, `op` |-> `src:operand`]
       abi_decoder_live_excludes_output) >> simp[]) >>
  `STRING #"%" (toString (first:num)) <> STRING #"%" (toString (first+1))` by simp[] >>
  qabbrev_tac `h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  `abi_decode_sim ctx fn s h` by
    (drule_all abi_decode_ready_header_sim >> simp[Abbr`h`]) >>
  `abi_decoder_loop_rel first limit_st fp s h` by
    (simp_tac bool_ss [Abbr`h`] >> irule abi_decoder_loop_rel_header >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp initial h` by
    (drule_all abi_decoder_loop_rel_trans >> simp[]) >>
  qexists_tac `h` >>
  asm_simp_tac (srw_ss()) [abi_decoder_primitive_loop_inv_def, Abbr`h`,
    abi_decode_mload_jump, abi_decode_header_state_def, abi_decode_load_update,
    Excl "enc_def"] >>
  simp[jump_to_def, update_var_def]
QED

(* The concrete increment/store/jump closes a primitive body iteration. *)
Theorem abi_decoder_primitive_backedge_code:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\ abi_decode_source_opcode opc ==>
  ?bb. lookup_block st1.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = st1.cs_current_insts ++
      abi_decode_backedge_insts st1.cs_next_id iv
        (STRING #"%" (toString st1.cs_next_var)) ip hdr /\
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions := abi_decode_header_insts hid ip src opc
        (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
        (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3)))
        st0.cs_current_bb exit_lbl|> /\
    phi_prefix_length (abi_decode_header_insts hid ip src opc
      (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
      (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3)))
      st0.cs_current_bb exit_lbl) = 0
Proof
  strip_tac >> drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  fs[abi_decoder_primitive_loop_compiled_def, abi_decoder_primitive_loop_code_def,
     abi_decode_loop_cfg_def] >>
  simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def] >> metis_tac[]
QED

Theorem abi_decoder_primitive_loop_separation:
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp ==>
  (slot + 32 <= d \/ d + 32 + LENGTH vs * type_memory_size tv <= slot) /\
  (opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= slot \/
    slot + 32 <= sb)
Proof
  strip_tac >> drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  `LENGTH vs * 32 <= maxn * 32` by simp[LE_MULT_RCANCEL] >>
  qpat_x_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decoder_primitive_loop_data_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  gvs[Excl "enc_def"] >> Omega.OMEGA_TAC
QED

Theorem abi_decoder_primitive_loop_backedge_reach:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_body_end opc (vyper_to_abi_type env ty) avs tv vs sb d
    first limit_st fp initial st1 iv j u /\ j < LENGTH vs ==>
  ?v. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr (SUC j) v /\ abi_decode_sim ctx fn u v
Proof
  strip_tac >>
  `abi_decode_source_opcode opc /\ slot < dimword (:256) /\ MEM (slot,32) fp` by
    fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_backedge_code >> strip_tac >>
  drule_all abi_decoder_primitive_loop_separation >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_primitive_body_end _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_body_end_def]) >>
  drule_all abi_decoder_loop_inputs_eval >> strip_tac >>
  `abi_decoder_operand_live first ip` by fs[abi_decoder_loop_inputs_def] >>
  `fresh_vars_wrt limit_st u` by fs[abi_decoder_loop_rel_def] >>
  `st1.cs_next_var < limit_st.cs_next_var` by fs[abi_decoder_primitive_loop_compiled_def] >>
  mp_tac (Q.INST [`fuel` |-> `0:num`, `s` |-> `u:venom_state`,
    `next` |-> `st1.cs_next_var`, `prefix` |-> `st1.cs_current_insts`,
    `id` |-> `st1.cs_next_id`, `aty` |-> `vyper_to_abi_type env ty`]
    abi_decoder_array_backedge) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_footprint_frame [(slot,32)] u v` >>
  `abi_decode_footprint_frame fp u v` by
    (drule_all abi_decoder_footprint_member_frame >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp u v` by
    (asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >>
     fs[abi_decoder_loop_rel_def]) >>
  `abi_decoder_loop_rel first limit_st fp initial v` by
    metis_tac[abi_decoder_loop_rel_trans] >>
  `ip <> Var (STRING #"%" (toString st1.cs_next_var))` by
    (drule_all abi_decoder_live_excludes_output >> simp[]) >>
  `abi_decode_sim ctx fn u v` by
    (qpat_assum `v = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule abi_decode_backedge_sim >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [abi_decoder_primitive_loop_inv_def]
QED

(* A finite primitive-array loop, with the body supplied by actual compilation. *)
Theorem abi_decoder_primitive_loop_header_reach:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr j s ==>
  ?h. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial (if j < LENGTH vs then st0.cs_current_bb else exit_lbl) j h /\
    abi_decode_sim ctx fn s h
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  qpat_assum `abi_decoder_loop_inputs _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_loop_inputs_def]) >>
  drule_all abi_decoder_primitive_loop_header >> simp[]
QED

Theorem abi_decoder_primitive_loop_iteration:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr j s /\ j < LENGTH vs ==>
  ?v. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr (SUC j) v /\ abi_decode_sim ctx fn s v
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_header_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial st0.cs_current_bb j h` by
    (qpat_x_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _
       (if _ then _ else _) _ _` mp_tac >> simp[]) >>
  drule_all abi_decoder_primitive_loop_body_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_primitive_loop_backedge_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem abi_decoder_primitive_loop_exit:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr (LENGTH vs) s ==>
  ?t. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_header_reach >> simp[]
QED

Theorem abi_decoder_primitive_loop_finite:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr i s ==>
  ?t. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs) t /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `i <= LENGTH vs` by
    fs[abi_decoder_primitive_loop_inv_def, abi_decoder_array_memory_def, Excl "enc_def"] >>
  mp_tac (Q.SPECL [`LENGTH (vs:vyperValue$value list)`, `i:num`,
    `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial hdr`,
    `abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
      first limit_st fp initial exit_lbl (LENGTH vs)`, `ctx`, `fn`, `s`]
    abi_decode_finite_iteration) >>
  impl_tac
  >- (conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac
      >- (rpt strip_tac >> drule_all abi_decoder_primitive_loop_iteration >> simp[]) >>
      rpt strip_tac >> drule_all abi_decoder_primitive_loop_exit >> simp[]) >>
  simp[]
QED

Theorem abi_decoder_primitive_loop_typed:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial hdr i s ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_loop_rel first limit_st fp initial t /\
    t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    mload slot t = n2w (LENGTH vs) /\ abi_decode_sim ctx fn s t
Proof
  strip_tac >> drule_all abi_decoder_primitive_loop_finite >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> fs[abi_decoder_primitive_loop_inv_def] >>
  drule_all abi_decoder_array_memory_exit >> simp[]
QED
