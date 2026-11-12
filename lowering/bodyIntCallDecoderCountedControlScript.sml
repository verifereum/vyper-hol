(* Counted concrete control for the ABI loop states. *)
Theory bodyIntCallDecoderCountedControl
Ancestors
  abiDecoderPrimitiveLoopFinite abiDecoderExecution fragGasSeq fragGasPath
  gasCount venomInstProofs instIdxIndep rich_list arithmetic venomState
  venomInst venomExecSemantics list fragExec abiDecoderContract words
  abiDecoderPrimitiveLoopInvariant abiDecoderLoopRegisters abiDecoderArrayInvariant
  abiDecoderArrayBackedge abiDecoderReentry abiDecoderLoop abiDecoderFrame
  abiDecoderPrimitiveLoopReach abiDecoderPrimitiveLoopContext abiDecoderPrimitiveLoopFrames
  emitHelperProps exprLoweringProps compileEnv valueEncoding

Theorem intcall_jump_step_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> GAS /\ step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path ctx func s 0 (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_edge ctx func s 0 (OK (jump_to lbl s))` by
    (simp[gas_path_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_rules, ADD_CLAUSES]
QED

Theorem intcall_zero_prefix_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
  EVERY (\i. i.inst_opcode <> GAS) code /\
  run_inst_seq code s = OK t /\ k = s.vs_inst_idx + LENGTH code ==>
  gas_path ctx func s 0 (OK (t with vs_inst_idx := k))
Proof
  strip_tac >> drule_all tuple_run_inst_seq_gas_path >>
  `FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[FILTER_EQ_NIL, EVERY_MEM]) >> simp[]
QED

Theorem intcall_decode_backedge_path:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv ip hdr /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w i) /\ eval_operand ip s = SOME p /\
  ip <> Var nv /\ i < ncount /\ ncount < dimword(:256) ==>
  gas_path ctx fn s 0 (OK (jump_to hdr
    (mstore (w2n p) (n2w (SUC i)) (update_var nv (n2w (SUC i)) s))))
Proof
  strip_tac >> drule_all abi_decode_increment_prefix >> strip_tac >>
  qmatch_goalsub_abbrev_tac `jump_to hdr t` >>
  `gas_path ctx fn s 0 (OK (t with vs_inst_idx := LENGTH prefix + 2))` by
    (irule intcall_zero_prefix_path >> simp[] >>
     qexists_tac `TAKE 2 (abi_decode_backedge_insts id iv nv ip hdr)` >>
     simp[abi_decode_backedge_insts_def, mk_inst_def, is_terminator_def,
          DROP_LENGTH_APPEND, Abbr `t`]) >>
  `gas_path ctx fn (t with vs_inst_idx := LENGTH prefix + 2) 0
     (OK (jump_to hdr t))` by
    (`jump_to hdr t = jump_to hdr
        (t with vs_inst_idx := LENGTH prefix + 2)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >> irule intcall_jump_step_path >>
     simp[Abbr `t`, mstore_def, update_var_def] >>
     qexists_tac `mk_inst (id+2) JMP [Label hdr] []` >>
     simp[get_instruction_def,
          abi_decode_backedge_insts_def, EL_APPEND_EQN, mk_inst_def,
          is_terminator_def, step_inst_base_opcode_eqs, jump_to_def]) >>
  metis_tac[gas_path_then, ADD_CLAUSES]
QED

Theorem intcall_decode_position_ready_header_path:
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl id ip src opc base_op first /\
  abi_decode_position_loop_ready hdr ip src opc base_op B sb p ncount j s /\
  abi_decode_source_opcode opc /\
  src <> Var (STRING #"%" (toString first)) /\
  base_op <> Var (STRING #"%" (toString first)) /\
  ncount < dimword(:256) ==>
  gas_path ctx fn s 0 (OK
    (jump_to (if j < ncount then body_lbl else exit_lbl)
      (abi_decode_position_header_state base_op first B sb j ncount s)))
Proof
  strip_tac >>
  gvs[abi_decode_position_loop_cfg_def, abi_decode_position_loop_ready_def] >>
  drule_all abi_decode_position_header_prefix >> strip_tac >>
  qmatch_goalsub_abbrev_tac `jump_to dest t` >>
  `gas_path ctx fn s 0 (OK (t with vs_inst_idx :=
      4 + abi_decode_position_header_delta base_op))` by
    (irule intcall_zero_prefix_path >> simp[] >>
     qexists_tac `TAKE (4 + abi_decode_position_header_delta base_op)
       (abi_decode_position_header_insts id ip src opc base_op first body_lbl exit_lbl)` >>
     Cases_on `base_op = Lit 0w` >>
     gvs[abi_decode_source_opcode_def, abi_decode_position_header_insts_def,
       abi_decode_position_header_delta_def, mk_inst_def, is_terminator_def, Abbr `t`]) >>
  `gas_path ctx fn (t with vs_inst_idx :=
      4 + abi_decode_position_header_delta base_op) 0 (OK (jump_to dest t))` by
    (`jump_to dest t = jump_to dest (t with vs_inst_idx :=
        4 + abi_decode_position_header_delta base_op)` by simp[jump_to_def] >>
     pop_assum SUBST1_TAC >> irule intcall_jump_step_path >>
     Cases_on `base_op = Lit 0w` >>
     simp[Abbr `t`, abi_decode_position_header_state_def,
       abi_decode_position_header_delta_def, update_var_def] >>
     qexists_tac `mk_inst (id + 4 + abi_decode_position_header_delta base_op) JNZ
       [Var (STRING #"%" (toString (first+3+abi_decode_position_header_delta base_op)));
        Label exit_lbl; Label body_lbl] []` >>
     simp[get_instruction_def, abi_decode_position_header_insts_def,
       abi_decode_position_header_delta_def, mk_inst_def, is_terminator_def,
       step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, Abbr `dest`] >>
     Cases_on `j < ncount` >> simp[bool_to_word_def]) >>
  metis_tac[gas_path_then, ADD_CLAUSES]
QED

Theorem intcall_decoder_primitive_loop_header_path:
  abi_decoder_primitive_loop_inv opc aty avs tv vs (B+sb) d slot first limit_st fp initial hdr j s /\
  abi_decode_position_loop_cfg fn hdr body_lbl exit_lbl hid ip src opc base_op first /\
  LENGTH avs = LENGTH vs /\ LENGTH vs < dimword (:256) /\ slot < dimword (:256) /\
  B+sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) /\
  abi_decode_source_opcode opc /\
  first + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  abi_decoder_operand_live first src /\ abi_decoder_operand_live first ip /\
  abi_decoder_operand_live first base_op /\ eval_operand base_op initial = SOME (n2w B) /\
  eval_operand ip initial = SOME (n2w slot) /\ eval_operand src initial = SOME (n2w sb) ==>
  ?h. abi_decoder_primitive_loop_inv opc aty avs tv vs (B+sb) d slot first limit_st fp
      initial (if j < LENGTH vs then body_lbl else exit_lbl) j h /\
      gas_path ctx fn s 0 (OK h)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_inv_def]) >>
  `fresh_vars_wrt limit_st s` by fs[abi_decoder_loop_rel_def] >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb) /\
   eval_operand base_op s = SOME (n2w B)` by metis_tac[abi_decoder_loop_rel_eval] >>
  drule_all abi_decoder_array_memory_count >> strip_tac >>
  `abi_decode_position_loop_ready hdr ip src opc base_op B sb (n2w slot) (LENGTH vs) j s` by
    fs[abi_decode_position_loop_ready_def, abi_decoder_array_memory_def, w2n_n2w, Excl "enc_def"] >>
  `src <> Var (STRING #"%" (toString first)) /\
   base_op <> Var (STRING #"%" (toString first))` by
    (conj_tac >> irule abi_decoder_live_excludes_output >> qexists_tac `first` >> simp[]) >>
  qabbrev_tac `h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_position_header_state base_op first B sb j (LENGTH vs) s)` >>
  `gas_path ctx fn s 0 (OK h)` by
    (drule_all intcall_decode_position_ready_header_path >> simp[Abbr `h`]) >>
  `abi_decoder_loop_rel first limit_st fp s h` by
    (simp_tac bool_ss [Abbr `h`] >> irule abi_decoder_loop_rel_position_header >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp initial h` by
    (drule_all abi_decoder_loop_rel_trans >> simp[]) >>
  qexists_tac `h` >>
  Cases_on `base_op = Lit 0w` >>
  asm_simp_tac (srw_ss()) [abi_decoder_primitive_loop_inv_def, Abbr `h`,
    abi_decode_mload_jump, abi_decode_position_header_state_def, abi_decode_load_update,
    Excl "enc_def"] >>
  simp[jump_to_def, update_var_def] >> gvs[mload_def]
QED

Theorem intcall_decoder_primitive_loop_backedge_path:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc base_op hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp (B+sb) d slot fp /\
  abi_decoder_loop_inputs first ip src dst base_op B sb d slot initial /\
  abi_decoder_primitive_body_end opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d
    first limit_st fp initial st1 iv j u /\ j < LENGTH vs ==>
  ?v. abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs (B+sb) d slot
      first limit_st fp initial hdr (SUC j) v /\ gas_path ctx fn u 0 (OK v)
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
    `id` |-> `st1.cs_next_id`, `aty` |-> `vyper_to_abi_type env ty`, `sb` |-> `B+sb`]
    abi_decoder_array_backedge) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_footprint_frame [(slot,32)] u v` >>
  `abi_decode_footprint_frame fp u v` by
    (drule_all abi_decoder_footprint_member_frame >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp u v` by
    (asm_simp_tac bool_ss [abi_decoder_loop_rel_def] >> fs[abi_decoder_loop_rel_def]) >>
  `abi_decoder_loop_rel first limit_st fp initial v` by
    metis_tac[abi_decoder_loop_rel_trans] >>
  `ip <> Var (STRING #"%" (toString st1.cs_next_var))` by
    (drule_all abi_decoder_live_excludes_output >> simp[]) >>
  `gas_path ctx fn u 0 (OK v)` by
    (qpat_assum `v = jump_to _ _` SUBST1_TAC >>
     `slot = w2n (n2w slot:bytes32)` by simp[w2n_n2w] >>
     pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
     irule intcall_decode_backedge_path >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> asm_simp_tac bool_ss [abi_decoder_primitive_loop_inv_def]
QED
