(* Execution of the actual compiled primitive body inside its containing function. *)
Theory abiDecoderPrimitiveLoopReach
Ancestors
  abiDecoderPrimitiveLoopFrames abiDecoderPrimitiveLoopContext
  abiDecoderPrimitiveLoopInvariant abiDecoderArrayIteration abiDecoderArrayInvariant
  abiDecoderLoop abiDecoderReentry abiDecoderExecution abiDecoderContract
  fragExec exprLoweringProps emitHelperProps compileEnv venomState words list arithmetic

Definition abi_decoder_primitive_body_end_def:
  abi_decoder_primitive_body_end opc aty avs tv vs sb d first limit_st fp initial
      st1 iv j u <=>
    abi_decoder_array_memory opc aty avs tv vs sb d (SUC j) u /\
    abi_decoder_loop_rel first limit_st fp initial u /\
    eval_operand (Var iv) u = SOME (n2w j) /\
    u.vs_current_bb = st1.cs_current_bb /\
    u.vs_inst_idx = LENGTH st1.cs_current_insts /\ ~u.vs_halted
End

Theorem abi_decoder_primitive_loop_body_reach:
  abi_decoder_primitive_loop_compiled fn st0 middle st1 ops ip src dst opc hi clamp
    hdr exit_lbl hid first iv limit_st /\
  abi_decoder_primitive_loop_data ce env sf ty tv maxn avs vs opc clamp sb d slot fp /\
  abi_decoder_loop_inputs first ip src dst sb d slot initial /\
  abi_decoder_primitive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d slot
    first limit_st fp initial st0.cs_current_bb j s /\ j < LENGTH vs ==>
  ?u. abi_decoder_primitive_body_end opc (vyper_to_abi_type env ty) avs tv vs sb d
      first limit_st fp initial st1 iv j u /\ abi_decode_sim ctx fn s u
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_primitive_loop_data_def] >>
  drule_all abi_decoder_primitive_compiled_facts >> strip_tac >>
  drule_all abi_decoder_primitive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_inv_def]) >>
  drule_all abi_decoder_loop_inputs_eval >> strip_tac >>
  mp_tac (Q.INST [`next` |-> `st0.cs_next_var`] abi_decoder_loop_inputs_live) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_decoder_primitive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_primitive_loop_code _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_code_def]) >>
  qpat_assum `abi_decoder_primitive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_primitive_loop_data_def]) >>
  `opc = MLOAD ==> sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= d \/
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= sb` by metis_tac[] >>
  `mload (w2n (n2w slot:bytes32)) s = n2w j` by simp[w2n_n2w] >>
  `fresh_vars_wrt limit_st s` by fs[abi_decoder_loop_rel_def] >>
  drule_all abi_decoder_primitive_array_iteration_from_state >> strip_tac >>
  qpat_x_assum `!cx. frag_exec cx _ _ _ _ _` (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx fn s u` >>
  `abi_decoder_loop_rel first limit_st fp s u` by
    (mp_tac (Q.INST [`next` |-> `st0.cs_next_var`, `s` |-> `s:venom_state`,
       `t` |-> `u:venom_state`] abi_decoder_primitive_body_rel) >> simp[]) >>
  `abi_decoder_loop_rel first limit_st fp initial u` by
    metis_tac[abi_decoder_loop_rel_trans] >>
  qexists_tac `u` >> simp[abi_decoder_primitive_body_end_def] >> metis_tac[]
QED
