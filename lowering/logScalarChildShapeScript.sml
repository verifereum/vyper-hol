(* Public straight-line compiler boundary for scalar tuple children. *)
Theory logScalarChildShape
Ancestors
  stmtSimLogEncodeFields stmtSimLogEncodeLayout stmtSimLogExecFields
  abiEncoderBytesCode abiEncoderChildCode abiDecoderArrayInit
  emitHelperProps exprLoweringProps compileEnv venomInst list

Theorem log_scalar_core_straight:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\ log_scalar_enc_info ei ==>
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  simp_tac bool_ss [log_scalar_enc_info_def] >> strip_tac >> gvs[]
  >- (drule log_encode_copy_safe >> strip_tac >> conj_tac
      >- first_assum ACCEPT_TAC >>
      fs[EVERY_MEM] >> gen_tac >> disch_tac >>
      qpat_x_assum `!i. MEM i _ ==> log_encode_safe_opcode _` drule >>
      simp_tac bool_ss [log_encode_safe_opcode_def] >> strip_tac >> gvs[is_terminator_def]) >>
  drule abi_encode_bytes_shape >> strip_tac >> conj_tac
  >- first_assum ACCEPT_TAC >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem log_scalar_child_straight:
  compile_abi_encode_child dst src ei dyn ho dp st = (out,final) /\ log_scalar_enc_info ei ==>
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  strip_tac >> reverse (Cases_on `dyn`)
  >- (drule abi_encode_static_child_trace >> strip_tac >>
      drule_all log_scalar_core_straight >> strip_tac >>
      drule inst_extends_emit_op >> strip_tac >>
      conj_tac >- (irule inst_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
      irule abi_decoder_emitted_every_append >> goal_assum (drule_at Any) >>
      asm_simp_tac bool_ss [] >> drule emitted_insts_emit_op >>
      simp[mk_inst_def, is_terminator_def]) >>
  drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule_all log_scalar_core_straight >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  `inst_extends st child_end` by
    (irule inst_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (irule inst_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  irule abi_decoder_emitted_every_append >> qexists_tac `child_end` >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- suspend "prefix" >>
  asm_simp_tac bool_ss []
QED
Resume log_scalar_child_straight[prefix]:
  irule abi_decoder_emitted_every_append >> qexists_tac `prepared` >>
  fs[EVERY_MEM] >> metis_tac[]
QED
Finalise log_scalar_child_straight
