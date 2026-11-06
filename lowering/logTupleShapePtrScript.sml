(* Compiler-only decomposition; runtime cursor ownership is handled separately. *)
Theory logTupleShapePtr
Ancestors
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode
  abiBuiltinAllocation abiDecoderTypedCompose stmtSimLogEncodeFields
  stmtSimLogEncodeLayout stmtSimLogExecFields
  emitHelperProps exprLoweringProps compileEnv context fragExec
  venomInst list rich_list words arithmetic

Theorem log_tuple_dynamic_phases:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,final) /\
  EXISTS (\(_,_,_,dyn). dyn) infos ==>
  ?cb a b ignored c dp result.
    compile_alloc_buffer 32 st = (cb,a) /\
    emit_void MSTORE [cb.buf_operand;
      Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))] a = ((),b) /\
    compile_abi_encode_complex_elems dst src infos 0 0 cb.buf_operand b = (ignored,c) /\
    emit_op MLOAD [cb.buf_operand] c = (out,final) /\
    cb.buf_operand = Var dp /\ out = Var result /\ cb.buf_size = 32 /\
    inst_extends st a /\ inst_extends a b /\ inst_extends c final /\
    cs_extends b c /\
    a.cs_next_id = st.cs_next_id + 1 /\
    b.cs_next_id = a.cs_next_id + 1 /\
    b.cs_next_id <= c.cs_next_id /\ final.cs_next_id = c.cs_next_id + 1 /\
    a.cs_next_var = st.cs_next_var + 1 /\
    b.cs_next_var = a.cs_next_var /\
    b.cs_next_var <= c.cs_next_var /\ final.cs_next_var = c.cs_next_var + 1
Proof
  strip_tac >> drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule abi_encoder_complex_prefix_trace >> strip_tac >> gvs[] >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac inst_extends_emit_op) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  drule inst_extends_emit_op >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule_all emitted_insts_emit_void >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

(* Straightness requires scalar members: arbitrary complex members may emit CFGs. *)
Theorem log_tuple_dynamic_code:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,final) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  abi_encode_complex_prefix infos st = (dp,b) /\
  compile_alloc_buffer 32 st = (cb,a) /\
  emit_void MSTORE [cb.buf_operand;
    Lit (n2w (SUM (MAP (\(_,asz,_,_). asz) infos)))] a = ((),b) /\
  compile_abi_encode_complex_elems dst src infos 0 0 dp b = (ignored,c) /\
  emit_op MLOAD [dp] c = (out,final) ==>
  inst_extends b c /\ inst_extends st final /\
  emitted_insts st final =
    emitted_insts st a ++ emitted_insts a b ++
    emitted_insts b c ++ emitted_insts c final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  strip_tac >> drule_all log_encode_dynamic_safe >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  `c.cs_blocks = b.cs_blocks` by fs[same_blocks_def] >>
  `inst_extends b c` by
    (irule abi_decoder_inst_extends_prefix >>
     qpat_x_assum `cs_extends b c` mp_tac >>
     simp[cs_extends_def] >> strip_tac >>
     `new = []` by (fs[] >> metis_tac[APPEND_11, APPEND_NIL]) >> gvs[]) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
      drule inst_extends_emit_op >> strip_tac >>
      drule inst_extends_emit_void >> strip_tac >>
      `emitted_insts st b = emitted_insts st a ++ emitted_insts a b` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      `inst_extends st c` by
        (irule inst_extends_trans >> qexists_tac `b` >> simp[]) >>
      `emitted_insts st final = emitted_insts st c ++ emitted_insts c final` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      `emitted_insts st c = emitted_insts st b ++ emitted_insts b c` by
        (irule emitted_insts_append >> fs[inst_extends_def]) >>
      simp[APPEND_ASSOC]) >>
  fs[EVERY_MEM] >> gen_tac >> disch_tac >>
  qpat_x_assum `!i. MEM i _ ==> log_encode_safe_opcode _` drule >>
  simp_tac bool_ss [log_encode_safe_opcode_def] >> strip_tac >> gvs[is_terminator_def]
QED
