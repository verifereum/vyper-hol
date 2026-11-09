(* Straight-line execution preserves the block cursor; shared hash boundary. *)
Theory bodyPtrHashBuiltinsCursor
Ancestors exprSimHash venomExecSemantics venomState venomInst
  venomInstProps list
  exprLoweringProps bodyPtrHashBuiltinsKeccakFixedRun
  bodyPtrHashBuiltinsShaFixed bodyPtrHashBuiltinsShaBytes emitHelper compileEnv
  context rich_list

Theorem hash_run_inst_seq_current_bb:
  run_inst_seq insts s = OK t /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) insts ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb`
    run_inst_seq_preserves_field)) >>
  qexists_tac `insts` >> asm_rewrite_tac [] >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem hash_fixed_keccak_emitted_length:
  compile_keccak256_bytesm x m sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 3
Proof
  strip_tac >> drule hash_fixed_keccak_emission >> simp[]
QED

Theorem hash_fixed_sha256_emitted_length:
  compile_sha256_bytesm x m sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 7
Proof
  strip_tac >> drule hash_sha256_fixed_parts >> strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC]
QED

Theorem hash_dynamic_sha256_emitted_length:
  compile_sha256_bytes x sm = (op,sb) ==>
  LENGTH (emitted_insts sm sb) = 7
Proof
  strip_tac >> drule hash_sha256_bytes_parts >> strip_tac >>
  gvs[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
    APPEND_ASSOC]
QED

Theorem hash_sha256_success_cursor:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
     BaseT (BytesT (Fixed m)) => compile_sha256_bytesm x m sm
   | _ => compile_sha256_word x sm) = (op,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK t /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  (t with vs_inst_idx := s.vs_inst_idx+7).vs_current_bb = sb.cs_current_bb /\
  (t with vs_inst_idx := s.vs_inst_idx+7).vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all sha256_typed_suffix_shape >> strip_tac >>
  drule_all hash_run_inst_seq_current_bb >> strip_tac >>
  `LENGTH (emitted_insts sm sb) = 7` by
    (Cases_on `is_bytestring_type (expr_type e)` >> gvs[]
     >- metis_tac[hash_dynamic_sha256_emitted_length] >>
     Cases_on `bty` >> gvs[] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[]) >>
     metis_tac[hash_fixed_sha256_emitted_length,
       bodyPtrHashBuiltinsShaFixedTheory.hash_sha256_word_bytesm]) >>
  gvs[exprLoweringPropsTheory.same_blocks_def]
QED
