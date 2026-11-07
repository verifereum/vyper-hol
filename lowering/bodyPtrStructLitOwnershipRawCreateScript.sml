Theory bodyPtrStructLitOwnershipRawCreate
Ancestors bodyPtrStructLitAbiEncodeFrame bodyPtrStructLitCreationFrames
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipCreateCalls bodyPtrStructLitEmitterFrame
  bodyPtrStructLitOwnershipCalls
  bodyPtrStructLitCreationCopyFrames bodyPtrStructLitOwnershipCallSuffix
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFrame
  bodyPtrStructLitOwnershipStructFrame
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering builtinCreate compileEnv context list pair rich_list

Theorem alloc_run_raw_create_ctor_prefix:
  shape_stable R /\
  (!e. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce (expr_type e) e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s data /\ plain_operand s len)
    (do buf <- compile_alloc_buffer cap;
        compile_copy_memory_dynamic buf.buf_operand data len;
        src <- compile_create_ctor_tuple cfn ce args;
        dst <- emit_op ADD [buf.buf_operand; len];
        args_len <- compile_abi_encode_to_buf dst src enc_info;
        total <- emit_op ADD [len; args_len];
        comp_return (buf.buf_operand,total)
     od)
    (\p s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s (FST p) /\ plain_operand s (SND p))
Proof
  strip_tac >> simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ (R s /\ cenv_shape_ok s ce /\
    plain_operand s data /\ plain_operand s len) /\ plain_operand s b.buf_operand` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  qx_gen_tac `buf` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s len /\ plain_operand s buf.buf_operand` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_memory_copy_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s len /\
        plain_operand s buf.buf_operand` >> simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (R s /\ plain_operand s len /\
    plain_operand s buf.buf_operand) /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_ctor_tuple_frame >>
      qexists `\s. R s /\ plain_operand s len /\ plain_operand s buf.buf_operand` >>
      simp[shape_stable_conj]) >>
  qx_gen_tac `src` >> simp[] >> suspend "encode"
QED

Resume alloc_run_raw_create_ctor_prefix[encode]:
  ho_match_mp_tac alloc_run_op_bind >> simp[GSYM CONJ_ASSOC] >>
  conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable]) >>
  conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
    simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `dst` >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s len /\ plain_operand s buf.buf_operand) /\
    plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_abi_encode_to_buf_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s len /\
        plain_operand s buf.buf_operand` >> simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  qx_gen_tac `args_len` >> simp[] >>
  ho_match_mp_tac alloc_run_op_bind >> simp[GSYM CONJ_ASSOC] >>
  conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
    simp[cenv_shape_ok_stable]) >>
  conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
    simp[] >> qexists `s` >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Finalise alloc_run_raw_create_ctor_prefix

Theorem alloc_run_compile_raw_create:
  (!e t. MEM e (bytecode_e::value_e::args) \/ salt_e = SOME e ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_raw_create cfn ce bytecode_e value_e args salt_e rof)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_raw_create_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_struct_child_frame) >>
      qexistsl [`ce`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `vv` >> simp[] >> suspend "snapshot"
QED

Resume alloc_run_compile_raw_create[snapshot]:
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_snapshot_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      Cases_on `vv` >> simp[value_shape_ok_def, vv_operand_def]) >>
  qx_gen_tac `bytecode` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (plain_operand s bytecode) /\
    cenv_shape_ok s ce /\ plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. plain_operand s bytecode`] >> simp[]) >>
  qx_gen_tac `value_op` >> simp[] >>
  ho_match_mp_tac alloc_run_op_bind >> simp[GSYM CONJ_ASSOC] >>
  conj_tac >- simp[shape_stable_conj, cenv_shape_ok_stable] >>
  conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
    simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `len` >>
  ho_match_mp_tac alloc_run_op_bind >> simp[GSYM CONJ_ASSOC] >>
  conj_tac >- simp[shape_stable_conj, cenv_shape_ok_stable] >>
  conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
    simp[] >> qexists `s` >> simp[]) >>
  qx_gen_tac `data` >> suspend "constructor"
QED

Resume alloc_run_compile_raw_create[constructor]:
  irule alloc_run_bind >>
  qexists `\p s. shape_state s /\ plain_operand s value_op /\ cenv_shape_ok s ce /\
    plain_operand s (FST p) /\ plain_operand s (SND p)` >> reverse conj_tac
  >- (Cases_on `args = []` >> simp[]
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
      irule alloc_run_conseq >> irule_at Any (SRULE [comp_ignore_bind_def] alloc_run_raw_create_ctor_prefix) >>
      qexists `\s. plain_operand s value_op` >> simp[]) >>
  qx_gen_tac `p` >> PairCases_on `p` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_salt_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_create_dispatch]
QED

Finalise alloc_run_compile_raw_create

Theorem alloc_run_create_call_raw:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_create_call cfn ce RawCreate has_salt rof args) (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "target es"]
  >- suspend "empty" >> namedCases_on `es` ["", "value rest"]
  >- suspend "single" >>
  Cases_on `LENGTH rest < (if has_salt then 1 else 0)`
  >- suspend "short" >>
  simp[compile_create_call_def] >> irule alloc_run_compile_raw_create >>
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  Cases_on `has_salt` >> gvs[] >>
  metis_tac[MEM_FRONT_NOT_NIL, MEM_LAST_NOT_NIL, LENGTH_NIL]
QED

Resume alloc_run_create_call_raw[empty]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_create_call_raw[single]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_create_call_raw[short]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Finalise alloc_run_create_call_raw

Theorem alloc_run_create_call:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_create_call cfn ce ck has_salt rof args) (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `ck = RawCreate`
  >- (gvs[] >> irule alloc_run_create_call_raw >> simp[]) >>
  irule alloc_run_create_call_nonraw >> simp[]
QED

Theorem alloc_run_call_create:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (CreateTarget ck has_salt rof extra) args dr)
    (\v s. fresh_outputs s)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def] >> drule_all alloc_run_create_call >>
  simp[alloc_run_def, oneline as_stack_val_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem alloc_run_compile_call:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty ct args dr) (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `ct` >>
  simp[alloc_run_call_internal, alloc_run_call_send, alloc_run_call_raw,
    alloc_run_call_raw_calldata, alloc_run_call_create, alloc_run_call_invalid] >>
  PairCases_on `p` >> irule alloc_run_call_external >> simp[]
QED
