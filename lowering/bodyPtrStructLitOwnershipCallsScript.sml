Theory bodyPtrStructLitOwnershipCalls
Ancestors bodyPtrStructLitOwnershipCallFrames bodyPtrStructLitOwnershipCallStaging
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipCallSuffix
  bodyPtrStructLitOwnershipShape
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering compileEnv context list rich_list pair gasShadowCompileBase
  venomInst unitShapeDefs stackPlanTypes

Theorem comp_bind_constant_pair[local]:
  comp_bind ($, v) k = k v
Proof
  simp[FUN_EQ_THM, comp_bind_def]
QED

Theorem alloc_run_call_invalid:
  ct = RawLog \/ ct = RawRevert \/ ct = SelfDestructTarget ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty ct args dr) (\v s. fresh_outputs s)
Proof
  strip_tac >> gvs[] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_call_internal:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (IntCall fid) args dr) (\v s. fresh_outputs s)
Proof
  strip_tac >>
  namedCases_on `ce.ce_func_info (nsid_to_string fid)` ["rc bs pvs"] >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\vs s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_multi_vvs_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  qx_gen_tac `vs` >> simp[] >>
  Cases_on `rc' > 0` >> simp[] >>
  TRY (rename1 `~(rc' > 0)` >> Cases_on `bs > 0` >> simp[]) >>
  simp[GSYM comp_bind_def, comp_bind_uncurry, comp_bind_assoc, SF ETA_ss] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_compile_stage_intcall_args,
        SRULE [SF ETA_ss] alloc_run_emit_multi_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss] alloc_run_store_multi_results] >>
    gen_tac >> simp[comp_bind_constant_pair, SF ETA_ss]) >>
  simp[alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_call_external:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (ExtCall static skip (name, ats, rty) opts) args dr)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `args`
  >- suspend "invalid" >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `addr` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_multi_vvs_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[MEM_TAKE, MEM]) >>
  qx_gen_tac `vals` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_ext_call_kwargs_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >> conj_tac
      >- metis_tac[MEM_DROP_IMP, MEM] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  qx_gen_tac `kwargs` >> PairCases_on `kwargs` >> simp[] >> suspend "suffix"
QED

Resume alloc_run_call_external[invalid]:
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_call_external[suffix]:
  namedCases_on `kwargs2` ["", "dp"] >> TRY (PairCases_on `dp`) >>
  Cases_on `kwargs1` >>
  simp[GSYM comp_bind_def, comp_bind_uncurry, SF ETA_ss] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_external_call_kwargs] >>
    gen_tac >> simp[]) >>
  simp[alloc_run_def, alloc_frame_refl] >> rpt strip_tac >> gvs[] >>
  Cases_on `abi_size_bound ce.ce_struct_fields
    (if needs_external_call_wrap rty then TupleT [rty] else rty) = 0` >>
  gvs[alloc_frame_refl])
QED

Finalise alloc_run_call_external

Theorem alloc_run_call_send_invalid[local]:
  (!a v gs. args = a::v::gs ==> LENGTH gs <> (if has_gas then 1 else 0)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (Send has_gas) args dr) (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "addr restargs"] >>
  TRY (namedCases_on `restargs` ["", "value gases"]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_call_send:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (Send has_gas) args dr) (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "addr restargs"]
  >- simp[alloc_run_call_send_invalid] >>
  namedCases_on `restargs` ["", "value gases"]
  >- simp[alloc_run_call_send_invalid] >>
  Cases_on `LENGTH gases = (if has_gas then 1 else 0)`
  >- (namedCases_on `gases` ["", "gas tailgas"] >>
      TRY (Cases_on `tailgas`) >> Cases_on `has_gas` >> gvs[] >>
      GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
      simp[compile_call_def, GSYM comp_bind_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
      (rpt (irule alloc_run_bind >>
        qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
        >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
            qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
        gen_tac >> simp[comp_bind_uncurry, SF ETA_ss]) >>
      irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op_fresh >>
          simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
      gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
      reverse conj_tac
      >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[alloc_run_def, alloc_frame_refl])) >>
  irule alloc_run_call_send_invalid >> simp[]
QED

Theorem alloc_run_call_raw_calldata:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (RawCallCalldataTarget rcf) args dr)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "addr kws"]
  >- suspend "invalid" >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `addr_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_ext_call_kwargs_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >> simp[] >> suspend "suffix"
QED

Resume alloc_run_call_raw_calldata[invalid]:
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_call_raw_calldata[suffix]:
  Cases_on `kw1` >> simp[GSYM comp_bind_def, comp_bind_uncurry,
    comp_bind_constant_pair, SF ETA_ss] >>
  (TRY (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_raw_call_outbuf] >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_msg_data_to_memory] >>
  qx_gen_tac `dat` >> PairCases_on `dat` >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_raw_call_finish] >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[alloc_run_def, alloc_frame_refl] >> rpt strip_tac >> gvs[] >>
  Cases_on `rcf.rcf_max_outsize = 0` >> gvs[alloc_frame_refl])
QED

Finalise alloc_run_call_raw_calldata

Theorem alloc_run_call_raw:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_call cfn ce rt ty (RawCallTarget rcf) args dr)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "addr rest"]
  >- suspend "invalid_empty" >>
  namedCases_on `rest` ["", "data kws"]
  >- suspend "invalid_one" >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `addr_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `data_op` >> simp[] >> suspend "loads"
QED

Resume alloc_run_call_raw[invalid_empty]:
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_call_raw[invalid_one]:
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_call_def, GSYM comp_bind_def] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_call_raw[loads]:
  Cases_on `is_label_operand data_op`
  >- simp[alloc_run_def, plain_operand_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s data_op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_op_shape_probe) >>
      qexists `\s. cenv_shape_ok s ce /\ plain_operand s data_op` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[data_op]` shape_stable_plain_operands),
        label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, label_positions_ok_def, is_terminator_def,
        is_read0_opcode_def, jump_label_ok_def, shape_state_def]) >>
  qx_gen_tac `data_len` >> simp[] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_op_shape_probe) >>
      qexists `\s. cenv_shape_ok s ce` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        label_or_plain_def, plain_operand_def, is_label_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, label_positions_ok_def,
        is_terminator_def, is_read0_opcode_def, jump_label_ok_def, shape_state_def]) >>
  qx_gen_tac `data_ptr` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_ext_call_kwargs_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  qx_gen_tac `kw` >> PairCases_on `kw` >> simp[] >> suspend "suffix"
QED

Resume alloc_run_call_raw[suffix]:
  Cases_on `kw1` >> simp[GSYM comp_bind_def, comp_bind_uncurry,
    comp_bind_constant_pair, SF ETA_ss] >>
  (TRY (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
    gen_tac >> simp[]) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_raw_call_outbuf] >>
  qx_gen_tac `out` >> PairCases_on `out` >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_raw_call_finish] >>
  simp[alloc_run_def, alloc_frame_refl] >> rpt strip_tac >> gvs[] >>
  Cases_on `rcf.rcf_max_outsize = 0` >> gvs[alloc_frame_refl])
QED

Finalise alloc_run_call_raw
