Theory bodyPtrStructLitOwnershipCreateCalls
Ancestors bodyPtrStructLitCreationFrames bodyPtrStructLitOwnershipCallSuffix
  bodyPtrStructLitOwnershipCalls bodyPtrStructLitOwnershipAbiEncode
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipIfexpFrame
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering builtinCreate compileEnv context list pair

Theorem alloc_run_create_blueprint_args:
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_create_blueprint_args cfn ce raw_args args) (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `raw_args`
  >- (namedCases_on `args` ["", "e es"]
      >- suspend "empty_raw" >>
      namedCases_on `es` ["", "e2 tail"]
      >- suspend "single_raw" >> suspend "many_raw") >>
  Cases_on `args = []`
  >- (gvs[compile_create_blueprint_args_def, comp_return_def, alloc_run_def,
        alloc_frame_refl] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_alloc_buffer_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_ctor_tuple_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_abi_encode_to_buf] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_blueprint_args[empty_raw]:
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_blueprint_args[many_raw]:
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_blueprint_args[single_raw]:
  simp[compile_create_blueprint_args_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >>
  ntac 2 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Finalise alloc_run_create_blueprint_args

Theorem alloc_run_create_call_nonraw:
  ck <> RawCreate /\
  (!e t. MEM e args ==>
    shape_step F compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_create_call cfn ce ck has_salt rof args) (\v s. fresh_outputs s)
Proof
  strip_tac >> namedCases_on `args` ["", "target es"]
  >- suspend "empty" >>
  namedCases_on `es` ["", "value rest"]
  >- suspend "single" >>
  Cases_on `LENGTH rest < (if has_salt then 1 else 0) +
    (case ck of CreateFromBlueprint _ => 1 | _ => 0)`
  >- suspend "short" >>
  simp[compile_create_call_def] >> Cases_on `ck` >> gvs[] >>
  (irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `target_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s target_op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. plain_operand s target_op`] >>
      simp[SRULE [] (Q.SPEC `[target_op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `value_op` >> simp[])
  >- suspend "proxy"
  >- suspend "copy" >> suspend "blueprint"
QED

Resume alloc_run_create_call_nonraw[empty]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_call_nonraw[single]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_call_nonraw[short]:
  simp[compile_create_call_def, comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
      simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_create_call_nonraw[proxy]:
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_proxy_buf_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_salt_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >> conj_tac
      >- (Cases_on `has_salt` >> Cases_on `rest` >> gvs[]) >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_create_dispatch]
QED
Resume alloc_run_create_call_nonraw[copy]:
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_salt_frame >>
      qexists `\s. T` >> simp[shape_stable_def] >> conj_tac
      >- (Cases_on `has_salt` >> Cases_on `rest` >> gvs[]) >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_create_copy]
QED
Resume alloc_run_create_call_nonraw[blueprint]:
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s target_op` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_salt_frame >>
      qexists `\s. plain_operand s target_op` >>
      simp[SRULE [] (Q.SPEC `[target_op]` shape_stable_plain_operands)] >>
      Cases_on `has_salt` >> Cases_on `rest` >> gvs[]) >>
  qx_gen_tac `salt` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\
    plain_operand s target_op /\ plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`F`, `\s. plain_operand s target_op`] >>
      simp[SRULE [] (Q.SPEC `[target_op]` shape_stable_plain_operands)] >>
      Cases_on `has_salt` >> namedCases_on `rest` ["", "h tail"] >> gvs[] >>
      namedCases_on `tail` ["", "h2 tail2"] >> gvs[]) >>
  qx_gen_tac `offset` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_create_blueprint_check_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `size_op` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_create_blueprint_args >>
      Cases_on `has_salt` >> namedCases_on `rest` ["", "h tail"] >> gvs[] >>
      namedCases_on `tail` ["", "h2 tail2"] >> gvs[] >> metis_tac[]) >>
  qx_gen_tac `dat` >> PairCases_on `dat` >> simp[] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_create_blueprint_append]
QED

Finalise alloc_run_create_call_nonraw

Theorem alloc_run_call_create_nonraw:
  ck <> RawCreate /\
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
  simp[compile_call_def] >>
  drule_all alloc_run_create_call_nonraw >>
  simp[alloc_run_def, oneline as_stack_val_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED
