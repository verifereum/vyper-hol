Theory bodyPtrStructLitOwnershipSliceCases
Ancestors bodyPtrStructLitOwnershipCalldataSlice
  bodyPtrStructLitOwnershipSliceTails bodyPtrStructLitOwnershipSlicePrefix
  bodyPtrStructLitOwnershipScratchFrame bodyPtrStructLitOwnershipBytesPrefix
  bodyPtrStructLitOwnershipIfexpFrame
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeRules
  loweringShapeProps exprLowering compileEnv context list pair gasShadowCompileBase

Theorem alloc_run_lower_value_then:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) (cfn ce ty e)
    (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T) /\
  (!v. alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v)
    (k v) (\w s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (comp_bind (lower_value cfn ce ty e) k) (\w s. T)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def]) >>
  simp[]
QED

Theorem alloc_run_as_ptr_tail:
  alloc_run fresh_outputs f (\v s. T) ==>
  alloc_run (\s. shape_state s /\ P s)
    (\s. as_ptr_val rt loc (f s)) (\v s. T)
Proof
  simp[alloc_run_def, oneline as_ptr_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `fresh_outputs s` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
  first_x_assum drule >> simp[]
QED

Theorem alloc_run_builtin_slice:
  3 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) /\
  (is_extcode (HD args) ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce ty (extcode_addr_expr (HD args))) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce ty (extcode_addr_expr (HD args))) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Slice n) args) (\v s. T)
Proof
  strip_tac >>
  `MEM (HD args) args /\ MEM (EL 1 args) args /\ MEM (EL 2 args) args` by
    (Cases_on `args` >> gvs[] >> Cases_on `t` >> gvs[] >>
     Cases_on `t'` >> gvs[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def] >>
  Cases_on `is_msg_data (HD args)` >- suspend "calldata" >>
  Cases_on `is_self_code (HD args)` >- suspend "code" >>
  Cases_on `is_extcode (HD args)` >- suspend "extcode" >>
  suspend "data"
QED

Resume alloc_run_builtin_slice[calldata]:
  simp[comp_bind_uncurry, SF ETA_ss] >>
  irule (Q.INST [`internal` |-> `internal`] alloc_run_lower_value_then) >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss, alloc_run_compile_slice_calldata]
QED

Resume alloc_run_builtin_slice[code]:
  simp[comp_bind_uncurry, SF ETA_ss] >>
  irule alloc_run_lower_value_then >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss, alloc_run_compile_slice_code]
QED

Resume alloc_run_builtin_slice[extcode]:
  simp[comp_bind_uncurry, SF ETA_ss] >>
  irule alloc_run_lower_value_then >>
  reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ cenv_shape_ok s ce /\
    EVERY (plain_operand s) [FST b; SND b]` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_slice_out_buf_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  Cases >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss, alloc_run_compile_slice_extcode]
QED

Resume alloc_run_builtin_slice[data]:
  simp[comp_bind_uncurry, SF ETA_ss] >>
  irule alloc_run_lower_value_then >> reverse conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >>
  Cases_on `is_bytestring_type (expr_type (HD args))` >> simp[]
  >- suspend "bytestring"
  >> suspend "fixed"
QED

Resume alloc_run_builtin_slice[bytestring]:
  simp[comp_bind_uncurry, SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ cenv_shape_ok s ce /\
    EVERY (plain_operand s) [FST b; SND b]` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_bytestring_src_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  Cases >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss, alloc_run_compile_slice_data]
QED

Resume alloc_run_builtin_slice[fixed]:
  simp[comp_bind_uncurry, SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ (cenv_shape_ok s ce /\ plain_operand s v) /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[v]` shape_stable_plain_operands)]) >>
  qx_gen_tac `buf` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ cenv_shape_ok s ce /\ T` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_mstore_frame >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_lower_value_then >>
  simp[] >> qexists `internal` >> conj_tac >- metis_tac[] >>
  gen_tac >> ho_match_mp_tac alloc_run_as_ptr_tail >>
  simp[SF ETA_ss, alloc_run_compile_slice_data]
QED

Finalise alloc_run_builtin_slice
