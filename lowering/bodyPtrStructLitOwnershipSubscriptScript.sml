Theory bodyPtrStructLitOwnershipSubscript
Ancestors bodyPtrStructLitOwnershipSubscriptTails bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeProps exprLowering compileEnv context

Theorem alloc_run_compile_subscript:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. T) /\
  (!ity. shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ity idx_e) (\v s. value_shape_ok s v)) /\
  (!ity. alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ity idx_e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_subscript cfn ce rt ty base_e idx_e) (\v s. T)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >> simp[shape_stable_def]) >>
  qx_gen_tac `base_vv` >> simp[] >> Cases_on `place_type ce base_e`
  >- suspend "map" >> suspend "value"
QED

Resume alloc_run_compile_subscript[map]:
  rename1 `place_type ce base_e = MapPT kt vt` >>
  simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
      qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
      metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (Cases_on `is_bytestring_type kt` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_keccak256_key,
        SRULE [SF ETA_ss] alloc_run_compile_mapping_subscript] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> rpt gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_compile_subscript[value]:
  rename1 `place_type ce base_e = ValPT bt` >> Cases_on `bt` >> simp[]
  >>~- ([`compile_tuple_subscript`],
     irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_tuple_subscript >>
          simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
   >- (irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
       qexistsl [`internal`, `\s. T`] >> simp[shape_stable_def] >>
       metis_tac[shape_state_def, shape_base_fresh_outputs])) >>
  gen_tac >> simp[] >>
  (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
   >- (simp[SF ETA_ss] >>
       irule (SRULE [SF ETA_ss] alloc_run_compile_array_subscript) >>
       simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_ptr_load])) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Finalise alloc_run_compile_subscript

Theorem alloc_run_expr_subscript:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ty base_e) (\v s. T) /\
  (!ity. shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ity idx_e) (\v s. value_shape_ok s v)) /\
  (!ity. alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (cfn ce ity idx_e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (Subscript rt base_e idx_e)) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_compile_subscript >> simp[] >> qexists `internal` >> simp[]
QED
