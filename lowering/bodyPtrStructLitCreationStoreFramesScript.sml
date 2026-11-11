Theory bodyPtrStructLitCreationStoreFrames
Ancestors bodyPtrStructLitEmitterFrame bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps
  exprLowering context compileEnv list

Theorem alloc_run_extcall_store_one_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s dst /\ plain_operand s src)
    (if is_word_type ty then emit_void MSTORE [dst; src]
     else if is_bytestring_type ty then compile_store_bytestring src dst
     else emit_void MCOPY [dst; src; Lit (n2w (type_memory_bytes ce ty))])
    (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >> Cases_on `is_word_type ty` >> simp[]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_void_frame >>
      qexists `R` >>
      simp[SRULE [stackPlanTypesTheory.is_label_operand_def]
        (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >> rpt strip_tac >>
      irule (cj 2 plain_data_inst_ok) >> simp[] >> qexists `s` >> simp[]) >>
  Cases_on `is_bytestring_type ty` >> simp[]
  >- (mp_tac (Q.INST [`dt` |-> `ty`, `st` |-> `ty`]
        alloc_run_store_memory_frame) >> simp[compile_store_memory_def]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_void_frame >>
      qexists `R` >>
      simp[SRULE [stackPlanTypesTheory.is_label_operand_def]
        (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >> rpt strip_tac >>
  irule (cj 2 plain_data_inst_ok) >> simp[] >> qexists `s` >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Theorem shape_stable_value_shapes:
  shape_stable (\s. EVERY (value_shape_ok s) vs)
Proof
  Induct_on `vs` >> simp[shape_stable_conj, value_shape_ok_stable] >>
  simp[shape_stable_def]
QED

Theorem alloc_run_extcall_store_values_frame:
  !vals buf off R. shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s buf /\ EVERY (value_shape_ok s) (MAP FST vals))
    (compile_extcall_store_values ce vals buf off)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s buf)
Proof
  Induct
  >- simp[compile_extcall_store_values_def, comp_return_def, alloc_run_def,
      alloc_frame_refl] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >> strip_tac >>
  simp[compile_extcall_store_values_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\dst s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
     value_shape_ok s head0 /\ EVERY (value_shape_ok s) (MAP FST vals)) /\
    plain_operand s dst` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_address_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
        value_shape_ok s head0 /\ EVERY (value_shape_ok s) (MAP FST vals)` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, value_shape_ok_stable,
        shape_stable_value_shapes,
        SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)]) >>
  qx_gen_tac `dst` >> simp[] >> irule alloc_run_bind >>
  qexists `\src s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
     EVERY (value_shape_ok s) (MAP FST vals) /\ plain_operand s dst) /\
    plain_operand s src` >> reverse conj_tac
  >- suspend "unwrap" >>
  qx_gen_tac `src` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s buf /\ EVERY (value_shape_ok s) (MAP FST vals)` >>
  reverse conj_tac >- suspend "store" >>
  gen_tac >> simp[] >> first_x_assum irule >> simp[]
QED

Resume alloc_run_extcall_store_values_frame[unwrap]:
  irule alloc_run_conseq >> irule_at Any alloc_run_unwrap_value_frame >>
  qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
    EVERY (value_shape_ok s) (MAP FST vals) /\ plain_operand s dst` >>
  simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_value_shapes,
    SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands),
    SRULE [] (Q.SPEC `[dst]` shape_stable_plain_operands)]
QED

Resume alloc_run_extcall_store_values_frame[store]:
  irule alloc_run_conseq >> irule_at Any alloc_run_extcall_store_one_frame >>
  qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf /\
    EVERY (value_shape_ok s) (MAP FST vals)` >>
  simp[shape_stable_conj, cenv_shape_ok_stable, shape_stable_value_shapes,
    SRULE [] (Q.SPEC `[buf]` shape_stable_plain_operands)]
QED

Finalise alloc_run_extcall_store_values_frame
