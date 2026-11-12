Theory bodyPtrStructLitCreationCopyFrames
Ancestors bodyPtrStructLitCreationShape bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitEmitterFrame bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipLocations
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps exprLowering context compileEnv

Theorem alloc_run_create_slot_copy_frame:
  shape_stable R /\ (loc = LocStorage \/ loc = LocTransient) ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src /\ plain_operand s dst)
    (compile_slot_to_memory src dst n loc) (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_slot_to_memory, create_slot_to_memory_shape]
QED

Theorem alloc_run_create_memory_copy_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s dst /\ plain_operand s src /\ plain_operand s len)
    (compile_copy_memory_dynamic dst src len) (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_copy_memory_dynamic, create_copy_memory_dynamic_shape]
QED

Theorem alloc_run_create_code_copy_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s src /\ plain_operand s dst)
    (compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src dst n off)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      plain_operand s src /\ plain_operand s dst)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_imm_copy_to_memory, compile_imm_copy_to_memory_shape]
QED

Theorem alloc_run_create_bytes_copy_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\
      plain_operand s dst /\ plain_operand s src)
    (do len <- emit_op MLOAD [src];
        size <- emit_op ADD [len; Lit 32w];
        compile_copy_memory_dynamic dst src size od)
    (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >>
  rpt (ho_match_mp_tac alloc_run_op_bind >>
    simp[SRULE [stackPlanTypesTheory.is_label_operand_def]
      (Q.INST [`op` |-> `Lit w`] (SPEC_ALL plain_operand_def))] >>
    (conj_tac >- (rpt (ho_match_mp_tac shape_stable_conj >> conj_tac) >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)])) >>
    (conj_tac >- (rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[plain_operand_def,
        stackPlanTypesTheory.is_label_operand_def])) >> rpt gen_tac) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_create_memory_copy_frame >>
  qexists `R` >> simp[]
QED

Theorem alloc_run_compile_create_snapshot:
  alloc_run fresh_outputs (compile_create_snapshot ce vv ty) (\v s. fresh_outputs s)
Proof
  simp[compile_create_snapshot_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[alloc_run_compile_alloc_buffer] >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. fresh_outputs s` >> reverse conj_tac
  >- (Cases_on `vv_location vv` >>
      TRY (rename1 `_ = SOME loc` >> Cases_on `loc`) >> simp[] >>
      (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
        reverse conj_tac
        >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_slot_to_memory,
            SRULE [SF ETA_ss] alloc_run_compile_imm_copy_to_memory] >>
        gen_tac >> simp[]) >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_copy_memory_dynamic] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl])) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
