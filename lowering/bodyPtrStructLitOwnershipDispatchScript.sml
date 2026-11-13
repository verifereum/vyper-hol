Theory bodyPtrStructLitOwnershipDispatch
Ancestors
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipControlFrame
  bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipShape
  loweringShapeProps loweringShapeRules loweringShapeDefs moduleLowering compileEnv context

Theorem alloc_run_compile_entry_checks_fresh:
  alloc_run fresh_outputs (compile_entry_checks min_cds payable)
    (\u s. fresh_outputs s)
Proof
  simp[compile_entry_checks_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >> conj_tac
  >- (gen_tac >> simp[] >> Cases_on `min_cds > 4`
      >- (simp[] >> ntac 3
          (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
           reverse conj_tac
           >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
           gen_tac >> simp[]) >>
          simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  Cases_on `payable`
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[] >> ntac 2
    (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
     reverse conj_tac
     >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
     gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_entry_checks_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s) (compile_entry_checks min_cds payable)
    (\u s. shape_state s /\ R s /\ fresh_outputs s)
Proof
  strip_tac >>
  `alloc_run shape_state (compile_entry_checks min_cds payable)
     (\u s. fresh_outputs s)` by
    (irule alloc_run_conseq >> irule_at Any alloc_run_compile_entry_checks_fresh >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
  irule_at Any compile_entry_checks_shape >> simp[SF ETA_ss] >>
  goal_assum (drule_at Any) >> qexists `R` >> simp[]
QED

Theorem alloc_run_compile_selector_checks_fresh:
  !sels method_id.
  alloc_run fresh_outputs (compile_selector_checks method_id sels)
    (\u s. fresh_outputs s)
Proof
  Induct >> simp[compile_selector_checks_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[compile_selector_checks_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
            SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
    gen_tac >> simp[]) >> simp[SF ETA_ss] >> first_x_assum (irule o SRULE [SF ETA_ss])
QED

Theorem alloc_run_compile_selector_dispatch_linear_fresh:
  alloc_run fresh_outputs (compile_selector_dispatch_linear sels fb)
    (\u s. fresh_outputs s)
Proof
  simp[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_empty_fresh,
            SRULE [SF ETA_ss] alloc_run_new_block_fresh,
            SRULE [SF ETA_ss] alloc_run_compile_selector_checks_fresh] >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_empty_fresh]
QED

Theorem alloc_run_compile_selector_dispatch_linear:
  EVERY (\(sel,lbl). isPREFIX "fn_" lbl) sels /\
  jump_label_ok fb /\ ~label_sfx "dispatch" fb ==>
  alloc_run shape_state (compile_selector_dispatch_linear sels fb)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any alloc_run_compile_selector_dispatch_linear_fresh >>
  irule_at Any compile_selector_dispatch_linear_shape >>
  simp[shape_state_def, shape_base_fresh_outputs] >>
  gvs[listTheory.EVERY_MEM, pairTheory.FORALL_PROD, jump_label_ok_def] >> metis_tac[]
QED
