Theory bodyPtrStructLitAssignFrame
Ancestors bodyPtrStructLitOwnershipControlFrame bodyPtrStructLitOwnershipLoops bodyPtrStructLitTypedShape bodyPtrStructLitStmtSuffixFrame bodyPtrStructLitEmitterFrame
  bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipTyped
  bodyPtrStructLitOwnershipLocations bodyPtrStructLitLoopShapeCopy
  bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  loweringShapeProps loweringShapeDefs loweringShapeRules stmtLowering
  context compileEnv venomInst unitShapeDefs

Theorem alloc_run_assign_normalize_frame:
  shape_stable R /\ (normalize ==> dt <> st) ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src)
    (if normalize then
       do b <- compile_alloc_buffer bytes;
          compile_store_memory_typed ce b.buf_operand dt src st;
          return b.buf_operand od
     else return src)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> Cases_on `normalize` >> gvs[]
  >- (irule alloc_run_bind >>
      qexists `\b s. shape_state s /\ (R s /\ plain_operand s src) /\
        plain_operand s b.buf_operand` >> reverse conj_tac
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_alloc_buffer_frame >>
          qexists `\s. R s /\ plain_operand s src` >>
          simp[shape_stable_conj,
            SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
      qx_gen_tac `b` >> BETA_TAC >> simp[comp_ignore_bind_def] >>
      irule alloc_run_bind >>
      qexists `\u s. shape_state s /\ R s /\ plain_operand s b.buf_operand` >>
      reverse conj_tac
      >- (irule alloc_run_conseq >>
          irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
          irule_at Any structlit_typed_store_unequal_shape >>
          irule_at Any alloc_run_compile_store_memory_typed >>
          qexists `\s. R s /\ plain_operand s b.buf_operand` >>
          simp[shape_stable_conj,
            SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_assign_bulk_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s src /\ plain_operand s dst)
    (if loc = LocCode then compile_imm_store_words ce.ce_imm_alloca src dst n off
     else do (if loc = LocTransient then compile_memory_to_transient src dst n
              else compile_memory_to_storage src dst n); return () od)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> Cases_on `loc = LocCode` >> simp[]
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
      irule_at Any compile_imm_store_words_shape >>
      irule_at Any alloc_run_compile_imm_store_words >> qexists `R` >> simp[]) >>
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce` >>
  conj_tac >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  Cases_on `loc = LocTransient` >> simp[] >>
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  qexistsl [`\s. R s /\ cenv_shape_ok s ce`, `\u s. T`,
    `\s. plain_operand s src /\ plain_operand s dst`] >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    alloc_run_compile_memory_to_storage, alloc_run_compile_memory_to_transient,
    compile_memory_to_storage_def, compile_memory_to_transient_def,
    loop_shape_word_copy]
QED

Theorem alloc_run_assign_loaded_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s src)
    (do v <- emit_op MLOAD [src];
        compile_store_at_loc ce.ce_imm_alloca dst v (SOME loc) od)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ (R s /\ cenv_shape_ok s ce /\
    plain_operand s dst) /\ plain_operand s v` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_op_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s dst` >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)] >>
      rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >> simp[] >>
      metis_tac[]) >>
  gen_tac >> BETA_TAC >> irule alloc_run_conseq >>
  irule_at Any alloc_run_compile_store_at_loc_frame >> qexists `R` >> simp[]
QED

Theorem alloc_run_assign_suffix_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s src)
    (if prim then compile_store_at_loc ce.ce_imm_alloca dst src (SOME loc)
     else if loc = LocCode then
       (if bytes <= 32 then
          do v <- emit_op MLOAD [src];
             compile_store_at_loc ce.ce_imm_alloca dst v (SOME loc) od
        else compile_imm_store_words ce.ce_imm_alloca src dst
          ((bytes + 31) DIV 32) 0)
     else case da of
       SOME (ew, ems) => compile_dynarray_to_storage src dst ew ems (loc = LocTransient)
     | NONE => if bytes <= 32 then
          do v <- emit_op MLOAD [src];
             compile_store_at_loc ce.ce_imm_alloca dst v (SOME loc) od
        else do (if loc = LocTransient then compile_memory_to_transient src dst (bytes DIV 32)
                 else compile_memory_to_storage src dst (bytes DIV 32)); return () od)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> Cases_on `prim` >> simp[alloc_run_compile_store_at_loc_frame] >>
  Cases_on `loc = LocCode` >> simp[]
  >- (Cases_on `bytes <= 32` >> simp[alloc_run_assign_loaded_frame] >>
      irule alloc_run_conseq >>
      irule_at Any (SRULE [] (Q.INST [`loc` |-> `LocCode`] alloc_run_assign_bulk_frame)) >>
      qexists `R` >> simp[]) >>
  Cases_on `da`
  >- (simp[] >> Cases_on `bytes <= 32` >> simp[alloc_run_assign_loaded_frame] >>
      Cases_on `loc = LocTransient` >> simp[] >>
      irule alloc_run_conseq >>
      FIRST [irule_at Any (SRULE [] (Q.INST [`loc` |-> `LocTransient`] alloc_run_assign_bulk_frame)),
        irule_at Any (SRULE [] (Q.INST [`loc` |-> `LocStorage`] alloc_run_assign_bulk_frame))] >>
      qexistsl [`ce`, `R`] >> simp[]) >>
  PairCases_on `x` >> simp[] >> irule alloc_run_conseq >>
  irule_at Any alloc_run_compile_dynarray_to_storage_frame >> qexistsl [`ce`, `R`] >> simp[]
QED

Theorem alloc_run_assign_normalize_bind:
  shape_stable R /\ (normalize ==> dt <> st) /\
  (!v. alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s v) (k v) Q) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s src)
    (comp_bind (if normalize then
       do b <- compile_alloc_buffer bytes;
          compile_store_memory_typed ce b.buf_operand dt src st;
          return b.buf_operand od
     else return src) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s v` >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_assign_normalize_frame >>
  qexists `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s dst` >>
  simp[shape_stable_conj, cenv_shape_ok_stable,
    SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands)]
QED

Theorem alloc_run_compile_assign_value_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s src)
    (compile_assign_value ce dst loc src prim NONE dt st da bytes)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> Cases_on `loc` >> simp[Once compile_assign_value_def]
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> suspend "calldata"
QED

Resume alloc_run_compile_assign_value_frame[memory]:
  Cases_on `prim` >> simp[]
  >- (irule alloc_run_conseq >>
      irule_at Any (SRULE [compile_store_at_loc_def]
        (Q.INST [`loc` |-> `SOME LocMemory`] alloc_run_compile_store_at_loc_frame)) >>
      qexistsl [`ce`, `R`] >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_store_memory_frame >>
  qexists `\s. R s /\ cenv_shape_ok s ce` >>
  simp[shape_stable_conj, cenv_shape_ok_stable]
QED

Resume alloc_run_compile_assign_value_frame[calldata]:
  simp[comp_ignore_bind_def] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce` >>
  conj_tac >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_emit_inst_frame >>
  qexistsl [`F`, `\s. R s /\ cenv_shape_ok s ce`] >>
  simp[shape_stable_conj, cenv_shape_ok_stable, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def]
QED

Resume alloc_run_compile_assign_value_frame[storage]:
  irule alloc_run_assign_normalize_bind >> simp[] >>
  gen_tac >> BETA_TAC >> irule alloc_run_conseq >>
  irule_at Any (SRULE [compile_store_at_loc_def]
    (Q.INST [`loc` |-> `LocStorage`] alloc_run_assign_suffix_frame)) >>
  qexistsl [`ce`, `R`] >> simp[]
QED
Resume alloc_run_compile_assign_value_frame[transient]:
  irule alloc_run_assign_normalize_bind >> simp[] >>
  gen_tac >> BETA_TAC >> irule alloc_run_conseq >>
  irule_at Any (SRULE [compile_store_at_loc_def]
    (Q.INST [`loc` |-> `LocTransient`] alloc_run_assign_suffix_frame)) >>
  qexistsl [`ce`, `R`] >> simp[]
QED
Resume alloc_run_compile_assign_value_frame[code]:
  irule alloc_run_assign_normalize_bind >> simp[] >>
  gen_tac >> BETA_TAC >> irule alloc_run_conseq >>
  irule_at Any (SRULE [compile_store_at_loc_def]
    (Q.INST [`loc` |-> `LocCode`] alloc_run_assign_suffix_frame)) >>
  qexists `R` >> simp[]
QED
Finalise alloc_run_compile_assign_value_frame
