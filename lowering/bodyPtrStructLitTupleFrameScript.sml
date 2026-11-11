Theory bodyPtrStructLitTupleFrame
Ancestors bodyPtrStructLitAssignFrame bodyPtrStructLitOwnershipStmtHelpers
  bodyPtrStructLitOwnershipControlFrame bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipPop stmtLowering loweringShapeProps
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitCompilerOwnership
  bodyPtrStructLitStmtSuffixFrame loweringShapeRules loweringShapeDefs
  context compileEnv venomInst unitShapeDefs emitHelper stackPlanTypes
  supportedStmtTraverse
  bodyPtrStructLitLoopShapeDynBody list bodyPtrStructLitEmitterFrame
  bodyPtrStructLitOwnershipLocations bodyPtrStructLitOwnershipIfexpFrame

Theorem alloc_run_compile_tuple_store_one_frame:
  (!env ty child. supported_target_exists (\e. e = child) bt /\
      ~supported_expr_exists expr_shape_root child ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s env)
      (compile_expr env ty child) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
      (compile_expr env ty child) (\v s. T)) /\
  ~supported_target_exists expr_shape_root bt /\ shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s value)
    (compile_tuple_store_all ce [src_ty] [BaseTarget bt] [value])
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\r s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s value /\ plain_operand s (FST r)` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_target_prefix_frame >>
      qexistsl [`internal`, `\s. R s /\ plain_operand s value`] >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[value]` shape_stable_plain_operands)]) >>
  qx_gen_tac `r` >> simp[loop_comp_return_bind] >>
  rpt IF_CASES_TAC >> simp[] >>
  (irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      FIRST [irule_at Any alloc_run_compile_store_at_loc_frame,
        irule_at Any alloc_run_compile_assign_value_frame,
        irule_at Any (SRULE [emit_inst_def, GSYM emit_void_def]
          (Q.INST [`internal` |-> `F`, `outs` |-> `[]`] alloc_run_emit_inst_frame))] >>
      qexists `\s. R s /\ cenv_shape_ok s ce` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, emit_void_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
        label_positions_ok_def, is_terminator_def, is_read0_opcode_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_compile_tuple_store_all_frame:
  !tys bts vals R.
  shape_stable R /\
  (!bt. MEM (BaseTarget bt) bts ==>
    (!env ty child. supported_target_exists (\e. e = child) bt /\
        ~supported_expr_exists expr_shape_root child ==>
      shape_step internal compiler_label (\s. cenv_shape_ok s env)
        (compile_expr env ty child) (\v s. value_shape_ok s v) /\
      alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
        (compile_expr env ty child) (\v s. T)) /\
    ~supported_target_exists expr_shape_root bt) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
      EVERY (plain_operand s) vals)
    (compile_tuple_store_all ce tys bts vals)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `bts` >> Cases_on `vals` >>
      simp[compile_tuple_store_all_def, comp_return_def, alloc_run_def,
        alloc_frame_refl]) >>
  rpt gen_tac >> strip_tac >> Cases_on `bts`
  >- simp[compile_tuple_store_all_def, comp_return_def, alloc_run_def,
       alloc_frame_refl] >>
  Cases_on `vals`
  >- simp[compile_tuple_store_all_def, comp_return_def, alloc_run_def,
       alloc_frame_refl] >>
  simp[Once compile_tuple_store_all_cons, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    EVERY (plain_operand s) t'` >> reverse conj_tac
  >- (Cases_on `h'`
      >- (irule alloc_run_conseq >>
          irule_at Any alloc_run_compile_tuple_store_one_frame >>
          qexistsl [`internal`, `\s. R s /\ EVERY (plain_operand s) t'`] >>
          simp[shape_stable_conj, shape_stable_plain_operands] >> metis_tac[MEM]) >>
      simp[compile_tuple_store_all_def, comp_ignore_bind_def] >>
      irule alloc_run_bind >>
      qexists `\u s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
        EVERY (plain_operand s) t'` >> conj_tac
      >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
      simp[emit_void_def] >>
      irule alloc_run_conseq >>
      irule_at Any (SRULE [emit_inst_def] alloc_run_emit_inst_frame) >>
      qexistsl [`F`, `\s. R s /\ cenv_shape_ok s ce /\ EVERY (plain_operand s) t'`] >>
      simp[emit_void_def, shape_stable_conj, cenv_shape_ok_stable,
        shape_stable_plain_operands, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def]) >>
  gen_tac >> simp[] >> first_x_assum irule >> simp[] >> metis_tac[MEM]
QED

Theorem alloc_run_load_memory_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s addr)
    (compile_load_memory addr prim)
    (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> Cases_on `prim` >> simp[compile_load_memory_def]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_op_frame >>
      qexists `R` >> simp[] >> rpt strip_tac >>
      irule (cj 2 plain_data_inst_ok) >>
      simp[] >> qexists `s` >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_tuple_load_all_frame:
  !tys src off R. shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src)
    (compile_tuple_load_all ce src tys off)
    (\vs s. shape_state s /\ R s /\ plain_operand s src /\
      EVERY (plain_operand s) vs)
Proof
  Induct
  >- simp[compile_tuple_load_all_def, comp_return_def, alloc_run_def,
       alloc_frame_refl] >>
  rpt gen_tac >> strip_tac >> simp[compile_tuple_load_all_def] >>
  irule alloc_run_bind >>
  qexists `\p s. shape_state s /\ R s /\ plain_operand s src /\ plain_operand s p` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_address_frame >>
      qexists `\s. R s /\ plain_operand s src` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)]) >>
  qx_gen_tac `p` >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ plain_operand s src /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_load_memory_frame >>
      qexists `\s. R s /\ plain_operand s src` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)]) >>
  qx_gen_tac `v` >> simp[] >> irule alloc_run_bind >>
  qexists `\vs s. shape_state s /\ R s /\ plain_operand s src /\
    plain_operand s v /\ EVERY (plain_operand s) vs` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> first_x_assum (irule_at Any) >>
      qexists `\s. R s /\ plain_operand s v` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[v]` shape_stable_plain_operands)]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_tuple_stage_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src)
    (comp_bind (compile_alloc_buffer bytes) (\b.
      comp_bind (comp_return b.buf_operand) (\p.
        comp_ignore_bind (emit_void MCOPY [p; src; Lit (n2w bytes)])
          (comp_return p))))
    (\p s. shape_state s /\ R s /\ plain_operand s p)
Proof
  strip_tac >> simp[loop_comp_return_bind, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ R s /\ plain_operand s src /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_alloc_buffer_frame >>
      qexists `\s. R s /\ plain_operand s src` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)]) >>
  qx_gen_tac `b` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s /\ plain_operand s b.buf_operand` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_void_frame >>
      qexists `\s. R s /\ plain_operand s b.buf_operand` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[b.buf_operand]` shape_stable_plain_operands),
        plain_operand_def, is_label_operand_def] >>
      rpt strip_tac >> irule (cj 2 plain_data_inst_ok) >> simp[] >>
      qexists `s` >> simp[plain_operand_def, is_label_operand_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_tuple_unpack_frame:
  shape_stable R /\
  (!bt. MEM (BaseTarget bt) bts ==>
    (!env ty child. supported_target_exists (\e. e = child) bt /\
        ~supported_expr_exists expr_shape_root child ==>
      shape_step internal compiler_label (\s. cenv_shape_ok s env)
        (compile_expr env ty child) (\v s. value_shape_ok s v) /\
      alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
        (compile_expr env ty child) (\v s. T)) /\
    ~supported_target_exists expr_shape_root bt) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s src)
    (compile_tuple_unpack ce ty stage bts src)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >> simp[compile_tuple_unpack_def] >> IF_CASES_TAC
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_inst_frame) >>
      qexists `\s. R s /\ cenv_shape_ok s ce` >>
      simp[shape_stable_conj, cenv_shape_ok_stable, lowered_inst_ok_def,
        mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, label_positions_ok_def, is_terminator_def,
        is_read0_opcode_def]) >>
  irule alloc_run_bind >>
  qexists `\p s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s p` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (irule alloc_run_conseq >> irule_at Any alloc_run_tuple_stage_frame >>
          qexists `\s. R s /\ cenv_shape_ok s ce` >>
          simp[shape_stable_conj, cenv_shape_ok_stable]) >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  qx_gen_tac `p` >> simp[] >> irule alloc_run_bind >>
  qexists `\vs s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    EVERY (plain_operand s) vs` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_compile_tuple_load_all_frame >>
      qexists `\s. R s /\ cenv_shape_ok s ce` >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule alloc_run_compile_tuple_store_all_frame >>
  simp[] >> qexists `internal` >> metis_tac[]
QED

Theorem assignments_exclude_base_target:
  !targets bt. ~supported_assignments_exists p targets /\
    MEM (BaseTarget bt) targets ==> ~supported_target_exists p bt
Proof
  Induct >> simp[supported_assignment_exists_def] >> rpt strip_tac >>
  gvs[] >> metis_tac[supported_assignment_exists_def]
QED
