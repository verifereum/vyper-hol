Theory bodyPtrBopInLiteralRun
Ancestors exprSimBopInLiteralWord
  exprLowering exprLoweringProps emitHelperProps compileEnv codegenRel
  contextCodegenRel fragExec venomExecSemantics venomState venomInst
  list words

Theorem literal_shape_trans[local]:
  !P sa sm sb.
    (sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
     same_blocks sa sm /\ EVERY P (emitted_insts sa sm)) /\
    (sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
     same_blocks sm sb /\ EVERY P (emitted_insts sm sb)) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\ EVERY P (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> simp[]) >>
  gvs[same_blocks_def]
QED

Theorem literal_shape_op[local]:
  !opc ops sa v sb.
    emit_op opc ops sa = (v,sb) /\ MEM opc [EQ; OR; AND; ISZERO] /\
    (LENGTH ops = 1 \/ LENGTH ops = 2) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. (i.inst_opcode = EQ \/ i.inst_opcode = OR \/
                i.inst_opcode = AND \/ i.inst_opcode = ISZERO) /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  rpt gen_tac >> strip_tac >>
  drule emit_op_extends >> drule emitted_insts_emit_op >> rpt strip_tac >>
  gvs[mk_inst_def]
QED

Theorem literal_eqs_shape:
  !xs needle sa cs sb.
    emit_membership_eqs needle xs sa = (cs,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. (i.inst_opcode = EQ \/ i.inst_opcode = OR \/
                i.inst_opcode = AND \/ i.inst_opcode = ISZERO) /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  Induct >> rpt gen_tac
  >- simp[emit_membership_eqs_def, comp_return_def, emitted_insts_refl,
          same_blocks_def] >>
  simp[emit_membership_eqs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule literal_shape_op >> impl_tac >- simp[] >> strip_tac >>
  irule literal_shape_trans >> metis_tac[]
QED

Theorem literal_or_shape:
  !cs acc sa op sb.
    fold_membership_or acc cs sa = (op,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. (i.inst_opcode = EQ \/ i.inst_opcode = OR \/
                i.inst_opcode = AND \/ i.inst_opcode = ISZERO) /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  Induct >> rpt gen_tac
  >- simp[fold_membership_or_def, comp_return_def, emitted_insts_refl,
          same_blocks_def] >>
  simp[fold_membership_or_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule literal_shape_op >> impl_tac >- simp[] >> strip_tac >>
  irule literal_shape_trans >> metis_tac[]
QED

Theorem literal_and_shape:
  !cs acc sa op sb.
    fold_membership_and acc cs sa = (op,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. (i.inst_opcode = EQ \/ i.inst_opcode = OR \/
                i.inst_opcode = AND \/ i.inst_opcode = ISZERO) /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  Induct >> rpt gen_tac
  >- simp[fold_membership_and_def, comp_return_def, emitted_insts_refl,
          same_blocks_def] >>
  simp[fold_membership_and_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `emit_op ISZERO _ sa = (_,s1)` >>
  rename1 `emit_op AND _ s1 = (_,s2)` >>
  qpat_x_assum `emit_op ISZERO _ _ = _` assume_tac >>
  drule literal_shape_op >> impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `emit_op AND _ _ = _` assume_tac >>
  drule literal_shape_op >> impl_tac >- simp[] >> strip_tac >>
  metis_tac[literal_shape_trans]
QED

Theorem literal_in_code_shape:
  !xs needle sa dst sb.
    compile_list_membership_in needle xs sa = (dst,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  rpt gen_tac >> simp[compile_list_membership_in_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, _)` >>
  drule literal_eqs_shape >> strip_tac >>
  Cases_on `cs` >> gvs[comp_return_def] >>
  drule literal_or_shape >> strip_tac >>
  irule literal_shape_trans >> metis_tac[]
QED

Theorem literal_notin_code_shape:
  !xs needle sa dst sb.
    compile_list_membership_notin needle xs sa = (dst,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  rpt gen_tac >> simp[compile_list_membership_notin_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_membership_eqs needle xs sa = (cs, _)` >>
  drule literal_eqs_shape >> strip_tac >>
  Cases_on `cs` >> gvs[comp_return_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule literal_and_shape >> strip_tac >>
  drule literal_shape_op >> impl_tac >- simp[] >> strip_tac >>
  metis_tac[literal_shape_trans]
QED

Theorem membership_scalar_run_frame:
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) is /\
  run_inst_seq is s = OK t ==>
  (t with vs_vars := s.vs_vars) = s
Proof
  strip_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (mp_tac (Q.SPECL [`is`, `\x:string. F`, `s`, `t`]
                    run_inst_seq_protected_frame) >>
     impl_tac >- (simp[] >> rpt strip_tac >>
       drule (iffLR EVERY_MEM) >> disch_then drule >> strip_tac >>
       irule (cj 1 step_pure_opcode_frame) >> qexists_tac `i` >>
       gvs[]) >> simp[]) >>
  simp[venom_state_component_equality] >>
  gvs[venom_state_component_equality]
QED

Theorem literal_in_code:
  compile_list_membership_in needle xs sa = (dst,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) (emitted_insts sa sb)
Proof
  strip_tac >> drule literal_in_code_shape >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem literal_notin_code:
  compile_list_membership_notin needle xs sa = (dst,sb) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO]) (emitted_insts sa sb)
Proof
  strip_tac >> drule literal_notin_code_shape >>
  simp[EVERY_MEM] >> metis_tac[]
QED
