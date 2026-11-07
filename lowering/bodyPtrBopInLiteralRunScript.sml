Theory bodyPtrBopInLiteralRun
Ancestors exprSimBopInLiteralWord
  exprLowering exprLoweringProps emitHelperProps compileEnv codegenRel
  contextCodegenRel fragExec venomExecSemantics venomState venomInst
  list words

Resume literal_notin_run[single]:
  drule_all emit_op_EQ_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  imp_res_tac emit_op_extends >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `ss''` >> simp[] >>
  Cases_on `w = h'` >> simp[bool_to_word_def]
QED

Resume literal_notin_run[cons]:
  drule_all emit_op_EQ_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  `LIST_REL (\x v. eval_operand x ss'' = SOME v) t ys` by
    (irule LIST_REL_mono >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!ws needle' w sa' op sb ss. _`
    (qspec_then `v::ys` mp_tac) >> simp[] >> disch_then drule >>
  disch_then (qspecl_then [`w`, `ss''`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `eval_operand neq_res tt = SOME (bool_to_word (bool_to_word (w = h'') = 0w))`
    by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `emit_op AND _ sm = (op,sb)` >>
  rename1 `run_inst_seq (emitted_insts sm sb) tt = OK sf` >>
  imp_res_tac emit_op_extends >>
  drule_all (Q.SPECL [`sa`, `cs'`, `cs''`] run_inst_seq_chain) >> strip_tac >>
  `run_inst_seq (emitted_insts sa cs'') ss = OK ss''` by simp[] >>
  drule_all (Q.SPECL [`sa`, `cs''`, `sm`] run_inst_seq_chain) >> strip_tac >>
  `run_inst_seq (emitted_insts sa sm) ss = OK tt` by simp[] >>
  drule_all (Q.SPECL [`sa`, `sm`, `sb`] run_inst_seq_chain) >> strip_tac >>
  `bool_to_word (bool_to_word (w = h'') = 0w) &&
   bool_to_word (w <> v /\ ~MEM w ys) =
   bool_to_word (w <> h'' /\ w <> v /\ ~MEM w ys)` by
    (Cases_on `w = h''` >> Cases_on `w <> v /\ ~MEM w ys` >>
     simp[bool_to_word_def, WORD_AND_IDEM, WORD_AND_CLAUSES]) >>
  qexists_tac `sf` >> simp[] >> metis_tac[]
QED

Finalise literal_notin_run

Theorem literal_in_code_shape:
  !xs needle sa dst sb.
    compile_list_membership_in needle xs sa = (dst,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    same_blocks sa sb /\
    EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
      (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
      LENGTH i.inst_outputs = 1) (emitted_insts sa sb)
Proof
  Induct >> rpt gen_tac
  >- simp[compile_list_membership_in_def, comp_return_def, emitted_insts_refl,
          same_blocks_def] >>
  Cases_on `xs` >> simp[compile_list_membership_in_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac
  >- (drule emit_op_extends >> strip_tac >>
      drule emitted_insts_emit_op >> strip_tac >>
      simp[mk_inst_def]) >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac emit_op_extends >>
  `emitted_insts sa cs'' = emitted_insts sa cs' ++ emitted_insts cs' cs''` by
    (irule emitted_insts_append >> simp[]) >>
  `cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs''` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa cs'' ++ emitted_insts cs'' sb` by
    (irule emitted_insts_append >> simp[]) >>
  imp_res_tac emitted_insts_emit_op >>
  simp[mk_inst_def] >> gvs[same_blocks_def]
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
  Induct >> rpt gen_tac
  >- simp[compile_list_membership_notin_def, comp_return_def, emitted_insts_refl,
          same_blocks_def] >>
  Cases_on `xs` >> simp[compile_list_membership_notin_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac
  >- (imp_res_tac emit_op_extends >>
      drule_all emitted_insts_append >> strip_tac >>
      imp_res_tac emitted_insts_emit_op >>
      simp[mk_inst_def] >> gvs[same_blocks_def]) >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac emit_op_extends >>
  `emitted_insts sa cs'' = emitted_insts sa cs' ++ emitted_insts cs' cs''` by
    (irule emitted_insts_append >> simp[]) >>
  `cs''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs''` by simp[] >>
  `emitted_insts sa cs''' = emitted_insts sa cs'' ++ emitted_insts cs'' cs'''` by
    (irule emitted_insts_append >> simp[]) >>
  `cs'''.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa cs'''` by simp[] >>
  `emitted_insts sa sb = emitted_insts sa cs''' ++ emitted_insts cs''' sb` by
    (irule emitted_insts_append >> simp[]) >>
  imp_res_tac emitted_insts_emit_op >>
  simp[mk_inst_def] >> gvs[same_blocks_def]
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
