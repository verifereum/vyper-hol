(* Single-step frame boundaries for the checked scalar Abs sequence. *)
Theory bodyPtrWordBuiltinsAbsSequence
Ancestors bodyPtrWordBuiltinsAbsSuffix bodyPtrWordBuiltinsScalarSequence
  bodyPtrWordBuiltinsNegSuffix bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomState venomInst venomExecProofs decoderGhostFramePtr
  contextCodegenRel codegenRel finite_map list pred_set

Theorem word_abs_ghost_step:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  new_site_bytes s t = {} ==>
  step_prov PG G inst t = set_prov G inst.inst_outputs
    (if inst.inst_opcode = SUB then first_prov G inst.inst_operands else NONE) /\
  step_taint inst s t tn = tn with t_var := set_var_taint tn.t_var inst.inst_outputs (out_taint tn inst s)
Proof
  strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, mem_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
  namedCases_on `inst.inst_operands` ["", "a rest"] >> simp[written_taint_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[written_taint_def] >>
  namedCases_on `more` ["", "c tail"] >> simp[written_taint_def] >>
  Cases_on `tail` >> simp[written_taint_def]
QED

Theorem word_abs_arithmetic_normal:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL] /\
  inst.inst_outputs = [x] /\ step_inst_base inst s = OK t ==>
  ?w. t = update_var x w s
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_abs_output_ghost_inv:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL] /\
  inst.inst_outputs = [x] /\ step_inst_base inst s = OK t /\
  ghost_inv d cenv cx es G tn s /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es (step_prov PG G inst t) (step_taint inst s t tn) t
Proof
  strip_tac >> drule_all word_abs_arithmetic_normal >> strip_tac >> gvs[] >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by gvs[MEM] >>
  simp[word_abs_ghost_step, step_prov_def, out_prov_def] >>
  irule word_neg_temp_ghost_inv >> simp[] >> metis_tac[]
QED

Theorem word_abs_output_ghost_kept:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL] /\
  inst.inst_outputs = [x] /\ step_inst_base inst s = OK t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G inst t) (step_taint inst s t tn)
Proof
  strip_tac >> drule_all word_abs_arithmetic_normal >> strip_tac >> gvs[] >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by gvs[MEM] >>
  simp[word_abs_ghost_step, step_prov_def, out_prov_def] >>
  irule word_neg_temp_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem word_abs_assert_normal:
  inst.inst_opcode = ASSERT /\ inst.inst_operands = [v] /\
  inst.inst_outputs = [] /\ step_inst_base inst s = OK t ==>
  t = s /\ step_prov PG G inst t = G /\ step_taint inst s t tn = tn
Proof
  strip_tac >>
  `t = s` by
    (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
     pure_rewrite_tac[opcode_case_def] >>
     simp[eval_operands_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  gvs[] >>
  `new_site_bytes s s = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by simp[] >>
  simp[word_abs_ghost_step, step_prov_def, out_prov_def, set_prov_def,
       set_var_taint_def, DRESTRICT_UNIV]
QED

Theorem word_abs_step_allocas:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  (inst.inst_opcode = ASSERT ==> ?v. inst.inst_operands = [v] /\ inst.inst_outputs = []) /\
  (inst.inst_opcode <> ASSERT ==> ?x. inst.inst_outputs = [x]) /\
  allocas_from lo s /\ step_inst_base inst s = OK t ==>
  allocas_from lo t
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> drule_all word_abs_assert_normal >> simp[]) >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL]` by gvs[MEM] >>
  `?x. inst.inst_outputs = [x]` by metis_tac[] >>
  drule_all word_abs_arithmetic_normal >> strip_tac >>
  gvs[allocas_from_def, update_var_def] >> metis_tac[]
QED

Theorem word_abs_step_ghost_inv:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  (inst.inst_opcode = ASSERT ==> ?v. inst.inst_operands = [v] /\ inst.inst_outputs = []) /\
  (inst.inst_opcode <> ASSERT ==> ?x. inst.inst_outputs = [x]) /\
  step_inst_base inst s = OK t /\ ghost_inv d cenv cx es G tn s /\
  (!x n p sz. MEM x inst.inst_outputs /\
     FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!x p sz. MEM x inst.inst_outputs /\ d <> NONE /\
     cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!x p sz. MEM x inst.inst_outputs /\
     cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es (step_prov PG G inst t) (step_taint inst s t tn) t
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> drule_all word_abs_assert_normal >> simp[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL]` by gvs[MEM] >>
  `?x. inst.inst_outputs = [x]` by metis_tac[] >>
  irule word_abs_output_ghost_inv >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]
QED

Theorem word_abs_step_ghost_kept:
  MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL] /\
  (inst.inst_opcode = ASSERT ==> ?v. inst.inst_operands = [v] /\ inst.inst_outputs = []) /\
  (inst.inst_opcode <> ASSERT ==> ?x. inst.inst_outputs = [x]) /\
  step_inst_base inst s = OK t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x p. MEM x inst.inst_outputs /\ not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G inst t) (step_taint inst s t tn)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ASSERT`
  >- (gvs[] >> drule_all word_abs_assert_normal >> simp[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; XOR; MUL]` by gvs[MEM] >>
  `?x. inst.inst_outputs = [x]` by metis_tac[] >>
  irule word_abs_output_ghost_kept >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]
QED

Theorem word_abs_allocas_index:
  allocas_from lo (s with vs_inst_idx := k) <=> allocas_from lo s
Proof
  simp[allocas_from_def]
QED
