(* Scalar opcode deltas needed by unsigned denomination scaling. *)
Theory bodyPtrWordBuiltinsScalingSteps
Ancestors bodyPtrWordBuiltinsAbsSequence bodyPtrWordBuiltinsAbsSuffix
  bodyPtrWordBuiltinsNegSuffix bodyPtrDefs ptrDiscipline ptrSafeRun
  venomExecSemantics venomState venomInst venomExecProofs decoderGhostFramePtr
  contextCodegenRel codegenRel finite_map list pred_set bodyPtrWordBuiltinsScalar

Theorem word_scale_delta_inst_ok:
  MEM inst.inst_opcode [Div; OR] /\
  (!arg. MEM arg inst.inst_operands ==>
    op_taint tn arg = {} /\ op_prov G arg = NONE) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s
Proof
  strip_tac >>
  gvs[MEM, ptr_inst_ok_def, access_ok_def, taint_ok_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_scale_delta_out_taint:
  MEM inst.inst_opcode [Div; OR] ==> out_taint tn inst s = {}
Proof
  simp[MEM] >> strip_tac >>
  (namedCases_on `inst.inst_operands` ["", "a rest"]
  >- simp[out_taint_def] >>
  namedCases_on `rest` ["", "b more"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  namedCases_on `more` ["", "c tail"]
  >- (Cases_on `eval_operand a s` >> gvs[out_taint_def]) >>
  Cases_on `tail` >> simp[out_taint_def])
QED

Theorem word_scale_delta_normal:
  MEM inst.inst_opcode [Div; OR] /\ inst.inst_outputs = [x] /\
  step_inst_base inst s = OK t ==> ?w. t = update_var x w s
Proof
  simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem word_scale_delta_ghost_step:
  MEM inst.inst_opcode [Div; OR] /\ new_site_bytes s t = {} ==>
  step_prov PG G inst t = set_prov G inst.inst_outputs NONE /\
  step_taint inst s t tn = tn with t_var := set_var_taint tn.t_var inst.inst_outputs {}
Proof
  strip_tac >> drule word_scale_delta_out_taint >> strip_tac >>
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

Theorem word_scale_delta_scalar_transfer:
  MEM inst.inst_opcode [Div; OR] /\
  (!x. x IN scalars ==> FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN scalars) ==>
  !x. x IN scalars UNION set inst.inst_outputs ==>
    FLOOKUP (step_prov PG G inst t) x = NONE /\
    op_taint (step_taint inst s t tn) (Var x) = {}
Proof
  strip_tac >>
  `!x. x IN scalars UNION set inst.inst_outputs ==>
       FLOOKUP (step_prov PG G inst t) x = NONE` by
    (rpt strip_tac >> irule step_prov_scalar_set >> gvs[MEM] >>
     qexists_tac `scalars` >> simp[] >> metis_tac[]) >>
  drule word_scale_delta_out_taint >> strip_tac >>
  rpt strip_tac >- metis_tac[] >>
  namedCases_on `inst.inst_outputs` ["", "out rest"]
  >- (gvs[step_taint_def, op_taint_def, set_var_taint_def,
          FLOOKUP_DRESTRICT] >> metis_tac[]) >>
  namedCases_on `rest` ["", "out2 tail"]
  >- (Cases_on `out = x` >>
      gvs[step_taint_def, op_taint_def, set_var_taint_def,
          FLOOKUP_UPDATE] >> metis_tac[]) >>
  gvs[step_taint_def, op_taint_def, set_var_taint_def,
      FLOOKUP_DRESTRICT] >> IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem word_scale_delta_output_ghost_inv:
  MEM inst.inst_opcode [Div; OR] /\
  inst.inst_outputs = [x] /\ step_inst_base inst s = OK t /\
  ghost_inv d cenv cx es G tn s /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es (step_prov PG G inst t) (step_taint inst s t tn) t
Proof
  strip_tac >> drule_all word_scale_delta_normal >> strip_tac >> gvs[] >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[word_scale_delta_ghost_step, step_prov_def, out_prov_def] >>
  irule word_neg_temp_ghost_inv >> simp[] >> metis_tac[]
QED

Theorem word_scale_delta_output_ghost_kept:
  MEM inst.inst_opcode [Div; OR] /\
  inst.inst_outputs = [x] /\ step_inst_base inst s = OK t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G inst t) (step_taint inst s t tn)
Proof
  strip_tac >> drule_all word_scale_delta_normal >> strip_tac >> gvs[] >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  simp[word_scale_delta_ghost_step, step_prov_def, out_prov_def] >>
  irule word_neg_temp_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem word_scale_inst_ok:
  MEM inst.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
  (!arg. MEM arg inst.inst_operands ==>
    op_taint tn arg = {} /\ op_prov G arg = NONE) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn inst s
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [Div; OR]`
  >- (irule word_scale_delta_inst_ok >> simp[]) >>
  irule word_abs_scalar_inst_ok >> gvs[MEM]
QED

Theorem word_scale_scalar_transfer:
  MEM inst.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
  (!x. x IN scalars ==> FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN scalars) ==>
  !x. x IN scalars UNION set inst.inst_outputs ==>
    FLOOKUP (step_prov PG G inst t) x = NONE /\
    op_taint (step_taint inst s t tn) (Var x) = {}
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [Div; OR]`
  >- metis_tac[word_scale_delta_scalar_transfer] >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by gvs[MEM] >>
  metis_tac[word_abs_scalar_transfer]
QED

Theorem word_scale_step_allocas:
  MEM inst.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
  (inst.inst_opcode = ASSERT ==> ?v. inst.inst_operands = [v] /\ inst.inst_outputs = []) /\
  (inst.inst_opcode <> ASSERT ==> ?x. inst.inst_outputs = [x]) /\
  allocas_from lo s /\ step_inst_base inst s = OK t ==>
  allocas_from lo t
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [Div; OR]`
  >- (`inst.inst_opcode <> ASSERT` by gvs[MEM] >>
      `?x. inst.inst_outputs = [x]` by metis_tac[] >>
      drule_all word_scale_delta_normal >> strip_tac >>
      gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  `MEM inst.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by gvs[MEM] >>
  drule_all word_abs_step_allocas >> simp[]
QED

Theorem word_scale_step_ghost_inv:
  MEM inst.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
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
  strip_tac >> Cases_on `MEM inst.inst_opcode [Div; OR]`
  >- (`inst.inst_opcode <> ASSERT` by gvs[MEM] >>
      `?x. inst.inst_outputs = [x]` by metis_tac[] >>
      irule word_scale_delta_output_ghost_inv >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]) >>
  irule word_abs_step_ghost_inv >> simp[] >> gvs[MEM] >> metis_tac[]
QED

Theorem word_scale_step_ghost_kept:
  MEM inst.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT] /\
  (inst.inst_opcode = ASSERT ==> ?v. inst.inst_operands = [v] /\ inst.inst_outputs = []) /\
  (inst.inst_opcode <> ASSERT ==> ?x. inst.inst_outputs = [x]) /\
  step_inst_base inst s = OK t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x p. MEM x inst.inst_outputs /\ not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G inst t) (step_taint inst s t tn)
Proof
  strip_tac >> Cases_on `MEM inst.inst_opcode [Div; OR]`
  >- (`inst.inst_opcode <> ASSERT` by gvs[MEM] >>
      `?x. inst.inst_outputs = [x]` by metis_tac[] >>
      irule word_scale_delta_output_ghost_kept >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]) >>
  irule word_abs_step_ghost_kept >> simp[] >> gvs[MEM] >> metis_tac[]
QED
