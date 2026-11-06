Theory bodyPtrIntCallRunFrame
Ancestors bodyPtrIntCallAllocation bodyPtrIntCallConfinement bodyPtrIntCallLowRegion
  bodyPtrIntCallTaintBounds venomExecSemantics ptrDiscipline
  finite_map pred_set arithmetic words list venomInst venomExecProps venomMemProps venomInstProofs1 venomState unitShapeDefs vyperCompiler compileVyper bodySim

(* SETFMP can introduce taint below the static allocation frontier. *)
Theorem intcall_setfmp_frame_probe:
  let s = ARB with <|vs_allocas := FEMPTY; vs_alloca_next := 1; vs_fmp := 0w|>;
      t = s with vs_fmp := 1w;
      inst = mk_inst 0 SETFMP [Lit 1w] [];
      empty_taint = ARB with <|t_mem := {}; t_var := FEMPTY|>
  in
    step_inst 0 ctx inst s = OK t /\
    access_ok 0 FEMPTY fn inst s /\
    intcall_alloc_outside {0} s /\
    intcall_prov_outside {0} [] FEMPTY /\
    (!op k. MEM op inst.inst_operands /\ k IN op_taint empty_taint op ==> k < 32) /\
    ~intcall_mem_frame {0} empty_taint (step_taint inst s t empty_taint)
Proof
  EVAL_TAC >> simp[SUBSET_DEF]
QED

Theorem intcall_checked_fn_no_setfmp:
  fn_ptr_ok_check PL fn /\ MEM inst (fn_insts fn) ==>
  inst.inst_opcode <> SETFMP
Proof
  simp[fn_ptr_ok_check_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[] >> rpt strip_tac >>
  fs[EVERY_MEM, inst_ptr_ok_check_def] >> metis_tac[]
QED

Theorem intcall_checked_context_no_setfmp:
  lowering_context_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) ==> inst.inst_opcode <> SETFMP
Proof
  strip_tac >> fs[lowering_context_ok_def, ptr_ok_check_def, EVERY_MEM] >>
  metis_tac[intcall_checked_fn_no_setfmp]
QED

Theorem intcall_runtime_unit_context_ok:
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  lowering_context_ok unit.cu_context
Proof
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  simp[lower_vyper_runtime_unit_def, AllCaseEqs()] >> rpt strip_tac >>
  drule run_lowering_context_ok >> simp[]
QED

Theorem intcall_body_context_ok:
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor ==>
  lowering_context_ok ctx
Proof
  simp[body_inv_def] >> rpt strip_tac >> gvs[] >>
  drule intcall_runtime_unit_context_ok >> simp[]
QED

Theorem intcall_body_lookup_no_setfmp:
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  MEM inst (fn_insts fn) ==> inst.inst_opcode <> SETFMP
Proof
  strip_tac >> drule_all intcall_body_context_ok >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  drule_all intcall_checked_context_no_setfmp >> simp[]
QED

Theorem intcall_body_instruction_no_setfmp:
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> SETFMP
Proof
  strip_tac >> irule intcall_body_lookup_no_setfmp >>
  goal_assum (drule_at Any) >> simp[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[EL_MEM]) >>
  fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED

Theorem intcall_step_alloc_outside:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  intcall_alloc_outside P s ==> intcall_alloc_outside P t
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (fs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[intcall_alloc_exec_alloca]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_allocas,
              step_inst_base_preserves_alloca_next] >>
  fs[intcall_alloc_outside_def] >> metis_tac[]
QED


Theorem intcall_ordinary_fmp[local]:
  step_inst_base inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> SETFMP ==> w2n t.vs_fmp <= w2n s.vs_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[jump_to_def] >>
      pairarg_tac >> gvs[]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> fs[is_alloca_op_def]) >>
  drule step_inst_base_preserves_all >> simp[] >> strip_tac >> simp[]
QED

Theorem intcall_step_new_site_outside:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  intcall_alloc_outside P s ==> new_site_bytes s t SUBSET COMPL P
Proof
  strip_tac >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (fs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
      metis_tac[intcall_alloc_new_site_bytes]) >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >>
  `w2n t.vs_fmp <= w2n s.vs_fmp` by metis_tac[intcall_ordinary_fmp] >>
  fs[new_site_bytes_def, SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem intcall_step_mem_frame:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> SETFMP /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ access_ok 0 G fn inst s ==>
  intcall_mem_frame P tn (step_taint inst s t tn)
Proof
  strip_tac >> irule intcall_mem_frame_step >> conj_tac
  >- metis_tac[intcall_step_new_site_outside] >>
  drule intcall_word_taint_operands >> strip_tac >>
  metis_tac[intcall_written_taint_outside_zero]
QED

Theorem intcall_body_step_mem_frame:
  step_inst fuel ctx inst s = OK t /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> DALLOCA /\
  body_inv tops ctx ce cx /\ ~ce.ce_is_ctor /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  intcall_alloc_outside P s /\ intcall_prov_outside P PG G /\
  intcall_word_taint_bounded tn /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ access_ok 0 G fn inst s ==>
  intcall_mem_frame P tn (step_taint inst s t tn)
Proof
  strip_tac >> irule intcall_step_mem_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[intcall_body_instruction_no_setfmp]
QED
