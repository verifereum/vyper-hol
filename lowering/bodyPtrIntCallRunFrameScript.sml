Theory bodyPtrIntCallRunFrame
Ancestors bodyPtrIntCallAllocation bodyPtrIntCallLowRegion
  bodyPtrIntCallTaintBounds venomExecSemantics ptrDiscipline
  finite_map pred_set arithmetic words list venomInst vyperCompiler compileVyper bodySim

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
