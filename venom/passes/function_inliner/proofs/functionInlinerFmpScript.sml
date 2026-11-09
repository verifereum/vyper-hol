(* Allocation-free execution and the FMP component of caller re-entry. *)
Theory functionInlinerFmp
Ancestors
  functionInlinerReturnTransport functionInlinerContract
  venomExecSemantics venomInstProofs1 opcodeClass list

Definition inline_fmp_result_def:
  inline_fmp_result fmp r <=>
    case r of
      OK u => u.vs_fmp = fmp
    | IntRet ir u => u.vs_fmp = fmp /\
        (ir.iret_adopt_fmp = NONE \/ ir.iret_adopt_fmp = SOME fmp)
    | Halt u => u.vs_fmp = fmp
    | Abort a u => u.vs_fmp = fmp
    | Error e => T
End

Theorem inline_setup_callee_fmp:
  setup_callee fn args s = SOME u ==> u.vs_fmp = s.vs_fmp
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
QED

Theorem inline_bind_outputs_fmp:
  bind_outputs outs vals s = SOME u ==> u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> irule bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> goal_assum (drule_at Any)
QED

Theorem inline_adopt_return_fmp:
  u.vs_fmp = caller.vs_fmp /\
  (ir.iret_adopt_fmp = NONE \/ ir.iret_adopt_fmp = SOME caller.vs_fmp) ==>
  (adopt_return_fmp ir (merge_callee_state caller u)).vs_fmp = u.vs_fmp
Proof
  strip_tac >> simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_clone_exit_fmp_reentry:
  inline_clone_exit p V opaque P outs caller ret ir u (OK v) /\
  inline_fmp_result caller.vs_fmp (IntRet ir u) ==>
  ?caller'. bind_outputs outs ir.iret_values caller = SOME caller' /\
    (adopt_return_fmp ir (merge_callee_state caller' u)).vs_fmp = v.vs_fmp
Proof
  simp[inline_clone_exit_def, inline_fmp_result_def] >> rpt strip_tac >>
  qexists `caller'` >> simp[venomStateTheory.jump_to_def] >>
  drule inline_bind_outputs_fmp >> strip_tac >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem inline_base_ok_fmp:
  step_inst_base inst s = OK u /\
  ~MEM inst.inst_opcode [ALLOCA; DALLOCA; DRET; SETFMP] ==>
  u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- (drule venomInstTheory.terminator_opcode_cases >> strip_tac >>
      gvs[step_inst_base_opcode_eqs, AllCaseEqs(),
          venomStateTheory.jump_to_def, venomStateTheory.halt_state_def,
          venomStateTheory.revert_state_def]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
  drule step_inst_base_preserves_all >> gvs[]
QED

Theorem inline_base_halt_fmp:
  step_inst_base inst s = Halt u ==> u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule step_inst_base_halt_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(),
      venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]
QED

Theorem inline_base_intret_fmp:
  step_inst_base inst s = IntRet ir u /\ inst.inst_opcode <> DRET ==>
  inline_fmp_result s.vs_fmp (IntRet ir u)
Proof
  strip_tac >> drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), inline_fmp_result_def]
QED

Theorem inline_base_abort_fmp:
  step_inst_base inst s = Abort a u ==> u.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_create_abort_iff, exec_write2_def,
      exec_ext_call_def,
      AllCaseEqs(),
      venomStateTheory.halt_state_def, venomStateTheory.revert_state_def,
      venomStateTheory.set_returndata_def]
QED

Theorem inline_base_fmp:
  ~MEM inst.inst_opcode [ALLOCA; DALLOCA; DRET; SETFMP] ==>
  inline_fmp_result s.vs_fmp (step_inst_base inst s)
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >>
  gvs[inline_fmp_result_def]
  >- (irule inline_base_ok_fmp >> goal_assum (drule_at Any) >> simp[])
  >- (drule inline_base_halt_fmp >> simp[])
  >- (drule inline_base_abort_fmp >> simp[]) >>
  drule inline_base_intret_fmp >> simp[inline_fmp_result_def]
QED

Theorem inline_eval_phis_fmp:
  !insts s u. eval_phis s insts = OK u ==> u.vs_fmp = s.vs_fmp
Proof
  rpt strip_tac >> drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  disch_then SUBST1_TAC >> simp[]
QED

Definition inline_fmp_inst_ok_def:
  inline_fmp_inst_ok inst <=>
    ~MEM inst.inst_opcode [ALLOCA; DALLOCA; DRET; SETFMP]
End

Definition inline_fmp_fn_ok_def:
  inline_fmp_fn_ok fn <=> EVERY inline_fmp_inst_ok (fn_insts fn)
End

Definition inline_fmp_ctx_ok_def:
  inline_fmp_ctx_ok ctx <=> EVERY inline_fmp_fn_ok ctx.ctx_functions
End

Theorem inline_execution_fmp:
  (!fuel ctx inst s.
    inline_fmp_ctx_ok ctx /\ inline_fmp_inst_ok inst ==>
    inline_fmp_result s.vs_fmp (step_inst fuel ctx inst s)) /\
  (!fuel ctx bb s.
    inline_fmp_ctx_ok ctx /\ EVERY inline_fmp_inst_ok bb.bb_instructions ==>
    inline_fmp_result s.vs_fmp (exec_block fuel ctx bb s)) /\
  (!fuel ctx fn s.
    inline_fmp_ctx_ok ctx /\ inline_fmp_fn_ok fn ==>
    inline_fmp_result s.vs_fmp (run_blocks fuel ctx fn s))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume inline_execution_fmp[step]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once step_inst_def] >> Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  simp[] >> irule inline_base_fmp >> gvs[inline_fmp_inst_ok_def]
QED

Resume inline_execution_fmp[invoke]:
  simp[] >> Cases_on `decode_invoke inst`
  >- simp[inline_fmp_result_def] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  rename1 `decode_invoke inst = SOME (nm,ops)` >>
  Cases_on `lookup_function nm ctx.ctx_functions`
  >- simp[inline_fmp_result_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME callee` >>
  Cases_on `eval_operands ops s` >- simp[inline_fmp_result_def] >>
  rename1 `eval_operands ops s = SOME args` >>
  Cases_on `setup_callee callee args s` >- simp[inline_fmp_result_def] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `inline_fmp_fn_ok callee` by
    (gvs[inline_fmp_ctx_ok_def] >>
     drule venomInstTheory.lookup_function_MEM >> metis_tac[EVERY_MEM]) >>
  `inline_fmp_result cs.vs_fmp (run_blocks fuel ctx callee cs)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule inline_setup_callee_fmp >> strip_tac >>
  Cases_on `run_blocks fuel ctx callee cs` >>
  gvs[inline_fmp_result_def, AllCaseEqs(), adopt_return_fmp_def,
      merge_callee_state_def] >>
  qmatch_goalsub_abbrev_tac `bind_outputs outs vals st` >>
  Cases_on `bind_outputs outs vals st` >> simp[] >>
  drule inline_bind_outputs_fmp >> simp[Abbr `st`]
QED

Resume inline_execution_fmp[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[inline_fmp_result_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inline_fmp_inst_ok inst` by
    metis_tac[ctxLookupAgreeHelpersTheory.EVERY_get_instruction] >>
  `inline_fmp_result s.vs_fmp (step_inst fuel ctx inst s)` by
    (first_x_assum irule >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[inline_fmp_result_def] >>
  IF_CASES_TAC >- (IF_CASES_TAC >> simp[inline_fmp_result_def]) >>
  first_x_assum drule >> simp[]
QED

Resume inline_execution_fmp[run]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[Once run_blocks_def] >> Cases_on `fuel` >- simp[inline_fmp_result_def] >>
  simp[] >> Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[inline_fmp_result_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY inline_fmp_inst_ok bb.bb_instructions` by
    metis_tac[inline_fmp_fn_ok_def, ctxLookupAgreeHelpersTheory.EVERY_fn_lookup_block] >>
  qspec_then `s` (qspec_then `bb.bb_instructions` strip_assume_tac)
    eval_phis_ok_or_error_defs >> simp[inline_fmp_result_def] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `sp.vs_fmp = s.vs_fmp` by metis_tac[inline_eval_phis_fmp] >>
  `inline_fmp_result s.vs_fmp
    (exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    gvs[] >>
  Cases_on `exec_block n ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[inline_fmp_result_def] >> IF_CASES_TAC >> simp[inline_fmp_result_def] >>
  first_x_assum drule >> simp[]
QED

Finalise inline_execution_fmp

Theorem inline_input_fmp_ctx:
  inliner_input_ok ctx ==> inline_fmp_ctx_ok ctx
Proof
  simp[inliner_input_ok_def, inline_fmp_ctx_ok_def, inline_fmp_fn_ok_def,
       inline_fmp_inst_ok_def, EVERY_MEM] >> metis_tac[]
QED

Theorem inline_callee_fmp_result:
  inline_fmp_ctx_ok ctx /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  setup_callee callee args caller = SOME cs ==>
  inline_fmp_result caller.vs_fmp (run_blocks fuel ctx callee cs)
Proof
  strip_tac >> drule inline_setup_callee_fmp >> strip_tac >>
  `inline_fmp_fn_ok callee` by
    (gvs[inline_fmp_ctx_ok_def] >> drule venomInstTheory.lookup_function_MEM >>
     metis_tac[EVERY_MEM]) >>
  mp_tac (cj 3 inline_execution_fmp) >>
  disch_then drule >> simp[] >> metis_tac[]
QED

Theorem inline_clone_exit_fmp_execution:
  inline_fmp_ctx_ok ctx /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  setup_callee callee args caller = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ir u /\
  inline_clone_exit p V opaque P outs caller ret ir u (OK v) ==>
  ?caller'. bind_outputs outs ir.iret_values caller = SOME caller' /\
    (adopt_return_fmp ir (merge_callee_state caller' u)).vs_fmp = v.vs_fmp
Proof
  strip_tac >> irule inline_clone_exit_fmp_reentry >>
  reverse conj_tac >- metis_tac[] >>
  drule_all inline_callee_fmp_result >>
  disch_then (qspec_then `fuel` mp_tac) >> simp[]
QED
