Theory ctxLookupAgreeHelpers
Ancestors
  venomExecSemantics venomInst venomState contextRawReachable
  contextCodegenRel venomInstProofs1 list

Theorem lookup_function_selected_name:
  lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm] >>
  gvs[lookup_function_def]
QED

Theorem EVERY_fn_insts_blocks:
  EVERY P (fn_insts_blocks bbs) <=>
  EVERY (\bb. EVERY P bb.bb_instructions) bbs
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def, EVERY_APPEND]
QED

Theorem EVERY_fn_block:
  EVERY P (fn_insts fn) /\ MEM bb fn.fn_blocks ==>
  EVERY P bb.bb_instructions
Proof
  rewrite_tac[fn_insts_def, EVERY_fn_insts_blocks] >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem selected_block_mem[local]:
  !bbs lbl bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >> rw[lookup_block_def, FIND_thm] >>
  gvs[lookup_block_def] >> metis_tac[]
QED

Theorem EVERY_fn_lookup_block:
  EVERY P (fn_insts fn) /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  EVERY P bb.bb_instructions
Proof
  strip_tac >> irule EVERY_fn_block >> qexists_tac `fn` >>
  metis_tac[selected_block_mem]
QED

Theorem EVERY_get_instruction:
  EVERY P bb.bb_instructions /\ get_instruction bb idx = SOME inst ==> P inst
Proof
  simp[get_instruction_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[EVERY_EL]
QED

Theorem EVERY_active_inst:
  EVERY P (fn_insts fn) /\ active_inst fn inst s ==> P inst
Proof
  rw[active_inst_def] >> drule_all EVERY_fn_block >>
  simp[EVERY_EL] >> metis_tac[]
QED

Theorem run_defs_predicate_cong:
  (!fuel ctx inst s. !P ctx'.
    (!i nm ops. P i /\ i.inst_opcode = INVOKE /\
       decode_invoke i = SOME (nm,ops) ==>
       lookup_function nm ctx.ctx_functions = lookup_function nm ctx'.ctx_functions /\
       (!fn. lookup_function nm ctx.ctx_functions = SOME fn ==> EVERY P (fn_insts fn))) /\
    P inst ==> step_inst fuel ctx inst s = step_inst fuel ctx' inst s) /\
  (!fuel ctx bb s. !P ctx'.
    (!i nm ops. P i /\ i.inst_opcode = INVOKE /\
       decode_invoke i = SOME (nm,ops) ==>
       lookup_function nm ctx.ctx_functions = lookup_function nm ctx'.ctx_functions /\
       (!fn. lookup_function nm ctx.ctx_functions = SOME fn ==> EVERY P (fn_insts fn))) /\
    EVERY P bb.bb_instructions ==> exec_block fuel ctx bb s = exec_block fuel ctx' bb s) /\
  (!fuel ctx fn s. !P ctx'.
    (!i nm ops. P i /\ i.inst_opcode = INVOKE /\
       decode_invoke i = SOME (nm,ops) ==>
       lookup_function nm ctx.ctx_functions = lookup_function nm ctx'.ctx_functions /\
       (!fn. lookup_function nm ctx.ctx_functions = SOME fn ==> EVERY P (fn_insts fn))) /\
    EVERY P (fn_insts fn) ==> run_blocks fuel ctx fn s = run_blocks fuel ctx' fn s)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume run_defs_predicate_cong[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
  Cases_on `inst.inst_opcode = INVOKE` >- suspend "invoke" >> simp[]
QED

Resume run_defs_predicate_cong[invoke]:
  simp[] >> Cases_on `decode_invoke inst` >- simp[] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  rename1 `decode_invoke inst = SOME (nm,ops)` >>
  qpat_assum `!i nm ops. _` (qspec_then `inst` mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  Cases_on `lookup_function nm ctx'.ctx_functions` >- simp[] >>
  rename1 `lookup_function nm ctx'.ctx_functions = SOME callee` >>
  Cases_on `eval_operands ops s` >- simp[] >>
  rename1 `eval_operands ops s = SOME args` >>
  Cases_on `setup_callee callee args s` >- simp[] >>
  rename1 `setup_callee callee args s = SOME cs` >>
  `run_blocks fuel ctx callee cs = run_blocks fuel ctx' callee cs`
    by (first_x_assum irule >> simp[] >> metis_tac[]) >> simp[]
QED

Resume run_defs_predicate_cong[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `P inst` by metis_tac[EVERY_get_instruction] >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s`
    by metis_tac[] >>
  simp[] >> Cases_on `step_inst fuel ctx' inst s` >> simp[] >>
  IF_CASES_TAC >> simp[] >> first_x_assum irule >> simp[] >>
  qexists_tac `P` >> simp[] >> first_assum ACCEPT_TAC
QED

Resume run_defs_predicate_cong[run]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  CONV_TAC (BINOP_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  Cases_on `fuel` >- simp[] >>
  rename1 `SUC n` >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `EVERY P bb.bb_instructions` by metis_tac[EVERY_fn_lookup_block] >>
  Cases_on `eval_phis s bb.bb_instructions` >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
   exec_block n ctx' bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
    by (first_x_assum irule >> simp[] >> qexists_tac `P` >>
        simp[] >> first_assum ACCEPT_TAC) >>
  simp[] >>
  Cases_on `exec_block n ctx' bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  first_x_assum irule >> simp[] >> qexists_tac `P` >>
  simp[] >> first_assum ACCEPT_TAC
QED

Finalise run_defs_predicate_cong

Theorem update_var_initial_fmp[simp]:
  (update_var x v s).vs_initial_fmp = s.vs_initial_fmp
Proof simp[update_var_def]
QED

Theorem fold_update_var_initial_fmp:
  !s. (FOLDL (\s (x,v). update_var x v s) s xs).vs_initial_fmp = s.vs_initial_fmp
Proof
  Induct_on `xs` >> simp[] >> rpt gen_tac >>
  rename1 `((\(x,v). update_var x v s) pair).vs_initial_fmp = _` >>
  PairCases_on `pair` >> simp[]
QED

Theorem bind_outputs_initial_fmp:
  bind_outputs outs vals s = SOME t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof
  simp[bind_outputs_def] >> strip_tac >>
  gvs[AllCaseEqs(), fold_update_var_initial_fmp]
QED

Theorem merge_callee_initial_fmp[simp]:
  (merge_callee_state s t).vs_initial_fmp = s.vs_initial_fmp
Proof simp[merge_callee_state_def]
QED

Theorem adopt_return_initial_fmp[simp]:
  (adopt_return_fmp ret s).vs_initial_fmp = s.vs_initial_fmp
Proof Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem setup_callee_initial_fmp:
  setup_callee fn args s = SOME t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof simp[setup_callee_def] >> strip_tac >> gvs[AllCaseEqs()]
QED

Theorem eval_phis_initial_fmp:
  !s t. eval_phis s insts = OK t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof
  Induct_on `insts` >- simp[eval_phis_def] >>
  rpt gen_tac >> simp[Once eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  gvs[AllCaseEqs()] >> metis_tac[update_var_initial_fmp]
QED

Theorem enters_block_initial_fmp:
  enters_block fn s t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof rw[enters_block_def] >> drule eval_phis_initial_fmp >> simp[]
QED

Theorem step_inst_base_terminator_initial_fmp[local]:
  is_terminator inst.inst_opcode /\ step_inst_base inst s = OK t ==>
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[step_inst_base_opcode_eqs] >>
  gvs[AllCaseEqs(), jump_to_def] >> pairarg_tac >> gvs[]
QED

Theorem step_inst_base_initial_fmp:
  step_inst_base inst s = OK t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_terminator_initial_fmp] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem step_inst_initial_fmp:
  step_inst fuel ctx inst s = OK t ==> t.vs_initial_fmp = s.vs_initial_fmp
Proof
  simp[Once step_inst_def] >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule bind_outputs_initial_fmp >> simp[]) >>
  simp[] >> metis_tac[step_inst_base_initial_fmp]
QED
