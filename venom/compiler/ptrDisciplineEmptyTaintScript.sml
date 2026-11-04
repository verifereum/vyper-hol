Theory ptrDisciplineEmptyTaint
Ancestors
  ptrDiscipline venomExecSemantics venomMemProofs venomInstProofs1
  opcodeClass runtimeProvenanceSources ctxLookupAgreeHelpers concretizeAnalysisBoundary
  finite_map pred_set list

Definition var_taint_empty_def:
  var_taint_empty tv <=> !v m. FLOOKUP tv v = SOME m ==> m = {}
End

Definition taint_empty_def:
  taint_empty tn <=>
    tn.t_mem = {} /\ var_taint_empty tn.t_var /\
    tn.t_stor = {} /\ tn.t_trans = {} /\ tn.t_imm = {}
End

Definition allocation_free_opcode_def:
  allocation_free_opcode opc <=>
    opc <> ALLOCA /\ opc <> DALLOCA /\ opc <> SETFMP /\
    opc <> DRET /\ opc <> RETFMP
End

Theorem entry_taint_empty:
  taint_empty entry_taint
Proof
  simp[taint_empty_def, var_taint_empty_def, entry_taint_def]
QED

Theorem op_taint_empty:
  taint_empty tn ==> op_taint tn op = {}
Proof
  strip_tac >> Cases_on `op` >> simp[op_taint_def] >>
  gvs[taint_empty_def, var_taint_empty_def] >>
  CASE_TAC >> simp[] >> metis_tac[]
QED

Theorem shift_taint_empty:
  shift_taint opc k {} = {}
Proof
  simp[shift_taint_def, EXTENSION]
QED

Theorem out_taint_empty:
  taint_empty tn ==> out_taint tn inst s = {}
Proof
  strip_tac >>
  simp[out_taint_def, op_taint_empty, shift_taint_empty,
       mem_word_taint_def, key_taint_def] >>
  gvs[taint_empty_def] >>
  rpt CASE_TAC >> simp[shift_taint_empty, op_taint_empty,
    mem_word_taint_def, key_taint_def]
QED

Theorem written_taint_empty:
  taint_empty tn ==> written_taint tn inst s = {}
Proof
  strip_tac >>
  `tn.t_mem = {}` by gvs[taint_empty_def] >>
  namedCases_on `inst.inst_operands` ["", "a xs"] >>
  simp[written_taint_def] >>
  namedCases_on `xs` ["", "v ys"] >> simp[written_taint_def] >>
  namedCases_on `ys` ["", "sz zs"] >>
  simp[written_taint_def, op_taint_empty] >-
    (rpt (CASE_TAC >> simp[])) >>
  namedCases_on `zs` ["", "extra rest"] >>
  simp[written_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[])
QED

Theorem set_var_taint_empty:
  var_taint_empty tv ==> var_taint_empty (set_var_taint tv outs {})
Proof
  strip_tac >> simp[set_var_taint_def] >> rpt CASE_TAC >>
  gvs[var_taint_empty_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem key_update_empty:
  key_update {} key {} = {}
Proof
  simp[key_update_def, EXTENSION]
QED

Theorem store_taint_empty:
  taint_empty tn ==> store_taint opc tn inst s {} = {}
Proof
  strip_tac >> simp[store_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[key_update_empty])
QED

Theorem imm_taint_empty:
  taint_empty tn ==> imm_taint tn inst s = {}
Proof
  strip_tac >> `tn.t_imm = {}` by gvs[taint_empty_def] >>
  simp[imm_taint_def, op_taint_empty] >>
  rpt (CASE_TAC >> simp[key_update_empty])
QED

Theorem step_taint_empty:
  taint_empty tn /\ new_site_bytes s s' = {} ==>
  taint_empty (step_taint inst s s' tn)
Proof
  strip_tac >>
  simp[step_taint_def, taint_empty_def, mem_taint_def,
       written_taint_empty, out_taint_empty, set_var_taint_empty,
       store_taint_empty, imm_taint_empty, adopt_reset_def] >>
  gvs[taint_empty_def, set_var_taint_empty] >>
  `taint_empty tn` by simp[taint_empty_def] >>
  simp[store_taint_empty]
QED

Theorem phi_taint_empty:
  taint_empty tn ==> phi_taint prev tn inst = {}
Proof
  strip_tac >> Cases_on `prev` >> simp[phi_taint_def] >>
  CASE_TAC >> simp[op_taint_empty]
QED

Theorem phis_taint_empty:
  taint_empty tn ==> var_taint_empty (phis_taint prev tn insts)
Proof
  Induct_on `insts` >> simp[phis_taint_def] >-
    simp[taint_empty_def] >>
  strip_tac >> simp[phi_taint_empty] >>
  CASE_TAC >> gvs[taint_empty_def, set_var_taint_empty]
QED

Theorem entry_taint_vars_empty:
  taint_empty tn ==> taint_empty (entry_taint_vars fn s tn)
Proof
  strip_tac >> simp[entry_taint_vars_def] >> CASE_TAC >>
  simp[taint_empty_def, phis_taint_empty] >> gvs[taint_empty_def]
QED

Theorem new_site_bytes_unchanged:
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  new_site_bytes s s' = {}
Proof
  simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem var_taint_empty_restrict:
  var_taint_empty tv ==> var_taint_empty (DRESTRICT tv dom)
Proof
  simp[var_taint_empty_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem taint_empty_variables:
  taint_empty tn /\ var_taint_empty tv ==>
  taint_empty (tn with t_var := tv)
Proof
  simp[taint_empty_def]
QED

Theorem var_taint_empty_fempty:
  var_taint_empty FEMPTY
Proof
  simp[var_taint_empty_def]
QED

Theorem merge_callee_state_allocas:
  (merge_callee_state caller callee).vs_allocas = caller.vs_allocas
Proof
  simp[merge_callee_state_def]
QED

Theorem allocation_free_step_allocas:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  (step_inst fuel ctx inst s = OK s' \/
   step_inst fuel ctx inst s = Halt s' \/
   (?a. step_inst fuel ctx inst s = Abort a s') \/
   (?v. step_inst fuel ctx inst s = IntRet v s')) ==>
  s'.vs_allocas = s.vs_allocas
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  metis_tac[step_inst_base_preserves_allocas]
QED

Theorem allocation_free_nonterminator_fmp_ok[local]:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
  drule_all step_inst_base_preserves_all >> simp[] >> metis_tac[]
QED

Theorem allocation_free_step_intret:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = IntRet ret s' ==>
  s' = s /\ ret.iret_adopt_fmp = NONE
Proof
  strip_tac >> gvs[step_inst_non_invoke, allocation_free_opcode_def] >>
  drule step_inst_base_intret_opcodes >> strip_tac >> gvs[] >>
  gvs[step_inst_base_def, AllCaseEqs()]
QED

Theorem allocation_free_terminator_fmp_ok[local]:
  allocation_free_opcode inst.inst_opcode /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[venomInstTheory.is_terminator_def, allocation_free_opcode_def] >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[] >> strip_tac >> gvs[AllCaseEqs(), venomStateTheory.jump_to_def]
QED

Theorem allocation_free_step_fmp_halt:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = Halt s' ==>
  s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  drule step_inst_base_halt_opcodes >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = Halt s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[] >> strip_tac >>
  gvs[AllCaseEqs(), extract_venom_result_def,
      venomStateTheory.halt_state_def, venomStateTheory.set_returndata_def]
QED

Theorem allocation_free_step_fmp_ok:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' ==> s'.vs_fmp = s.vs_fmp
Proof
  metis_tac[allocation_free_nonterminator_fmp_ok,
            allocation_free_terminator_fmp_ok]
QED

Theorem allocation_free_step_new_site_bytes:
  inst.inst_opcode <> INVOKE /\ allocation_free_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s' ==> new_site_bytes s s' = {}
Proof
  strip_tac >> irule new_site_bytes_unchanged >>
  metis_tac[allocation_free_step_fmp_ok, allocation_free_step_allocas]
QED

Theorem bind_outputs_allocation_frame:
  bind_outputs outs vals s = SOME s' ==>
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp
Proof
  strip_tac >> conj_tac >>
  irule bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem ret_taint_empty:
  taint_empty tn ==> ret_taint tn inst s = {}
Proof
  strip_tac >> `tn.t_mem = {}` by gvs[taint_empty_def] >>
  simp[ret_taint_def] >> rpt (CASE_TAC >> simp[EXTENSION])
QED

Theorem enters_block_allocas:
  enters_block fn s s1 ==> s1.vs_allocas = s.vs_allocas
Proof
  simp[contextCodegenRelTheory.enters_block_def] >> rpt strip_tac >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem step_prov_empty:
  allocation_free_opcode inst.inst_opcode /\ EVERY ($= NONE) PG ==>
  step_prov PG FEMPTY inst s' = FEMPTY
Proof
  strip_tac >> simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `FLOOKUP (step_prov PG FEMPTY inst s') x` >> simp[] >>
  gvs[allocation_free_opcode_def, EVERY_EL] >>
  drule_all step_prov_source >> simp[] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >> gvs[]
QED

Theorem entry_prov_empty:
  entry_prov fn s FEMPTY = FEMPTY
Proof
  simp[entry_prov_def] >> CASE_TAC >> simp[] >>
  simp[fmap_eq_flookup] >> gen_tac >>
  Cases_on `FLOOKUP (phis_prov s.vs_prev_bb FEMPTY x.bb_instructions) x'` >>
  simp[] >> drule phis_prov_source >> simp[op_prov_def] >>
  rpt strip_tac >> Cases_on `op` >> gvs[op_prov_def]
QED

Definition allocation_free_frame_def:
  allocation_free_frame ctx f <=>
    MEM f.cf_fn ctx.ctx_functions /\ f.cf_state.vs_allocas = FEMPTY /\
    f.cf_prov = FEMPTY /\ EVERY ($= NONE) f.cf_params /\
    var_taint_empty f.cf_tvar
End

Theorem allocation_free_frame_reachable:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
                    (fn_insts fn)) ctx.ctx_functions /\
  vs.vs_allocas = FEMPTY ==>
  MEM fn ctx.ctx_functions /\ s.vs_allocas = FEMPTY /\ G = FEMPTY /\
  EVERY ($= NONE) PG /\ taint_empty tn /\
  EVERY (allocation_free_frame ctx) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume allocation_free_frame_reachable[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  simp[entry_taint_empty] >> conj_tac
  >- (gvs[venomInstTheory.lookup_function_def] >>
      drule venomExecProofsTheory.FIND_MEM >> simp[]) >>
  drule enters_block_allocas >> simp[]
QED

Resume allocation_free_frame_reachable[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  `EVERY (\i. allocation_free_opcode i.inst_opcode) (fn_insts fn)` by
    (qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  qpat_x_assum `active_inst fn inst' _` kall_tac >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  `s'.vs_allocas = s.vs_allocas` by
    (irule allocation_free_step_allocas >>
     qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[]) >>
  simp[step_prov_empty] >>
  irule step_taint_empty >> simp[] >>
  irule allocation_free_step_new_site_bytes >>
  qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[]
QED

Resume allocation_free_frame_reachable[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  `EVERY (\i. allocation_free_opcode i.inst_opcode) (fn_insts fn)` by
    (qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  qpat_x_assum `active_inst fn inst' _` kall_tac >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[venomInstTheory.is_terminator_def]) >>
  `s'.vs_allocas = s.vs_allocas` by
    (irule allocation_free_step_allocas >>
     qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[]) >>
  drule enters_block_allocas >> strip_tac >>
  simp[entry_prov_empty, entry_taint_vars_empty]
QED

Resume allocation_free_frame_reachable[call]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  drule setup_callee_empty_allocas >> strip_tac >>
  drule enters_block_allocas >> strip_tac >>
  simp[allocation_free_frame_def, taint_empty_variables,
       var_taint_empty_fempty, taint_empty_def, EVERY_MAP, op_prov_def] >>
  gvs[venomInstTheory.lookup_function_def] >>
  drule venomExecProofsTheory.FIND_MEM >>
  simp[taint_empty_def, EVERY_MEM] >> strip_tac >>
  reverse conj_tac >- gvs[taint_empty_def] >>
  gen_tac >> strip_tac >> Cases_on `x` >> simp[]
QED

Resume allocation_free_frame_reachable[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[allocation_free_frame_def] >>
  `EVERY (\i. allocation_free_opcode i.inst_opcode) (fn_insts fn)` by
    (qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  qpat_x_assum `active_inst f.cf_fn inst' _` kall_tac >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[Once step_inst_def, AllCaseEqs()]) >>
  drule_all allocation_free_step_intret >> strip_tac >>
  drule bind_outputs_allocation_frame >>
  simp[adopt_return_fmp_def, merge_callee_state_allocas] >> strip_tac >>
  simp[taint_empty_variables, var_taint_empty_restrict]
QED

Finalise allocation_free_frame_reachable

Theorem allocation_free_reachable_taint:
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
                    (fn_insts fn)) ctx.ctx_functions /\
  vs.vs_allocas = FEMPTY /\
  frame_reachable vs ctx stk PG G tn fn inst s ==> taint_empty tn
Proof
  strip_tac >> drule allocation_free_frame_reachable >> simp[]
QED

Theorem allocation_free_final_taint:
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
                    (fn_insts fn)) ctx.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ final_taint vs ctx s_h tn R ==>
  taint_empty tn /\ R = {}
Proof
  simp[final_taint_def] >> rpt strip_tac >> gvs[] >>
  drule allocation_free_frame_reachable >> simp[] >> strip_tac >>
  `EVERY (\i. allocation_free_opcode i.inst_opcode) (fn_insts fn)` by
    (qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then (qspec_then `fn` mp_tac) >> simp[]) >>
  drule_all EVERY_active_inst >> simp[] >> strip_tac >>
  simp[ret_taint_empty] >>
  irule step_taint_empty >> simp[] >> irule new_site_bytes_unchanged >>
  conj_tac
  >- (drule_all allocation_free_step_fmp_halt >> simp[]) >>
  irule allocation_free_step_allocas >>
  qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[]
QED

Theorem allocation_free_taint_within:
  EVERY (\fn. EVERY (\inst. allocation_free_opcode inst.inst_opcode)
                    (fn_insts fn)) ctx.ctx_functions /\
  vs.vs_allocas = FEMPTY ==> taint_within D ctx vs
Proof
  strip_tac >> simp[taint_within_def] >> conj_tac
  >- (rpt strip_tac >> drule_all allocation_free_reachable_taint >>
      simp[taint_empty_def]) >>
  rpt strip_tac >> drule_all allocation_free_final_taint >>
  simp[taint_empty_def]
QED
