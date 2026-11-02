(* Semantic boundaries for DFT frame-prefix simulation. *)
Theory dftFrameFacts
Ancestors
  dftDefs unitShapeDefs venomExecSemantics venomWf venomState venomInst
  venomEffects finite_map list option o1PassLift ctxLookupAgreeHelpers
  contextCodegenRel codegenRel unitMemInv venomMemProps

Theorem dft_operand_defined:
  (!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) ops ==> l IN FDOM s.vs_labels) /\
  MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_DEF, option_CASES]
QED

Theorem dft_operands_defined[local]:
  (!op. MEM op ops ==> ?w. eval_operand op s = SOME w) ==>
  ?ws. eval_operands ops s = SOME ws
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> simp[] >> metis_tac[]
QED

Theorem dft_movable_step_total:
  inst_wf i /\ inst_shape_ok i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ ~is_fallible i /\
  i.inst_opcode <> ALLOCA /\
  (!v. MEM (Var v) i.inst_operands ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels) ==>
  ?t. step_inst fuel C i s = OK t
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> ?w. eval_operand op s = SOME w`
    by metis_tac[dft_operand_defined] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_fallible_def, opcode_fail_class_def, is_pseudo_def,
      is_terminator_def, inst_shape_ok_def] >>
  qpat_x_assum `inst_wf i` mp_tac >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [inst_wf_def, TypeBase.case_def_of ``:opcode``] >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[exec_ext_call_def, LET_THM] >>
  rpt pairarg_tac >> gvs[] >>
  simp[REVERSE_APPEND, AllCaseEqs()] >>
  metis_tac[dft_operands_defined, MEM_REVERSE]
QED

Theorem dft_mem_corr_trans:
  mem_corr i s j t /\ mem_corr j t k u ==> mem_corr i s k u
Proof
  rw[mem_corr_def] >> metis_tac[]
QED

Theorem dft_call_corr_trans:
  call_corr i s j t /\ call_corr j t k u ==> call_corr i s k u
Proof
  rw[call_corr_def] >> gvs[] >> metis_tac[]
QED

Theorem dft_frame_reach_initial_fmp:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    s.vs_initial_fmp = s0.vs_initial_fmp
Proof
  ho_match_mp_tac frame_reach_ind >> rpt strip_tac >>
  imp_res_tac enters_block_initial_fmp >>
  imp_res_tac step_inst_initial_fmp >> simp[]
QED

Theorem dft_fold_update_alloca_fields[local]:
  !xs s. (FOLDL (\s (x,v). update_var x v s) s xs).vs_allocas = s.vs_allocas /\
         (FOLDL (\s (x,v). update_var x v s) s xs).vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >>
  simp[update_var_def]
QED

Theorem dft_bind_outputs_alloca_fields[local]:
  bind_outputs outs vals s = SOME t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[bind_outputs_def] >> strip_tac >>
  gvs[AllCaseEqs(), dft_fold_update_alloca_fields]
QED

Theorem dft_step_alloca_fields:
  i.inst_opcode <> ALLOCA /\ step_inst fuel C i s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def] >> strip_tac >> gvs[AllCaseEqs()] >>
      drule dft_bind_outputs_alloca_fields >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[merge_callee_state_def, adopt_return_fmp_def]) >>
  `step_inst_base i s = OK t` by metis_tac[step_inst_non_invoke] >>
  metis_tac[step_inst_base_preserves_allocas,
            step_inst_base_preserves_alloca_next]
QED

Theorem dft_eval_phis_alloca_fields[local]:
  !is s t. eval_phis s is = OK t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >> simp[Once eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[update_var_def] >>
  metis_tac[]
QED

Theorem dft_enters_block_alloca_fields[local]:
  enters_block fn s t ==>
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  rw[enters_block_def] >> drule dft_eval_phis_alloca_fields >> simp[]
QED

Theorem dft_frame_reach_alloca_fields:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
    EVERY (\i. i.inst_opcode <> ALLOCA) (fn_insts fn) ==>
    s.vs_allocas = s0.vs_allocas /\ s.vs_alloca_next = s0.vs_alloca_next
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- metis_tac[dft_enters_block_alloca_fields]
  >- (drule frame_reach_active >> strip_tac >>
      `i.inst_opcode <> ALLOCA` by (drule_all EVERY_active_inst >> simp[]) >>
      drule_all dft_step_alloca_fields >> simp[])
  >> drule frame_reach_active >> strip_tac >>
  `i.inst_opcode <> ALLOCA` by (drule_all EVERY_active_inst >> simp[]) >>
  drule_all dft_step_alloca_fields >> strip_tac >>
  drule dft_enters_block_alloca_fields >> simp[]
QED

Theorem dft_eval_operands_cong[local]:
  !ops s t.
    (!op. MEM op ops ==> eval_operand op s = eval_operand op t) ==>
    eval_operands ops s = eval_operands ops t
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  first_x_assum (drule_then (fn th => rewrite_tac[th]))
QED

Theorem dft_source_read_ranges_cong[local]:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  source_memory_read_ranges i s = source_memory_read_ranges i t
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  simp[source_memory_read_ranges_def] >>
  simp[dret_memory_read_ranges_def, memory_range_of_operands_def] >>
  simp[Cong list_case_cong]
  >- (drule dft_eval_operands_cong >> disch_then (fn th => rewrite_tac[th])) >>
  Cases_on `i.inst_operands` >> simp[] >>
  rename1 `i.inst_operands = h::ops` >> Cases_on `h` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `!op. MEM op (REVERSE ops) ==> eval_operand op s = eval_operand op t`
    by (rpt strip_tac >> first_x_assum irule >> gvs[MEM_REVERSE]) >>
  `eval_operands (DROP 2 (REVERSE ops)) s =
   eval_operands (DROP 2 (REVERSE ops)) t`
    by (irule dft_eval_operands_cong >> rpt strip_tac >>
        qpat_x_assum `!op. MEM op (REVERSE ops) ==> _` irule >>
        gvs[MEM_DROP] >> once_rewrite_tac[GSYM MEM_REVERSE] >>
        pure_rewrite_tac[MEM_EL] >> qexists_tac `m + 2` >> simp[]) >>
  `eval_operand (HD (REVERSE ops)) s = eval_operand (HD (REVERSE ops)) t`
    by (first_x_assum irule >> Cases_on `REVERSE ops` >> gvs[]) >>
  `eval_operand (EL 1 (REVERSE ops)) s = eval_operand (EL 1 (REVERSE ops)) t`
    by (first_x_assum irule >> pure_rewrite_tac[MEM_EL] >>
        qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[]
QED

Theorem dft_source_write_ranges_cong[local]:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (i.inst_opcode = DRET ==> s.vs_call_entry_fmp = t.vs_call_entry_fmp) ==>
  source_memory_write_ranges i s = source_memory_write_ranges i t
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  simp[source_memory_write_ranges_def] >>
  simp[fixed_source_write_range_def, sized_source_write_range_def] >>
  simp[Cong list_case_cong]
  >- (drule dft_eval_operands_cong >> disch_then (fn th => rewrite_tac[th]) >>
      simp[])
QED

Theorem dft_inst_mem_ranges_cong:
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (i.inst_opcode = DRET ==> s.vs_call_entry_fmp = t.vs_call_entry_fmp) ==>
  inst_mem_ranges i s = inst_mem_ranges i t
Proof
  strip_tac >> simp[inst_mem_ranges_def] >>
  drule dft_source_read_ranges_cong >>
  drule_all dft_source_write_ranges_cong >> simp[]
QED

Theorem dft_mem_corr_same_inst:
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
  t.vs_initial_fmp = s.vs_initial_fmp /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (i.inst_opcode = DRET ==> s.vs_call_entry_fmp = t.vs_call_entry_fmp) ==>
  mem_corr i s i t
Proof
  strip_tac >> drule_all dft_inst_mem_ranges_cong >> simp[mem_corr_def]
QED
