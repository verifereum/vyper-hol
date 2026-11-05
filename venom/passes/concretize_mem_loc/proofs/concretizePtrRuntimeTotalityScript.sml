Theory concretizePtrRuntimeTotality
Ancestors
  concretizePtrStepTotality concretizePtrPhiTotality
  ptrDiscipline contextCodegenRel venomExecSemantics venomState
  o1PassContract unitTransformDefs pointerConfinedDefs allocaRemapSSA venomWf venomExecProps finite_map pred_set list

Theorem initial_phis_identity:
  !insts s'. s.vs_prev_bb = NONE /\ eval_phis s insts = OK s' ==> s' = s
Proof
  Cases >> simp[eval_phis_def, eval_one_phi_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem initial_entry_empty[local]:
  s.vs_prev_bb = NONE /\ s.vs_vars = FEMPTY /\ enters_block fn s s1 ==>
  s1.vs_vars = FEMPTY
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule_all initial_phis_identity >> strip_tac >> gvs[]
QED

Theorem invoke_outputs_not_local[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  MEM v inst.inst_outputs ==> v NOTIN pointer_derived_vars fn (alloca_roots fn)
Proof
  rpt strip_tac >> drule_all local_output_origin >>
  simp[is_pointer_preserving_op_def]
QED

Theorem fold_updates_non_output[local]:
  !kvs s. ~MEM v (MAP FST kvs) ==>
  lookup_var v (FOLDL (\s' (out,x). update_var out x s') s kvs) = lookup_var v s
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem bind_outputs_non_output[local]:
  bind_outputs outs vals s = SOME s' /\ ~MEM v outs ==>
    lookup_var v s' = lookup_var v s
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  `MAP FST (ZIP (outs,vals)) = outs` by (irule (cj 1 MAP_ZIP) >> simp[]) >>
  gvs[] >> irule fold_updates_non_output >> simp[]
QED

Definition pure_local_total_def:
  pure_local_total P fn s G <=>
  !v w. v IN (pointer_derived_vars fn (alloca_roots fn) DIFF
               pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)) /\
        lookup_var v s = SOME w ==> ?site. FLOOKUP G v = SOME site
End

Theorem pure_local_return[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  pure_local_total P fn s G /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' ==>
  pure_local_total P fn s' (DRESTRICT G (COMPL (set inst.inst_outputs)))
Proof
  simp[pure_local_total_def] >> rpt strip_tac >>
  `~MEM v inst.inst_outputs` by metis_tac[invoke_outputs_not_local, IN_DIFF] >>
  drule_all bind_outputs_non_output >>
  simp[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def] >>
  Cases_on `ret.iret_adopt_fmp` >> simp[] >> strip_tac >>
  simp[FLOOKUP_DRESTRICT] >> gvs[lookup_var_def] >> metis_tac[]
QED

Theorem pure_local_next[local]:
  fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' /\ pure_local_total P fn s G ==>
  pure_local_total P fn s' (step_prov PG G inst s')
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >> simp[]) >>
  gvs[pure_local_total_def] >> rpt strip_tac >>
  irule ptr_pure_local_step_totality >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[IN_DIFF]
QED

Theorem pure_local_block[local]:
  fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
  enters_block fn s' s1 /\ pure_local_total P fn s G ==>
  pure_local_total P fn s1 (entry_prov fn s' G)
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `pure_local_total P fn s' G` by
    (gvs[pure_local_total_def] >> metis_tac[step_terminator_preserves_vars]) >>
  gvs[pure_local_total_def, lookup_var_def, entry_prov_def] >>
  rewrite_tac[GSYM lookup_var_def] >> rpt strip_tac >>
  irule ptr_pure_local_phis_totality >> conj_tac >- metis_tac[] >>
  qexistsl_tac [`pointer_derived_vars fn (alloca_roots fn)`, `P`,
    `pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)`, `fn`] >>
  simp[lookup_var_def] >> metis_tac[]
QED

Definition pure_local_saved_def:
  pure_local_saved P ctx f <=>
  MEM f.cf_fn ctx.ctx_functions /\
  MEM f.cf_inst (fn_insts f.cf_fn) /\ f.cf_inst.inst_opcode = INVOKE /\
  pure_local_total P f.cf_fn f.cf_state f.cf_prov
End

Theorem frame_pure_local_total:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  o1_run_state_ok vs /\ EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions ==>
  MEM fn ctx.ctx_functions /\ pure_local_total P fn s G /\
  EVERY (pure_local_saved P ctx) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_pure_local_total[entry]:
  rpt gen_tac >> strip_tac >> strip_tac >> simp[] >> conj_tac
  >- metis_tac[lookup_function_MEM] >>
  `vs.vs_vars = FEMPTY` by gvs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `s.vs_vars = FEMPTY` by
    (drule_at (Pos last) initial_entry_empty >> simp[]) >>
  simp[pure_local_total_def, lookup_var_def]
QED

Resume frame_pure_local_total[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  `fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn` by metis_tac[EVERY_MEM] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_def, MEM_EL, mem_fn_insts_intro] >>
  `pure_local_total P fn s' (step_prov PG G inst s')` by
    (irule pure_local_next >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[pure_local_total_def, lookup_var_def]
QED
Resume frame_pure_local_total[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  `fn_ptr_ok P fn /\ ssa_form fn /\ fn_inst_wf fn` by metis_tac[EVERY_MEM] >>
  simp[] >> irule pure_local_block >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Resume frame_pure_local_total[call]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[] >>
  `MEM fn' ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_def, MEM_EL, mem_fn_insts_intro] >>
  `cs.vs_prev_bb = NONE /\ cs.vs_vars = FEMPTY` by
    gvs[setup_callee_def, AllCaseEqs()] >>
  `s''.vs_vars = FEMPTY` by metis_tac[initial_entry_empty] >>
  gvs[pure_local_saved_def, pure_local_total_def, lookup_var_def]
QED
Resume frame_pure_local_total[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >> fs[pure_local_saved_def] >>
  `ssa_form f.cf_fn` by metis_tac[EVERY_MEM] >>
  `pure_local_total P f.cf_fn s'
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))` by
    (irule pure_local_return >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[pure_local_total_def, lookup_var_def]
QED
Finalise frame_pure_local_total

Theorem ptr_reachable_pure_local_totality:
  o1_run_state_ok vs /\ EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  !v w. v IN (pointer_derived_vars fn (alloca_roots fn) DIFF
               pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)) /\
        lookup_var v s = SOME w ==> ?site. FLOOKUP G v = SOME site
Proof
  strip_tac >> drule_all frame_pure_local_total >> simp[pure_local_total_def]
QED
