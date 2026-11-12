(* Successful counted paths never lower the current allocation frontier. *)
Theory bodyIntCallFamStmtForFrontier
Ancestors
  fragGasMode fragGasPath intCallFrame venomMemProps venomExecProofs
  venomExecSemantics venomState venomInst arithmetic

Theorem intcall_step_frontier_mono:
  step_inst fuel ctx inst s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule step_inst_alloca_alloca_next_mono >>
      qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[is_alloca_op_def]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_next] >> simp[]
QED

Resume intcall_step_frontier_mono[invoke]:
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once run_defs, AllCaseEqs()] >> strip_tac >>
  drule invoke_return_frame >> simp[]
QED
Finalise intcall_step_frontier_mono

Theorem intcall_gas_edge_frontier_mono:
  gas_path_edge ctx func s n (OK t) ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  rw[gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >- (drule intcall_step_frontier_mono >> simp[])
  >- (drule eval_phis_preserves_alloca_fields >> strip_tac >>
      drule intcall_step_frontier_mono >> simp[])
  >- simp[jump_to_def] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[fragExecTheory.exit_result_def]
QED

Theorem intcall_gas_path_frontier_mono:
  gas_path ctx func s n (OK t) ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  `!ctx func s n r. gas_path ctx func s n r ==>
     !t. r = OK t ==> s.vs_alloca_next <= t.vs_alloca_next`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- (rpt strip_tac >> gvs[] >>
      drule intcall_gas_edge_frontier_mono >> strip_tac >>
      decide_tac) >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def]
QED

Theorem intcall_marked_path_frontier_mono:
  gas_marked_path mode ctx func s n (OK t) ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule gas_marked_path_exec >>
  metis_tac[intcall_gas_path_frontier_mono]
QED
