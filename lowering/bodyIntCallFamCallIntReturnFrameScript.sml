(* Spatial boundaries for the nested internal call's return. *)
Theory bodyIntCallFamCallIntReturnFrame
Ancestors
  bodyIntCallSeamDefs intCallFrame exprSimDefs compileEnv

Theorem intcall_callee_exit_protected:
  allocas_above lo t /\
  (!a k. P a k ==> a + k <= lo) /\
  intcall_callee_exit func ce cx rtv rc rb n m t res ee (IntRet ir cs) ==>
  !a k. P a k ==>
    mem_bytes_at a k cs.vs_memory = mem_bytes_at a k t.vs_memory
Proof
  simp[intcall_callee_exit_def, expr_exit_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!b sz. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[allocas_above_def] >> conj_tac
  >- (first_x_assum drule >> decide_tac) >>
  rpt strip_tac >> simp[regions_disjoint_def] >>
  `lo <= off` by metis_tac[] >>
  `a + k <= lo` by metis_tac[] >> decide_tac
QED

Theorem intcall_callee_exit_protected_merge:
  allocas_above lo t /\
  (!a k. P a k ==> a + k <= lo) /\
  intcall_callee_exit func ce cx rtv rc rb n m t res ee (IntRet ir cs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  !a k. P a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k t.vs_memory
Proof
  strip_tac >> drule invoke_return_frame >> strip_tac >>
  simp[] >> drule_all intcall_callee_exit_protected >> simp[]
QED
