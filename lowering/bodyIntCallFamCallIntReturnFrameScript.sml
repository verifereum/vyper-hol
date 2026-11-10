(* Spatial boundaries for the nested internal call's return. *)
Theory bodyIntCallFamCallIntReturnFrame
Ancestors
  bodyIntCallSeamDefs intCallFrame exprSimDefs compileEnv intCallResult
  exprLowering venomExecSemantics vyperImmutableMetadataFrame
  vyperInterpreter vyperState gasSummary

Theorem marked_exec_immutable_metadata:
  (!st result fin. source st = (result,fin) ==>
     immutable_metadata_frame st fin) /\
  gas_marked_exec memory (ctx,func) source (es,s) marks res ee r ==>
  immutable_metadata_frame es ee
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  first_x_assum drule >> simp[immutable_metadata_frame_def] >>
  metis_tac[]
QED

Theorem intcall_callee_src_metadata:
  intcall_callee_src cx name ss es = (res,ee) ==>
  immutable_metadata_frame es ee
Proof
  strip_tac >>
  Cases_on `eval_stmts (cx with stk updated_by CONS (NONE,name)) ss es` >>
  rename1 `eval_stmts _ _ _ = (result0,st)` >>
  `immutable_metadata_frame es st` by
    (irule (cj 2 eval_metadata_frame_with_results) >>
     goal_assum (drule_at Any)) >>
  Cases_on `result0` >>
  gvs[intcall_callee_src_def, try_def, ignore_bind_def, bind_def, return_def] >>
  rename1 `handle_function ex st = _` >>
  Cases_on `ex` >>
  gvs[handle_function_def, return_def, raise_def]
QED

Theorem intcall_callee_exit_protected:
  allocas_above lo t /\
  (!a k. P a k ==> a + k <= lo) /\
  intcall_callee_exit func ce cx rtv rcn rb n m t res ee (IntRet ir cs) ==>
  !a k. P a k ==>
    mem_bytes_at a k cs.vs_memory = mem_bytes_at a k t.vs_memory
Proof
  simp[intcall_callee_exit_def, expr_exit_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  `a + k <= lo` by metis_tac[] >>
  qpat_x_assum `!b sz. _ ==> mem_bytes_at _ _ _ = _` irule >>
  fs[allocas_above_def] >> rpt strip_tac
  >~ [`regions_disjoint _ _ _ _`]
  >- (simp[regions_disjoint_def] >>
      `lo <= off` by metis_tac[] >> decide_tac) >>
  decide_tac
QED

Theorem intcall_callee_exit_protected_merge:
  allocas_above lo t /\
  (!a k. P a k ==> a + k <= lo) /\
  intcall_callee_exit func ce cx rtv rcn rb n m t res ee (IntRet ir cs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  !a k. P a k ==>
    mem_bytes_at a k u.vs_memory = mem_bytes_at a k t.vs_memory
Proof
  strip_tac >> drule invoke_return_frame >> strip_tac >>
  simp[] >> metis_tac[intcall_callee_exit_protected]
QED

(* Attach resources to a specified straight-line store witness.  Equality
   of run_inst_seq results is functional; no uniqueness of gas_path normal
   endpoints is asserted.  The caller can then count this very witness. *)
Theorem intcall_store_results_resources:
  store_multi_results buf ops off sa = ((),sb) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  (!x. MEM (Var x) ops ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  MAP (\op. eval_operand op s) ops = MAP SOME ws /\
  b + off + 32 * LENGTH ops < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  allocas_above lo s /\
  (!a k. P a k ==> a + k <= b + off \/ b + off + 32 * LENGTH ops <= a) ==>
  allocas_above lo u /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!a k. P a k ==> mem_bytes_at a k u.vs_memory = mem_bytes_at a k s.vs_memory)
Proof
  strip_tac >> drule store_multi_results_run >>
  disch_then (qspecl_then [`s`,`b`,`ws`] mp_tac) >>
  simp[] >> strip_tac >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     disch_then (fn th =>
       mp_tac (Q.AP_TERM `\z:venom_state. (z.vs_allocas,z.vs_alloca_next)` th)) >>
     simp[]) >>
  fs[allocas_above_def] >> metis_tac[]
QED
