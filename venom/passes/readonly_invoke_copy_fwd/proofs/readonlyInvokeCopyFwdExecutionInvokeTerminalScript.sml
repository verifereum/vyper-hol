(* A terminating callee propagates its Halt or Abort directly through INVOKE,
   including calls whose target argument list was rewritten. *)
Theory readonlyInvokeCopyFwdExecutionInvokeTerminal
Ancestors
  reachableFnSim passSimulationDefs
  venomExecSemantics venomState venomInst list

Theorem ricf_execution_invoke_terminal:
  fn_sim_below D vs C Ct R Rret (SUC k) /\
  MEM callee C.ctx_functions /\
  lookup_function callee.fn_name Ct.ctx_functions = SOME callee' /\
  R cstk cPG cG ctn callee cs ct /\
  block_reach vs C cstk cPG cG ctn callee cs /\
  ((?se. run_blocks k C callee cs = Halt se) \/
   (?ab se. run_blocks k C callee cs = Abort ab se)) /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  j.inst_opcode = INVOKE /\ decode_invoke j = SOME (callee.fn_name,ops') /\
  eval_operands ops' t = SOME args' /\ setup_callee callee' args' t = SOME ct ==>
  ?m. block_step_rel D vs C P Pret stk PG fn
    (step_inst k C i s) (step_inst m Ct j t)
Proof
  strip_tac >>
  `terminates (run_blocks k C callee cs)` by
    (gvs[terminates_def]) >>
  qpat_x_assum `fn_sim_below _ _ _ _ _ _ _` mp_tac >>
  simp[fn_sim_below_def] >>
  disch_then (qspecl_then
    [`k`,`cstk`,`cPG`,`cG`,`ctn`,`callee`,`callee'`,`cs`,`ct`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> qexists_tac `m` >>
  Cases_on `run_blocks k C callee cs` >>
  Cases_on `run_blocks m Ct callee' ct` >>
  gvs[fn_run_rel_def] >>
  PURE_ONCE_REWRITE_TAC [step_inst_def] >> fs[] >>
  fs[block_step_rel_def, fn_run_rel_def]
QED
