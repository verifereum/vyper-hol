(* Successful calls restore the caller allocation map. Partial allocation
   history therefore survives actual step_inst execution, including INVOKE. *)
Theory abiAllocationHistoryRun
Ancestors
  abiAllocationHistory abiAllocationHistoryCode venomInstProofs1
  venomExecSemantics venomState venomInst finite_map list relation

Theorem abi_alloca_history_bind_outputs:
  bind_outputs outs vals s = SOME t ==> t.vs_allocas = s.vs_allocas
Proof
  mp_tac (Q.ISPEC `\s:venom_state. s.vs_allocas` bind_outputs_preserves) >>
  simp[update_var_def] >>
  disch_then (qspecl_then [`outs`, `vals`, `s`, `t`] ACCEPT_TAC)
QED

Theorem abi_alloca_history_invoke:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs()] >>
  drule abi_alloca_history_bind_outputs >>
  simp[merge_callee_state_def]
QED

Theorem abi_alloca_history_step_inst:
  abi_alloca_history code s /\ MEM inst code /\
  step_inst fuel ctx inst s = OK t ==> abi_alloca_history code t
Proof
  Cases_on `inst.inst_opcode = INVOKE` >> strip_tac
  >- (drule_all abi_alloca_history_invoke >> strip_tac >>
      drule_all abi_alloca_history_frame >> simp[]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  drule_all abi_alloca_history_step >> simp[]
QED

Theorem abi_alloca_history_step_reachable:
  !s t. RTC (\s t. ?fuel inst. MEM inst code /\
    step_inst fuel ctx inst s = OK t) s t ==>
    abi_alloca_history code s ==> abi_alloca_history code t
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac >>
  drule_all abi_alloca_history_step_inst >> strip_tac >>
  first_x_assum irule >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_ALLOCATION_HISTORY_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI allocation history run not kernel closed: " ^ n)
  end) (DB.thms "abiAllocationHistoryRun");

