(* Installed entry checks either revert empty or reach positional registration. *)
Theory calldataNoneSelectedChecks
Ancestors entryChecksRejectJoint entryChecksPassPtr actualEntryAllocationFrame
  moduleLowering moduleLoweringProps compileEnv exprLoweringProps fragExec
  fragGasOriginPtr ptrDiscipline ptrSafeRun venomState words arithmetic list

Theorem selected_checks_reject_or_continue:
  compile_entry_checks m pay opened = ((),checked) /\
  fn_has_code opened checked fn /\ fresh_vars_wrt opened s /\
  ~s.vs_halted /\ s.vs_current_bb = opened.cs_current_bb /\
  s.vs_inst_idx = LENGTH opened.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  m < dimword (:256) /\ LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  4 <= LENGTH s.vs_call_ctx.cc_calldata ==>
  (?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (Abort Revert_abort z,H,u)) \/
  (?t H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK t,H,u)) /\
    m <= LENGTH s.vs_call_ctx.cc_calldata /\
    vars_pc_only s t /\ fresh_vars_wrt checked t /\ ~t.vs_halted /\
    t.vs_current_bb = checked.cs_current_bb /\
    t.vs_inst_idx = LENGTH checked.cs_current_insts /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
    allocas_from lo t /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm)
Proof
  strip_tac >>
  Cases_on `(pay \/ s.vs_call_ctx.cc_callvalue = 0w) /\
            m <= LENGTH s.vs_call_ctx.cc_calldata`
  >- (disj2_tac >> gvs[] >>
      drule compile_entry_checks_ptr_endpoint >>
      disch_then (qspecl_then [`tn`, `s`, `lo`, `fn`, `ctx`, `PG`, `G`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qx_choosel_then [`t`, `H`, `u`] strip_assume_tac) >>
      qexistsl_tac [`t`, `H`, `u`] >> simp[] >>
      metis_tac[vars_pc_only_fields, vars_pc_only_allocas]) >>
  disj1_tac >>
  irule compile_entry_checks_reject_joint >> simp[] >>
  qexistsl_tac [`checked`, `m`, `pay`, `opened`] >> simp[] >>
  Cases_on `m <= LENGTH s.vs_call_ctx.cc_calldata`
  >- gvs[] >>
  disj2_tac >> decide_tac
QED
