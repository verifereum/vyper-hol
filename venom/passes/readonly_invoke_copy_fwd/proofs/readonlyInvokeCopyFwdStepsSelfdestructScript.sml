Theory readonlyInvokeCopyFwdStepsSelfdestruct
Ancestors
  readonlyInvokeCopyFwdStepsControl readonlyInvokeCopyFwdRel
  o1LowerDloadHaltResult o1LowerDloadShared taintAgree ptrDiscipline codegenRel
  venomState venomExecSemantics internalReturnCopyFwdSim
  finite_map words list pred_set

(* SELFDESTRUCT changes accounts, clears returndata and halts.  In this IR
   it leaves pending deletions unchanged (the account update is not a no-op). *)
Theorem ricf_selfdestruct_footprint:
  inst.inst_opcode = SELFDESTRUCT /\ inst.inst_outputs = [] /\ step_inst fuel C inst s = Halt u ==>
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_pending_deletions = s.vs_pending_deletions /\
  step_taint inst s u tn = tn
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >> gvs[halt_state_def, set_returndata_def,
    step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
    mem_taint_def, set_var_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, range_bytes_def, DRESTRICT_UNIV,
    taint_component_equality, source_memory_write_ranges_def,
    FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

(* The shared-account primitive allows masked storage, not just account
   equality.  Saved frames explicitly use the same storage-owner address;
   this is a consumer premise, not a consequence of the certificate. *)
Theorem ricf_cert_selfdestruct_halt:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_opcode = SELFDESTRUCT /\ inst.inst_outputs = [] /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address) /\
  step_inst fuel C inst s = Halt u ==>
  ?v. step_inst fuel C' inst t = Halt v /\
    ricf_cert_return_core D ids stk maps targets curs un u v /\
    ircf_cross un cur u v
Proof
  strip_tac >>
  drule ricf_cert_return_boundary >> strip_tac >>
  `ld_shared_agree D s.vs_call_ctx.cc_address un s t /\
   s.vs_call_ctx = t.vs_call_ctx` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def, ricf_frame_agree_def,
       taint_agree_def, ricf_cert_return_core_def, ricf_live_return_core_def,
       venom_state_component_equality] >>
  drule_all ld_shared_selfdestruct_step >>
  disch_then (qspec_then `C'` strip_assume_tac) >>
  `u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
   step_taint inst s u un = un` by metis_tac[ricf_selfdestruct_footprint] >>
  `t1.vs_memory = t.vs_memory /\ t1.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ricf_selfdestruct_footprint] >>
  qexists_tac `t1` >> simp[] >>
  fs[ricf_cert_return_core_def, ricf_live_return_core_def] >>
  rpt conj_tac
  >- (irule ricf_live_stack_refresh >> reverse conj_tac
      >- (qexistsl [`s`, `t`, `un`] >> simp[]) >>
      simp[] >> rpt strip_tac >>
      gvs[ricf_live_stack_agree_def, ricf_live_frame_decompose,
          ircf_cross_def] >> metis_tac[]) 
  >- metis_tac[]
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >> gvs[ircf_cross_def] >> metis_tac[]
QED

Theorem ricf_cert_selfdestruct:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_opcode = SELFDESTRUCT /\ inst.inst_outputs = [] /\
  inst.inst_operands = [a] /\ ~s.vs_call_ctx.cc_static /\
  eval_operand a s = SOME beneficiary /\ eval_operand a t = SOME beneficiary /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address) ==>
  ?u v. step_inst fuel C inst s = Halt u /\
    step_inst fuel C' inst t = Halt v /\
    ricf_control_result D ids stk PG fn sites maps targets H un cur curs
      (Halt u) (Halt v)
Proof
  strip_tac >>
  `?u. step_inst fuel C inst s = Halt u` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  `!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t`
    by simp[] >>
  drule_all ricf_cert_selfdestruct_halt >>
  simp[] >> disch_then (qspec_then `C'` strip_assume_tac) >>
  simp[ricf_control_result_def]
QED
