Theory lowerDloadPtrNormalReturn
Ancestors lowerDloadPtrReturn lowerDloadPtrNormalPush lowerDloadPtrSupport
  venomExecSemantics list rich_list pred_set

Theorem dload_normal_return:
  dload_boundary_core lo (e::f::fs)
    (set (fn_ir_vars fn) DIFF {a | retpc_var fn a})
    (MAP (\cc. set (fn_ir_vars cc.cf_fn) DIFF {a | retpc_var cc.cf_fn a}) (c::cs))
    PG PH G H tn un s t (c::cs) (d::ds) /\
  frame_reachable vs0 C (c::cs) PG G tn fn ri s /\ active_inst fn ri s /\
  ri.inst_opcode = RET /\ ptr_use_ok P pv ri /\ FDOM G SUBSET pv /\ taint_ok fn tn ri s /\
  (!a. MEM (Var a) (FRONT ri.inst_operands) ==>
    a IN (set (fn_ir_vars fn) DIFF {a | retpc_var fn a})) /\
  (!a. MEM (Var a) ri.inst_operands ==> (lookup_var a s = NONE <=> lookup_var a t = NONE)) /\
  step_inst fuel Ct ri t = IntRet rt t /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) d.cf_fn.fn_blocks) /\
  bind_outputs d.cf_inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state d.cf_state t)) = SOME t' /\
  active_inst d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) /\
  LENGTH (e::f::fs) = SUC (LENGTH (c::cs)) /\ LENGTH (c::cs) = LENGTH (d::ds) /\
  (!k. k < LENGTH (e::f::fs) ==>
    (EL k (e::f::fs)).dr_scratch =
      FDOM (EL k (t::MAP (\dd. dd.cf_state) (d::ds))).vs_allocas DIFF
      {id | ?i. MEM i (fn_insts (EL k (fn::MAP (\cc. cc.cf_fn) (c::cs)))) /\
                i.inst_id = id}) /\
  (!k. k < LENGTH (c::cs) ==>
    let cc = EL k (c::cs); dd = EL k (d::ds) in
    dload_live_layout lo cc.cf_state.vs_alloca_next dd.cf_state.vs_alloca_next
      (DROP (SUC k) (e::f::fs)) /\
    dload_equal_environment cc.cf_state dd.cf_state /\
    cc.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    cc.cf_inst = dd.cf_inst /\
    (!a. a IN set (fn_ir_vars cc.cf_fn) ==>
      (lookup_var a cc.cf_state = NONE <=> lookup_var a dd.cf_state = NONE)) /\
    (?qc. ir_supply_covers_fn qc cc.cf_fn /\
      (?qc'. lower_dload_function_supply qc cc.cf_fn = (dd.cf_fn,qc')) /\
      dload_control_match qc cc.cf_fn dd.cf_fn cc.cf_state dd.cf_state
        cc.cf_inst [cc.cf_inst] 0)) /\
  (!h. MEM h C.ctx_functions ==> fn_ptr_ok P h) ==>
  ?rs s' i emitted qc.
    step_inst fuel C ri s = IntRet rs s /\ rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    bind_outputs c.cf_inst.inst_outputs rs.iret_values
      (adopt_return_fmp rs (merge_callee_state c.cf_state s)) = SOME s' /\
    dload_boundary_core lo (f::fs)
      (set (fn_ir_vars c.cf_fn) DIFF {a | retpc_var c.cf_fn a})
      (MAP (\cc. set (fn_ir_vars cc.cf_fn) DIFF {a | retpc_var cc.cf_fn a}) cs)
      c.cf_params d.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (DRESTRICT d.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs)))
      (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) cs ds /\
    dload_control_match qc c.cf_fn d.cf_fn
      (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) i emitted 0 /\ j = HD emitted /\
    frame_reachable vs0 C cs c.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      c.cf_fn i (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx) /\
    (!a. a IN set (fn_ir_vars c.cf_fn) ==>
      (lookup_var a (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx) = NONE <=>
       lookup_var a (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) = NONE)) /\
    (!k. k < LENGTH cs ==> dload_live_layout lo
      (EL k cs).cf_state.vs_alloca_next (EL k ds).cf_state.vs_alloca_next
      (DROP (SUC k) (f::fs))) /\
    ir_supply_covers_fn qc c.cf_fn /\
    (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
    LENGTH (f::fs) = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH (f::fs) ==>
      (EL k (f::fs)).dr_scratch =
        FDOM (EL k ((t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx)::
          MAP (\dd. dd.cf_state) ds)).vs_allocas DIFF
        {id | ?i. MEM i (fn_insts (EL k (c.cf_fn::MAP (\cc. cc.cf_fn) cs))) /\
                  i.inst_id = id}) /\
    (!k. k < LENGTH cs ==>
      let cc = EL k cs; dd = EL k ds in
      dload_live_layout lo cc.cf_state.vs_alloca_next dd.cf_state.vs_alloca_next
        (DROP (SUC k) (f::fs)) /\
      dload_equal_environment cc.cf_state dd.cf_state /\
      cc.cf_state.vs_call_ctx.cc_address =
        (s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx).vs_call_ctx.cc_address /\
      cc.cf_inst = dd.cf_inst /\
      (!a. a IN set (fn_ir_vars cc.cf_fn) ==>
        (lookup_var a cc.cf_state = NONE <=> lookup_var a dd.cf_state = NONE)) /\
      (?q. ir_supply_covers_fn q cc.cf_fn /\
        (?q'. lower_dload_function_supply q cc.cf_fn = (dd.cf_fn,q')) /\
        dload_control_match q cc.cf_fn dd.cf_fn cc.cf_state dd.cf_state
          cc.cf_inst [cc.cf_inst] 0)) /\
    FDOM (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs))) SUBSET fn_pv P c.cf_fn /\
    (!k b sz. k < LENGTH c.cf_params /\ EL k c.cf_params = SOME (b,sz) ==>
      k IN P c.cf_fn.fn_name) /\
    (!cc. MEM cc cs ==> FDOM cc.cf_prov SUBSET fn_pv P cc.cf_fn) /\
    (!cc k b sz. MEM cc cs /\ k < LENGTH cc.cf_params /\
      EL k cc.cf_params = SOME (b,sz) ==> k IN P cc.cf_fn.fn_name)
Proof
  strip_tac >>
  qpat_assum `!k. k < LENGTH (c::cs) ==> _`
    (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])) >>
  `!k. k < LENGTH (c::cs) ==> dload_live_layout lo
    (EL k (c::cs)).cf_state.vs_alloca_next
    (EL k (d::ds)).cf_state.vs_alloca_next (DROP (SUC k) (e::f::fs))` by
    (rpt strip_tac >>
     qpat_assum `!k. k < LENGTH (c::cs) ==> _`
       (qspec_then `k` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])) >> gvs[]) >>
  rule_assum_tac (PURE_REWRITE_RULE [MAP]) >>
  drule_all (Q.INST [`U` |-> `set (fn_ir_vars c.cf_fn)`] dload_actual_return) >>
  strip_tac >> qexistsl_tac [`rs`, `s'`, `i`, `emitted`, `qc`] >> gvs[] >>
  conj_tac >- suspend "stack" >>
  conj_tac >- suspend "saved" >>
  suspend "support"
QED

Resume dload_normal_return[stack]:
  `t'.vs_allocas = d.cf_state.vs_allocas` by
    (qpat_assum `bind_outputs _ _ _ = SOME t'`
       (mp_then Any mp_tac dload_bind_outputs_frame) >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!k. k < SUC (SUC _) ==> _`
    (qspec_then `SUC k` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  Cases_on `k` >> gvs[]
QED

Resume dload_normal_return[saved]:
  `s'.vs_call_ctx = c.cf_state.vs_call_ctx` by
    (qpat_assum `bind_outputs _ _ _ = SOME s'`
       (mp_then Any mp_tac dload_bind_outputs_frame) >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!k. k < SUC _ ==> dload_equal_environment _ _ /\ _`
    (qspec_then `SUC k` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Resume dload_normal_return[support]:
  qpat_assum `frame_reachable vs0 C cs _ _ _ c.cf_fn i _`
    (mp_then Any mp_tac frame_reachable_prov_supported) >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >>
  strip_tac >> rpt conj_tac >> rpt strip_tac >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED

Finalise dload_normal_return
