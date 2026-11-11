Theory lowerDloadPtrJointAllocClosure
Ancestors lowerDloadPtrNormalNext lowerDloadPtrJointAlloc lowerDloadPtrJointBudget lowerDloadPtrSupport
  lowerDloadPtrBlockEntry lowerDloadPtrCall lowerDloadPtrJointNext
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrRel lowerDloadPtrStatic
  lowerDloadDefs o1ContractLowerDload o1PassContract unitTransformDefs lowerDloadPtrRawReachable memSafeRun
  ptrDiscipline unitShapeDefs codegenRel venomExecSemantics venomState
  venomInst venomWf venomExecProps contextCodegenRel list rich_list pred_set finite_map

Theorem dload_alloca_success_lookup:
  i.inst_opcode = ALLOCA /\ step_inst fuel C i s = OK s1 ==>
  (!v. lookup_var v s1 = NONE <=>
    ~MEM v i.inst_outputs /\ lookup_var v s = NONE) /\
  s1.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem dload_joint_tracked_alloca_next:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  (?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
    i.inst_opcode = ALLOCA /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))) /\
  frame_reachable vs C' ds PH H un g j t /\
  active_inst g j t /\ ~is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
  step_inst fuel C' j t = OK t1 /\
  active_inst g next (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      (step_prov PH H j t1) (step_taint j t t1 un) /\
    dload_control_match q f g s (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      i emitted n /\ next = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH ds /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) ds)).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k ds in
      dload_live_layout lo c.cf_state.vs_alloca_next d.cf_state.vs_alloca_next
        (DROP (SUC k) fs) /\
      dload_equal_environment c.cf_state d.cf_state /\
      c.cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
      c.cf_inst = d.cf_inst /\
      (!a. a IN set (fn_ir_vars c.cf_fn) ==>
        (lookup_var a c.cf_state = NONE <=> lookup_var a d.cf_state = NONE)) /\
      (?qc. ir_supply_covers_fn qc c.cf_fn /\
        (?qc'. lower_dload_function_supply qc c.cf_fn = (d.cf_fn,qc')) /\
        dload_control_match qc c.cf_fn d.cf_fn c.cf_state d.cf_state
          c.cf_inst [c.cf_inst] 0))
Proof
  strip_tac >>
  `emitted = [i] /\ n = 0 /\ j = i` by
    (drule dload_control_match_expansion >> strip_tac >>
     qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gnvs[] >>
     `n = 0` by decide_tac >> gvs[]) >>
  gnvs[dload_prefix_zero] >>
  Cases_on `fs` >- gvs[] >> rename1 `LENGTH (r::rs) = _` >>
  `vs.vs_allocas = FEMPTY` by fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `SUM (MAP (\r. CARD r.dr_scratch) (r::rs)) <= ctx_dload_count C` by
    suspend "budget" >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     `MEM f C.ctx_functions` by
       (qpat_assum `frame_reachable vs C cs PG G tn f i s`
          (mp_then Any mp_tac frame_reachable_raw_certificate) >>
        simp[] >> strip_tac >> simp[]) >>
     fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, fn_shape_ok_def,
       wf_function_def, fn_labels_def]) >>
  `r.dr_scratch = FDOM t0.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)}` by
    (qpat_x_assum `!k. k < _ ==> (EL k (r::rs)).dr_scratch = _` (qspec_then `0` mp_tac) >>
     simp[EXTENSION] >> metis_tac[]) >>
  drule_at (Pat `dload_boundary_core`) dload_actual_alloca_boundary_next >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `active_inst`)) >>
  disch_then (drule_at (Pat `o1_src_inv`)) >> simp[] >> strip_tac >>
  `(!v. lookup_var v s1 = NONE <=> ~MEM v i.inst_outputs /\ lookup_var v s = NONE) /\
    s1.vs_call_ctx = s.vs_call_ctx` by
    (qpat_assum `step_inst fuel C i s = OK s1`
       (mp_then Any mp_tac dload_alloca_success_lookup) >> simp[]) >>
  `!v. lookup_var v t1 = NONE <=> ~MEM v i.inst_outputs /\ lookup_var v t0 = NONE` by
    (qpat_assum `step_inst fuel C' i t0 = OK t1`
       (mp_then Any mp_tac dload_alloca_success_lookup) >> simp[]) >>
  qpat_x_assum `dload_boundary_core _ (r::rs) _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `dload_boundary_core`) dload_normal_changed_head_successor >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (qspecl_then [`t0`,`s`,`r`,`HD emitted'`,`P`,`C'`] mp_tac) >>
  simp[EVERY_MEM] >> disch_then irule >>
  rpt strip_tac >> fs[EVERY_MEM, lookup_var_def] >> metis_tac[]
QED

Resume dload_joint_tracked_alloca_next[budget]:
  rpt strip_tac >>
  irule dload_joint_runtime_scratch_budget >>
  conj_tac >- metis_tac[] >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' ds PH H0 un0 g i t0`
    (irule_at (Pat `frame_reachable`)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k. k < _ ==> (EL k (r::rs)).dr_scratch = _`
        (qspec_then `k` mp_tac) >> simp[EXTENSION] >> metis_tac[]) >>
  suspend "budget_cover"
QED

Resume dload_joint_tracked_alloca_next[budget_cover]:
  rpt strip_tac >> Cases_on `k` >> simp[]
  >- metis_tac[] >>
  qpat_x_assum `!k. k < LENGTH ds ==> _` (qspec_then `n` mp_tac) >>
  simp[EL_MAP] >> metis_tac[]
QED

Finalise dload_joint_tracked_alloca_next
