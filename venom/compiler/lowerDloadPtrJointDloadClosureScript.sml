Theory lowerDloadPtrJointDloadClosure
Ancestors lowerDloadPtrJointBytesClosure lowerDloadPtrDloadOrigins
  lowerDloadPtrBackwardNext lowerDloadPtrNormalNext lowerDloadPtrReplay
  lowerDloadPtrSourceInv lowerDloadPtrStatic lowerDloadPtrPhase lowerDloadPtrRel
  lowerDloadDefs o1PassContract ptrDiscipline venomExecSemantics venomState
  lowerDloadPtrJointNext o1ContractLowerDload unitShapeDefs
  lowerDloadPtrRawReachable memSafeRun unitTransformDefs codegenRel
  contextCodegenRel venomInst venomWf venomExecProps irSupply
  venomFnScheduleRunner o1PassLift unitMemInv contextRawReachable
  lowerDloadPtrSupplyOrigins lowerDloadPtrRuntimeSupport lowerDloadPtrAggregate
  list rich_list pred_set finite_map

Theorem dload_joint_tracked_dload_complete_next:
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
    i.inst_opcode = DLOAD /\ SUC n = LENGTH emitted /\
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
  Cases_on `fs` >- gvs[] >> rename1 `LENGTH (r::rs) = _` >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
      (mp_then Any mp_tac frame_reachable_raw_certificate) >>
     simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `?off out. i.inst_operands = [off] /\ i.inst_outputs = [out]` by
    suspend "shape" >>
  `n = 3 /\ LENGTH emitted = 4` by
    (drule dload_control_match_expansion >> strip_tac >>
     qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `dload_prefix_match pfuel C' PH emitted 4 t0 H0 un0
     (t1 with vs_inst_idx := SUC t.vs_inst_idx)
     (step_prov PH H j t1) (step_taint j t t1 un)` by
    (qpat_x_assum `j = EL n emitted` SUBST_ALL_TAC >>
     drule_at (Pat `dload_prefix_match`) dload_prefix_extend_mixed >>
     disch_then (qspecl_then [`t1`,`fuel`,`C'`] mp_tac) >> simp[]) >>
  `?supply after av cv.
    lower_dload_inst_supply supply i = (emitted,after) /\
    (EL 0 emitted).inst_outputs = [av] /\ (EL 1 emitted).inst_outputs = [cv] /\
    av <> cv /\ av NOTIN set (fn_ir_vars f) /\ cv NOTIN set (fn_ir_vars f) /\
    (EL 0 emitted).inst_id NOTIN {ci.inst_id | MEM ci (fn_insts f)}` by
    suspend "supply" >>
  `fn_ptr_ok P f` by fs[EVERY_MEM] >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `!v. off = Var v ==> v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    suspend "operand" >>
  `off <> Var av` by
    (strip_tac >> gvs[] >> metis_tac[fn_ir_vars_operand, MEM]) >>
  `code_layout_valid s` by suspend "layout" >>
  `dload_offset_ok C f i s /\ dload_headroom_ok C f i s` by
    (conj_tac
     >- (qpat_assum `frame_reachable vs C cs PG G tn f i s`
           (mp_then Any mp_tac o1_src_frame_dload_offset_ok) >>
         disch_then (qspec_then `D` mp_tac) >> simp[]) >>
     qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac o1_src_frame_dload_headroom_ok) >>
     disch_then (qspec_then `D` mp_tac) >> simp[]) >>
  `FDOM s.vs_allocas SUBSET {ci.inst_id | MEM ci (fn_insts f)}` by
    suspend "source_domain" >>
  `r.dr_scratch = FDOM t0.vs_allocas DIFF {ci.inst_id | MEM ci (fn_insts f)}` by
    (qpat_x_assum `!k. k < LENGTH (r::rs) ==> _` (qspec_then `0` mp_tac) >>
     simp[EXTENSION] >> metis_tac[]) >>
  `(FLOOKUP t0.vs_allocas (EL 0 emitted).inst_id = NONE ==>
    t0.vs_alloca_next + 32 < dimword (:256))` by suspend "reserve" >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac dload_tracked_backward_next_fresh) >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_prefix_match _ _ _ _ 4 _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lower_dload_inst_supply`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (drule_at (Pat `i.inst_operands = _`)) >>
  disch_then (drule_at (Pat `i.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `r.dr_scratch = _`)) >>
  disch_then (drule_at (Pat `(EL 0 emitted).inst_outputs = _`)) >>
  disch_then (qspec_then `out` mp_tac) >>
  disch_then (drule_at (Pat `active_inst`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f)`,`P`] mp_tac) >>
  simp[] >> strip_tac >>
  `r1.dr_scratch = FDOM (t1 with vs_inst_idx := SUC t.vs_inst_idx).vs_allocas DIFF
    {ci.inst_id | MEM ci (fn_insts f)}` by suspend "target_domain" >>
  `(s1 with vs_inst_idx := SUC s.vs_inst_idx).vs_call_ctx.cc_address =
    s.vs_call_ctx.cc_address` by (drule_all dload_source_step_call_context >> simp[]) >>
  qpat_x_assum `dload_boundary_core _ (r::rs) _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `dload_boundary_core`) dload_normal_changed_head_successor >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (qspecl_then [`t0`,`s`,`r`,`next`,`P`,`C'`] mp_tac) >>
  simp[EVERY_MEM] >> disch_then irule >> fs[EVERY_MEM]
QED

Resume dload_joint_tracked_dload_complete_next[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >>
  Cases_on `i.inst_outputs` >> gvs[]
QED

Resume dload_joint_tracked_dload_complete_next[operand]:
  rpt strip_tac >> simp[] >> conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `MEM (Var v) i.inst_operands` by simp[] >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume dload_joint_tracked_dload_complete_next[supply]:
  rpt strip_tac >> drule_all dload_control_supply_origins >> simp[]
QED

Resume dload_joint_tracked_dload_complete_next[layout]:
  rpt strip_tac >> drule_all o1_src_frame_code_layout_valid >> simp[]
QED

Resume dload_joint_tracked_dload_complete_next[source_domain]:
  rpt strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (mp_then Any mp_tac dload_frame_alloca_support) >>
  simp[] >> strip_tac >>
  fs[SUBSET_DEF, MEM_MAP, MEM_FILTER, GSPECIFICATION] >> metis_tac[]
QED

Resume dload_joint_tracked_dload_complete_next[reserve]:
  rpt strip_tac >>
  `vs.vs_allocas = FEMPTY` by
    fs[o1_run_state_ok_def, o1_initial_state_ok_def] >>
  `dload_table_stack (r::rs) (s::MAP (\c. c.cf_state) cs)
    (t0::MAP (\d. d.cf_state) ds)` by fs[dload_boundary_core_def] >>
  irule dload_positive_prefix_fresh_reserve >>
  qpat_assum `frame_reachable vs C cs PG G tn f i s`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `frame_reachable vs C' ds PH H un g j t`
    (irule_at (Pat `frame_reachable`)) >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un`
    (irule_at (Pat `dload_prefix_match`)) >>
  qpat_assum `lower_dload_inst_supply supply i = (emitted,after)`
    (irule_at (Pat `lower_dload_inst_supply`)) >>
  qpat_assum `dload_table_stack (r::rs) _ _`
    (irule_at (Pat `dload_table_stack`)) >>
  qpat_assum `callee_first names C.ctx_functions`
    (irule_at (Pat `callee_first`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[EXTENSION] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `k`
  >- (simp[] >> metis_tac[]) >>
  fs[] >>
  qpat_x_assum `!k. k < LENGTH cs ==> _` (qspec_then `n'` mp_tac) >>
  simp[EL_MAP] >> metis_tac[]
QED

Resume dload_joint_tracked_dload_complete_next[target_domain]:
  rpt strip_tac >>
  qpat_assum `dload_prefix_match pfuel C' PH emitted 4 _ _ _ _ _ _`
    (mp_then (Pat `dload_prefix_match`) mp_tac dload_supply_prefix_alloca_domain) >>
  disch_then (drule_at (Pat `lower_dload_inst_supply`)) >>
  simp[] >> strip_tac >> fs[] >>
  `~(?ci. (HD emitted).inst_id = ci.inst_id /\ MEM ci (fn_insts f))` by metis_tac[] >>
  simp[]
QED

Finalise dload_joint_tracked_dload_complete_next
