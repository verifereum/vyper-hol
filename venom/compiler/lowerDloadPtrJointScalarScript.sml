Theory lowerDloadPtrJointScalar
Ancestors lowerDloadPtrScalar lowerDloadPtrBump lowerDloadPtrCall lowerDloadPtrNormalNext
  lowerDloadPtrJointInterior lowerDloadPtrOrdinary lowerDloadPtrJointNext
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrRel lowerDloadPtrStatic
  lowerDloadDefs o1ContractLowerDload o1PassContract lowerDloadPtrRawReachable
  ptrDiscipline unitShapeDefs codegenRel venomExecSemantics venomState
  venomInst venomWf contextCodegenRel list rich_list pred_set finite_map

Theorem dload_original_nonopaque_operands:
  opaque_use_ok f /\ MEM i (fn_insts f) /\
  ~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET] ==>
  !v. MEM (Var v) i.inst_operands ==>
    v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})
Proof
  rpt strip_tac >> simp[] >> conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Theorem dload_joint_tracked_scalar_next:
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
    MEM i.inst_opcode [LT; GT; EQ; MUL; Div; SDIV; Mod; SMOD; Exp;
      ADDMOD; MULMOD; SLT; SGT; ISZERO; AND; OR; XOR; NOT; SIGNEXTEND; BYTE; OFFSET; BUMP] /\
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
     `i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES` by
       (qpat_x_assum `MEM i.inst_opcode _` mp_tac >>
        rpt (pop_assum kall_tac) >> simp[MEM] >> rpt strip_tac >> gvs[]) >>
     simp[lower_dload_inst_supply_def] >>
     rpt strip_tac >> gnvs[] >>
     `n = 0` by decide_tac >> gvs[]) >>
  gnvs[dload_prefix_zero] >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
       fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  `?s1. step_inst fuel C i s = OK s1 /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t1 with vs_inst_idx := SUC t0.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH (step_prov PG G i s1) (step_prov PH H0 i t1)
      (step_taint i s s1 tn) (step_taint i t0 t1 un0)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t0.vs_inst_idx) cs ds /\
    s1 = s with vs_vars := s1.vs_vars /\
    t1 = t0 with vs_vars := t1.vs_vars` by suspend "semantic" >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ G _ _ _ _ _ _ _` kall_tac >>
  drule_at (Pat `dload_boundary_core`) dload_normal_unchanged_successor >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (qspecl_then [`t0`,`s`,`next`,`P`,`C'`] mp_tac) >>
  simp[EVERY_MEM, EL] >>
  (impl_tac >- (conj_tac >- fs[EVERY_MEM] >>
    conj_tac >- (qpat_x_assum `t1 = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
    qpat_x_assum `s1 = _` (fn th => once_rewrite_tac[th]) >> simp[])) >>
  simp[]
QED

Resume dload_joint_tracked_scalar_next[semantic]:
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `s.vs_labels = t0.vs_labels` by
    (drule dload_boundary_environment >> metis_tac[dload_equal_environment_code]) >>
  `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `~MEM i.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by
    (qpat_x_assum `_ \/ _` mp_tac >> rpt (pop_assum kall_tac) >>
     rpt strip_tac >> gvs[MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (drule_at (Pat `MEM i (fn_insts f)`) dload_original_nonopaque_operands >>
     simp[]) >>
  `!v. MEM (Var v) i.inst_operands ==> MEM v (fn_ir_vars f)` by
    metis_tac[fn_ir_vars_operand] >>
  Cases_on `i.inst_opcode = BUMP`
  >- (drule_at (Pat `dload_boundary_core`) dload_boundary_core_bump_index >>
      disch_then (drule_at (Pat `step_inst`)) >>
      disch_then (drule_at (Pat `fn_ptr_ok`)) >>
      disch_then (qspecl_then [`set (fn_ir_vars f)`,`C`] mp_tac) >>
      simp[]) >>
  Cases_on `MEM i.inst_opcode [LT; GT; EQ]`
  >- (drule_at (Pat `dload_boundary_core`) dload_boundary_core_compare_index >>
      disch_then (drule_at (Pat `step_inst`)) >>
      disch_then (drule_at (Pat `fn_ptr_ok`)) >>
      disch_then (qspecl_then [`set (fn_ir_vars f)`,`C`] mp_tac) >>
      simp[] >> (impl_tac >- gvs[MEM]) >> simp[]) >>
  drule_at (Pat `dload_boundary_core`) dload_boundary_core_scalar_index >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
      disch_then (qspecl_then [`set (fn_ir_vars f)`,`C`] mp_tac) >>
  simp[] >> (impl_tac >-
    (qpat_x_assum `_ \/ _` mp_tac >>
     qpat_x_assum `~MEM i.inst_opcode [LT; GT; EQ]` mp_tac >>
     qpat_x_assum `i.inst_opcode <> BUMP` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[MEM] >> metis_tac[])) >> simp[]
QED

Finalise dload_joint_tracked_scalar_next
