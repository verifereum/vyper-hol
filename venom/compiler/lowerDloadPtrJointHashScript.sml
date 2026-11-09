Theory lowerDloadPtrJointHash
Ancestors lowerDloadPtrHash lowerDloadPtrBlockEntry lowerDloadPtrCall lowerDloadPtrNormalNext
  lowerDloadPtrJointInterior lowerDloadPtrOrdinary lowerDloadPtrJointNext
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrRel lowerDloadPtrStatic
  lowerDloadDefs o1ContractLowerDload o1PassContract lowerDloadPtrRawReachable memSafeRun
  ptrDiscipline unitShapeDefs codegenRel venomExecSemantics venomState
  venomInst venomWf venomExecProps contextCodegenRel list rich_list pred_set finite_map

Theorem dload_joint_tracked_sha3_next:
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
    i.inst_opcode = SHA3 /\
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
     simp[lower_dload_inst_supply_def] >> rpt strip_tac >> gnvs[] >>
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
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by simp[] >>
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

Resume dload_joint_tracked_sha3_next[semantic]:
  rpt strip_tac >>
  `fn_ptr_ok P f` by
    (qpat_x_assum `EVERY (fn_ptr_ok P) _` mp_tac >> simp[EVERY_MEM]) >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `s.vs_labels = t0.vs_labels` by
    (drule dload_boundary_environment >> metis_tac[dload_equal_environment_code]) >>
  `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (rpt strip_tac >> simp[] >> conj_tac
     >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
     strip_tac >> drule_all opaque_use_ok_retpc_use >>
     gvs[retpc_use_ok_def]) >>
  `!v. MEM (Var v) i.inst_operands ==> MEM v (fn_ir_vars f)` by
    metis_tac[fn_ir_vars_operand] >>
  `~in_revert_forward f s` by
    (`active_inst f i s` by fs[dload_control_match_def] >>
     qpat_x_assum `active_inst f i s` mp_tac >>
     simp[active_inst_def, in_revert_forward_def] >>
     rpt strip_tac >> gvs[] >>
     `ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)` by
       fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def] >>
     `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[] >>
     `get_instruction bb s.vs_inst_idx = SOME (EL s.vs_inst_idx bb.bb_instructions)` by
       simp[get_instruction_def] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  `~about_to_revert f i s` by simp[about_to_revert_def] >>
  drule_at (Pat `dload_boundary_core`) dload_boundary_core_sha3 >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (qspecl_then [`set (fn_ir_vars f)`,`C`] mp_tac) >>
  simp[] >> strip_tac >> qexists `s'` >> simp[lookup_var_def] >>
  (conj_tac >- gvs[lookup_var_def] >>
   qpat_assum `dload_boundary_core _ _ _ _ _ _ _ _ _ _ s' t1 _ _`
     (mp_then Any mp_tac dload_boundary_core_index_update) >> simp[])
QED

Finalise dload_joint_tracked_sha3_next
