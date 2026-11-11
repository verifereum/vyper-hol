Theory lowerDloadPtrJointBytesClosure
Ancestors lowerDloadPtrBackwardNext lowerDloadPtrNormalNext lowerDloadPtrReplay
  lowerDloadPtrSourceInv lowerDloadPtrJointAllocClosure lowerDloadPtrStatic
  lowerDloadPtrBytesTransport lowerDloadPtrPhase lowerDloadPtrRel
  lowerDloadDefs o1PassContract ptrDiscipline venomExecSemantics venomState
  lowerDloadPtrJointNext o1ContractLowerDload
  unitShapeDefs lowerDloadPtrRawReachable memSafeRun unitTransformDefs
  codegenRel contextCodegenRel venomInst venomWf venomExecProps
  irSupply venomFnScheduleRunner o1PassLift unitMemInv contextRawReachable
  list rich_list pred_set finite_map

Theorem dloadbytes_step_fields:
  i.inst_opcode = DLOADBYTES /\ step_inst fuel C i s = OK s1 ==>
  s1.vs_allocas = s.vs_allocas /\ s1.vs_call_ctx = s.vs_call_ctx /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
    write_memory_with_expansion_def]
QED

Theorem dloadbytes_supply_allocas:
  lower_dload_inst_supply supply i = (xs,next) /\
  i.inst_opcode = DLOADBYTES /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\
  dload_prefix_match fuel C PH xs 2 t H un t2 H2 un2 ==>
  t2.vs_allocas = t.vs_allocas
Proof
  strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `dload_prefix_match _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  `2 = SUC (SUC 0)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  simp[dload_prefix_match_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >> gvs[write_memory_with_expansion_def] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
  strip_tac >> gvs[update_var_def]
QED

Theorem dload_joint_tracked_dloadbytes_complete_next:
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
    i.inst_opcode = DLOADBYTES /\ SUC n = LENGTH emitted /\
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
  `?dst off sz. i.inst_operands = [dst;off;sz] /\ i.inst_outputs = []` by
    suspend "shape" >>
  `n = 1` by
    (drule dload_control_match_expansion >> strip_tac >>
     qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
     simp[lower_dload_inst_supply_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[]) >>
  `LENGTH emitted = 2` by decide_tac >>
  `dload_prefix_match pfuel C' PH emitted 2 t0 H0 un0
     (t1 with vs_inst_idx := SUC t.vs_inst_idx)
     (step_prov PH H j t1) (step_taint j t t1 un)` by
    (qpat_x_assum `j = EL n emitted` SUBST_ALL_TAC >>
     drule_at (Pat `dload_prefix_match`) dload_prefix_extend_mixed >>
     disch_then (qspecl_then [`t1`,`fuel`,`C'`] mp_tac) >> simp[]) >>
  `?supply after cv supply1.
    lower_dload_inst_supply supply i = (emitted,after) /\
    fresh_ir_var supply = (cv,supply1) /\ cv NOTIN set (fn_ir_vars f)` by
    suspend "supply" >>
  `fn_ptr_ok P f` by fs[EVERY_MEM] >>
  `access_ok lo G f i s /\ taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    suspend "operands" >>
  `dst <> Var cv /\ sz <> Var cv` by
    (strip_tac >> gvs[] >> metis_tac[fn_ir_vars_operand]) >>
  `~in_revert_forward f s` by suspend "forward" >>
  `code_layout_valid s` by suspend "layout" >>
  `dload_offset_ok C f i s` by
    (qpat_assum `frame_reachable vs C cs PG G tn f i s`
       (mp_then Any mp_tac o1_src_frame_dload_offset_ok) >>
     disch_then (qspec_then `D` mp_tac) >> simp[]) >>
  qpat_assum `dload_prefix_match _ _ _ _ 2 _ _ _ _ _ _`
    (mp_then Any mp_tac dloadbytes_supply_boundary) >>
  disch_then (drule_at (Pat `dload_boundary_core`)) >>
  disch_then (drule_at (Pat `lower_dload_inst_supply`)) >>
  disch_then (drule_at (Pat `fresh_ir_var`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok`)) >>
  disch_then (drule_at (Pat `dload_offset_ok`)) >>
  simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  drule_at (Pat `lower_dload_inst_supply`) dloadbytes_supply_definedness_control >>
  disch_then (drule_at (Pat `fresh_ir_var`)) >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `dload_prefix_match _ _ _ _ 2 _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`sz`,`off`,`dst`,`set (fn_ir_vars f)`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `dload_control_match q f g s t0 i emitted 0`
    (mp_then Any mp_tac dload_control_emission_next_fields) >>
  disch_then (drule_at (Pat `active_inst`)) >>
  disch_then (qspec_then `s1` mp_tac) >> simp[] >> strip_tac >>
  `frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
    f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by suspend "reachable" >>
  `s1.vs_call_ctx = s.vs_call_ctx` by (drule_all dloadbytes_step_fields >> simp[]) >>
  `(t1 with vs_inst_idx := SUC t.vs_inst_idx).vs_allocas = t0.vs_allocas` by
    (qpat_assum `dload_prefix_match _ _ _ _ 2 _ _ _ _ _ _`
       (mp_then Any mp_tac dloadbytes_supply_allocas) >>
     disch_then (drule_at (Pat `lower_dload_inst_supply`)) >> simp[]) >>
  qpat_x_assum `dload_boundary_core _ _ _ _ _ _ G _ _ _ _ _ _ _` kall_tac >>
  gnvs[] >>
  drule_at (Pat `dload_boundary_core`) dload_normal_unchanged_successor >>
  disch_then (drule_at (Pat `frame_reachable`)) >>
  disch_then (drule_at (Pat `dload_control_match`)) >>
  disch_then (qspecl_then [`t0`,`s`,`HD emitted'`,`P`,`C'`] mp_tac) >>
  simp[EVERY_MEM] >> disch_then irule >> fs[EVERY_MEM]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[shape]:
  rpt strip_tac >>
  `fn_inst_wf f` by fs[o1_fn_shape_def] >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  Cases_on `i.inst_operands` >> gvs[] >> rename1 `SUC (LENGTH rest) = 3` >>
  Cases_on `rest` >> gvs[] >> rename1 `SUC (SUC (LENGTH tail)) = 3` >>
  Cases_on `tail` >> gvs[] >>
  rename1 `SUC (SUC (SUC (LENGTH last))) = 3` >>
  Cases_on `last` >> gvs[]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[operands]:
  rpt strip_tac >> simp[] >> conj_tac
  >- (irule fn_ir_vars_operand >> qexists `i` >> simp[]) >>
  `opaque_use_ok f` by fs[o1_fn_shape_def, fn_shape_ok_def] >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  gvs[retpc_use_ok_def, MEM]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[forward]:
  rpt strip_tac >>
  `active_inst f i s` by fs[dload_control_match_def] >>
  `ALL_DISTINCT (fn_labels f)` by
    fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def] >>
  qpat_x_assum `active_inst f i s` mp_tac >>
  pure_rewrite_tac[active_inst_def] >> strip_tac >>
  `lookup_block s.vs_current_bb f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb s.vs_inst_idx = SOME i` by simp[get_instruction_def] >>
  gvs[in_revert_forward_def] >>
  drule_all revert_forward_at_opcode >> simp[]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[reachable]:
  rpt strip_tac >> irule frame_reachable_next >>
  fs[dload_control_match_def, is_terminator_def] >> metis_tac[]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[supply]:
  rpt strip_tac >>
  qpat_x_assum `dload_control_match q f g s t0 i emitted 0` mp_tac >>
  pure_rewrite_tac[dload_control_match_def] >> strip_tac >>
  Cases_on `fresh_ir_var is` >> rename1 `fresh_ir_var is = (cv1,supply2)` >>
  qexistsl [`is`,`after`,`cv1`,`supply2`] >> simp[] >>
  Cases_on `lower_dload_blocks_supply q (TAKE bi f.fn_blocks)` >>
  drule lower_dload_blocks_supply_reserved_operand >> strip_tac >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Resume dload_joint_tracked_dloadbytes_complete_next[layout]:
  rpt strip_tac >> drule_all o1_src_frame_code_layout_valid >> simp[]
QED

Finalise dload_joint_tracked_dloadbytes_complete_next
