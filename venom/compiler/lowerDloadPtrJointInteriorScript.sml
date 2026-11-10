Theory lowerDloadPtrJointInterior
Ancestors lowerDloadPtrJointCall lowerDloadPtrPhaseNext lowerDloadPtrReplay
  lowerDloadPtrAggregate lowerDloadPtrPhase lowerDloadPtrRel
  lowerDloadPtrRawReachable o1PassContract lowerDloadDefs lowerDloadPtrStatic o1ContractLowerDload
  ptrDiscipline venomExecSemantics venomState venomInst venomWf
  unitShapeDefs codegenRel contextCodegenRel list pred_set finite_map

Theorem dload_joint_interior_next_closed:
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
    SUC n < LENGTH emitted /\
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
  step_inst fuel C' j t = OK v /\
  active_inst g next (v with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0
      (v with vs_inst_idx := SUC t.vs_inst_idx)
      (step_prov PH H j v) (step_taint j t v un) /\
    dload_control_match q f g s (v with vs_inst_idx := SUC t.vs_inst_idx)
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
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  `dload_phase_core pfuel C' q f g i emitted n lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
    PG PH G tn s t H un cs ds` by
    (simp[dload_phase_core_def] >> metis_tac[]) >>
  `step_inst pfuel C' (EL n emitted) t = OK v` by
    gvs[step_inst_non_invoke] >>
  drule_all dload_actual_phase_next >> strip_tac >>
  drule dload_phase_anchor >> strip_tac >>
  qexistsl [`cs`,`PG`,`G`,`tn`,`f`,`i`,`s`,`q`,`emitted`,`SUC n`,
    `pfuel`,`t0`,`H0`,`un0`,`fs`] >> simp[] >>
  irule dload_prefix_extend >> simp[] >> metis_tac[]
QED
