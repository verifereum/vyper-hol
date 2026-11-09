Theory lowerDloadPtrJointReturn
Ancestors lowerDloadPtrJointCall lowerDloadPtrNormalReturn
  lowerDloadPtrTerminalClosure lowerDloadPtrPhase o1ContractSimplifyCfg
  o1ContractSimplifyCfgSrcFrame o1PassContract o1ContractLowerDload lowerDloadPtrRawReachable unitShapeDefs ptrDiscipline venomWf
  lowerDloadPtrStatic lowerDloadPtrRel lowerDloadDefs venomInst contextCodegenRel
  venomExecSemantics venomState list rich_list pred_set finite_map option

Theorem dload_return_phase_zero[local]:
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  step_inst fuel Ct j t = IntRet rt tend ==>
  n = 0 /\ emitted = [i] /\ j = i
Proof
  strip_tac >> drule step_inst_intret_opcodes >> strip_tac >>
  drule dload_control_match_expansion >> strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >> gvs[]
QED

Theorem dload_joint_return_closed:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  ((?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs (d::ds) /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ ri = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs = LENGTH (d::ds) /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state) (d::ds))).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (g,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs; d = EL k (d::ds) in
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
          c.cf_inst [c.cf_inst] 0))) \/
    dload_terminal_mode lo P vs C (d::ds) H un g ri t) /\
  active_inst g ri t /\ step_inst fuel C' ri t = IntRet rt tend /\
  bind_outputs d.cf_inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state d.cf_state tend)) = SOME t' /\
  active_inst d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) ==>
  (?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG d.cf_params G H0 tn un0 s t0 cs ds /\
    dload_control_match q f d.cf_fn s t0 i emitted 0 /\
    dload_prefix_match pfuel C' d.cf_params emitted n t0 H0 un0
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx)
      (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
      (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs))) /\
    dload_control_match q f d.cf_fn s
      (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx) i emitted n /\ j = EL n emitted /\
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
    (?q'. lower_dload_function_supply q f = (d.cf_fn,q')) /\
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
          c.cf_inst [c.cf_inst] 0))) \/
    dload_terminal_mode lo P vs C ds
      (DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs)))
      (un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs)))
      d.cf_fn j (t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx)
Proof
  strip_tac >- suspend "normal" >>
  metis_tac[dload_terminal_mode_no_return]
QED

Resume dload_joint_return_closed[normal]:
  drule_all dload_return_phase_zero >> strip_tac >> gvs[dload_prefix_zero] >>
  rename1 `step_inst fuel C' ri t = IntRet rt tend` >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `active_inst f ri s` by metis_tac[dload_control_match_boundary] >>
  `MEM ri (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `ri.inst_opcode = RET` by
    (drule step_inst_intret_opcodes >> gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  `tend = t` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  gnvs[] >> suspend "origins"
QED

Resume dload_joint_return_closed[origins]:
  `ptr_use_ok P (fn_pv P f) ri` by gvs[fn_ptr_ok_def] >>
  `taint_ok f tn ri s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ri.inst_operands <> []` by
    (strip_tac >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def]) >>
  `!a. MEM (Var a) (FRONT ri.inst_operands) ==>
    a IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (rpt strip_tac >>
     `MEM (Var a) ri.inst_operands` by metis_tac[MEM_FRONT_NOT_NIL] >>
     simp[] >> conj_tac >- metis_tac[fn_ir_vars_operand] >>
     strip_tac >>
     `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     drule_all opaque_use_ok_retpc_use >>
     strip_tac >> gvs[retpc_use_ok_def, FRONT_APPEND]) >>
  `!a. MEM (Var a) ri.inst_operands ==>
    (lookup_var a s = NONE <=> lookup_var a t = NONE)` by
    metis_tac[fn_ir_vars_operand] >>
  Cases_on `cs` >- gvs[] >>
  rename1 `frame_reachable vs C (c::cs0) PG G tn f ri s` >>
  Cases_on `fs` >- gvs[] >>
  rename1 `dload_boundary_core lo (e::fs0) _ _ _ _ _ _ _ _ _ _ _ _` >>
  Cases_on `fs0` >- gvs[] >>
  rename1 `dload_boundary_core lo (e::ef::fs1) _ _ _ _ _ _ _ _ _ _ _ _` >>
  qpat_assum `!k. k < SUC (LENGTH ds) ==> _`
    (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [LET_THM])) >>
  `MEM c.cf_fn C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >>
     gvs[frame_stack_prefix_def]) >>
  `o1_fn_shape C c.cf_fn` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) d.cf_fn.fn_blocks)` by
    (qpat_assum `lower_dload_function_supply _ c.cf_fn = _`
       (mp_then Any mp_tac lower_dload_function_supply_labels) >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  `!h. MEM h C.ctx_functions ==> fn_ptr_ok P h` by metis_tac[EVERY_MEM] >>
  suspend "pop"
QED

Resume dload_joint_return_closed[pop]:
  drule_at (Pat `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    dload_normal_return >>
  disch_then (drule_at (Pat `frame_reachable _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_use_ok _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `bind_outputs _ _ _ = _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ _`)) >>
  simp[] >>
  strip_tac >>
  disj1_tac >>
  qexistsl_tac [`cs0`, `c.cf_params`,
    `DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs))`,
    `tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs))`,
    `c.cf_fn`, `i`, `s' with vs_inst_idx := SUC c.cf_state.vs_inst_idx`,
    `qc''`, `emitted`, `0`, `0`,
    `t' with vs_inst_idx := SUC d.cf_state.vs_inst_idx`,
    `DRESTRICT d.cf_prov (COMPL (set d.cf_inst.inst_outputs))`,
    `un with t_var := DRESTRICT d.cf_tvar (COMPL (set d.cf_inst.inst_outputs))`,
    `ef::fs1`] >>
  simp[dload_prefix_zero] >> gnvs[]
QED

Finalise dload_joint_return_closed

val _ = if null (hyp dload_joint_return_closed) then ()
  else raise Fail "joint return: nonempty hypotheses";
