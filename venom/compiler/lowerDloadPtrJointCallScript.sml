Theory lowerDloadPtrJointCall
Ancestors lowerDloadPtrJointBlock lowerDloadPtrInvoke lowerDloadPtrJointEntry
  lowerDloadPtrNormalPush lowerDloadPtrPhase lowerDloadPtrTerminalClosure
  o1PassContract o1ContractLowerDload lowerDloadPtrRawReachable unitShapeDefs
  ptrDiscipline lowerDloadPtrStatic contextCodegenRel venomWf
  lowerDloadPtrRel lowerDloadDefs venomInst
  venomExecSemantics venomState list rich_list pred_set finite_map option

Theorem dload_call_phase_zero[local]:
  dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
  j.inst_opcode = INVOKE ==>
  n = 0 /\ emitted = [i] /\ j = i
Proof
  strip_tac >> drule dload_control_match_expansion >> strip_tac >>
  qpat_x_assum `lower_dload_inst_supply _ _ = _` mp_tac >>
  simp[lower_dload_inst_supply_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[AllCaseEqs()] >>
  `n = 0 \/ n = 1 \/ n = 2 \/ n = 3` by decide_tac >> gvs[]
QED

Theorem dload_joint_call_closed:
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
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t H un /\
    dload_control_match q f g s t i emitted n /\ callinst = EL n emitted /\
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
          c.cf_inst [c.cf_inst] 0))) \/
    dload_terminal_mode lo P vs C ds H un g callinst t) /\
  active_inst g callinst t /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C'.ctx_functions = SOME gc /\
  eval_operands ops t = SOME args /\ setup_callee gc args t = SOME u /\
  enters_block gc u t1 /\ active_inst gc j t1 ==>
  (?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG (MAP (op_prov H) ops) G H0 tn un0 s t0 cs
      (<|cf_fn:=g; cf_inst:=callinst; cf_state:=t; cf_params:=PH;
         cf_prov:=H; cf_tvar:=un.t_var|> :: ds) /\
    dload_control_match q f gc s t0 i emitted 0 /\
    dload_prefix_match pfuel C' (MAP (op_prov H) ops) emitted n t0 H0 un0 t1
      FEMPTY (un with t_var:=FEMPTY) /\
    dload_control_match q f gc s t1 i emitted n /\ j = EL n emitted /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s = NONE <=> lookup_var v t0 = NONE)) /\
    FDOM G SUBSET fn_pv P f /\
    (!k b sz. k < LENGTH PG /\ EL k PG = SOME (b,sz) ==> k IN P f.fn_name) /\
    (!c. MEM c cs ==> FDOM c.cf_prov SUBSET fn_pv P c.cf_fn) /\
    (!c k b sz. MEM c cs /\ k < LENGTH c.cf_params /\
      EL k c.cf_params = SOME (b,sz) ==> k IN P c.cf_fn.fn_name) /\
    LENGTH fs = SUC (LENGTH cs) /\ LENGTH cs =
      LENGTH (<|cf_fn:=g; cf_inst:=callinst; cf_state:=t; cf_params:=PH;
                cf_prov:=H; cf_tvar:=un.t_var|> :: ds) /\
    (!k. k < LENGTH fs ==>
      (EL k fs).dr_scratch =
        FDOM (EL k (t0::MAP (\d. d.cf_state)
          (<|cf_fn:=g; cf_inst:=callinst; cf_state:=t; cf_params:=PH;
             cf_prov:=H; cf_tvar:=un.t_var|> :: ds))).vs_allocas DIFF
        {id | ?ci. MEM ci (fn_insts (EL k (f::MAP (\c. c.cf_fn) cs))) /\
                   ci.inst_id = id}) /\
    ir_supply_covers_fn q f /\
    (?q'. lower_dload_function_supply q f = (gc,q')) /\
    (!k. k < LENGTH cs ==>
      let c = EL k cs;
          d = EL k (<|cf_fn:=g; cf_inst:=callinst; cf_state:=t; cf_params:=PH;
                      cf_prov:=H; cf_tvar:=un.t_var|> :: ds) in
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
    dload_terminal_mode lo P vs C
      (<|cf_fn:=g; cf_inst:=callinst; cf_state:=t; cf_params:=PH;
         cf_prov:=H; cf_tvar:=un.t_var|> :: ds)
      FEMPTY (un with t_var:=FEMPTY) gc j t1
Proof
  strip_tac >- suspend "normal" >>
  metis_tac[dload_terminal_mode_no_call]
QED

Resume dload_joint_call_closed[normal]:
  drule_all dload_call_phase_zero >> strip_tac >> gnvs[dload_prefix_zero] >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `taint_ok f tn callinst s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `active_inst f callinst s` by metis_tac[dload_control_match_boundary] >>
  `MEM callinst (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) ops ==>
    v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (rpt strip_tac >>
     `MEM (Var v) callinst.inst_operands` by
       (qpat_x_assum `decode_invoke _ = _` mp_tac >>
        simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
     simp[] >> conj_tac >- metis_tac[fn_ir_vars_operand] >>
     strip_tac >>
     `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     drule_all opaque_use_ok_retpc_use >> gvs[retpc_use_ok_def, MEM]) >>
  drule_all dload_stage_lookup_back >> strip_tac >>
  rename1 `lookup_function nm C.ctx_functions = SOME callee` >>
  `MEM callee C.ctx_functions` by
    metis_tac[lookup_function_MEM] >>
  `o1_fn_shape C callee` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `first_block_no_phi callee /\ ~NULL callee.fn_blocks` by
    (fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def] >>
     Cases_on `callee.fn_blocks` >> gvs[fn_has_entry_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) gc.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  `!h. MEM h C.ctx_functions ==> fn_ptr_ok P h` by metis_tac[EVERY_MEM] >>
  suspend "push"
QED

Resume dload_joint_call_closed[push]:
  drule_at (Pat `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    dload_normal_invoke_call >> disch_then drule >>
  disch_then (drule_at (Pat `dload_control_match _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `lookup_function _ _ = _`)) >>
  disch_then (drule_at (Pat `lower_dload_function_supply _ _ = _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operands _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `enters_block _ _ _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ _`)) >>
  disch_then (drule_at (Pat `lower_dload_function_supply _ _ = _`)) >>
  disch_then (qspec_then `P` mp_tac) >> simp[] >>
  strip_tac >>
  disj1_tac >>
  qexistsl_tac [`<|cf_fn := f; cf_inst := callinst; cf_state := s;
      cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: cs`,
    `MAP (op_prov G) ops`, `FEMPTY`, `tn with t_var := FEMPTY`,
    `callee`, `i`, `u'`, `q''`, `emitted`, `0`, `0`, `t1`, `FEMPTY`,
    `un0 with t_var := FEMPTY`,
    `<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs`] >>
  simp[dload_prefix_zero] >> gnvs[] >> metis_tac[]
QED

Finalise dload_joint_call_closed

val _ = if null (hyp dload_joint_call_closed) then ()
  else raise Fail "joint call: nonempty hypotheses";
