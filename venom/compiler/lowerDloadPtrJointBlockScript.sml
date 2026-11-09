Theory lowerDloadPtrJointBlock
Ancestors lowerDloadPtrNormalBlock lowerDloadPtrControlInversion
  lowerDloadPtrTerminalClosure lowerDloadPtrPhase lowerDloadPtrBlockEntry
  o1PassContract o1ContractLowerDload lowerDloadPtrRawReachable unitShapeDefs
  ptrDiscipline lowerDloadPtrRel lowerDloadPtrStatic lowerDloadDefs
  contextCodegenRel venomInst venomState venomWf list rich_list pred_set finite_map

Theorem dload_joint_block_closed:
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
    dload_control_match q f g s t i emitted n /\ j = EL n emitted /\
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
    dload_terminal_mode lo P vs C ds H un g j t) /\
  active_inst g j t /\ is_terminator j.inst_opcode /\
  step_inst fuel C' j t = OK t1 /\ ~t1.vs_halted /\
  enters_block g t1 t2 /\ active_inst g j' t2 ==>
  (?cs PG G tn f i s q emitted n pfuel t0 H0 un0 fs.
    frame_reachable vs C cs PG G tn f i s /\
    dload_boundary_core lo fs
      (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (MAP (\c. set (fn_ir_vars c.cf_fn) DIFF {v | retpc_var c.cf_fn v}) cs)
      PG PH G H0 tn un0 s t0 cs ds /\
    dload_control_match q f g s t0 i emitted 0 /\
    dload_prefix_match pfuel C' PH emitted n t0 H0 un0 t2
      (entry_prov g t1 H) (entry_taint_vars g t1 un) /\
    dload_control_match q f g s t2 i emitted n /\ j' = EL n emitted /\
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
    dload_terminal_mode lo P vs C ds (entry_prov g t1 H)
      (entry_taint_vars g t1 un) g j' t2
Proof
  strip_tac
  >- suspend "normal"
  >> metis_tac[dload_terminal_mode_no_block]
QED

Resume dload_joint_block_closed[normal]:
  drule_all dload_control_block_inversion >> strip_tac >>
  gnvs[dload_prefix_zero] >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >> first_x_assum drule >> simp[]) >>
  `o1_fn_shape C f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks)` by
    (drule lower_dload_function_supply_labels >>
     fs[o1_fn_shape_def, fn_shape_ok_def, wf_function_def, fn_labels_def]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) i.inst_operands ==>
    v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (rpt strip_tac >> simp[] >> conj_tac >- metis_tac[fn_ir_vars_operand] >>
     strip_tac >>
     `opaque_use_ok f` by gvs[o1_fn_shape_def, fn_shape_ok_def] >>
     drule_all opaque_use_ok_retpc_use >>
     gvs[retpc_use_ok_def, MEM]) >>
  `!h. MEM h C.ctx_functions ==> fn_ptr_ok P h` by metis_tac[EVERY_MEM] >>
  `!a v lbl op w. MEM a (fn_insts f) /\ a.inst_opcode = PHI /\
    a.inst_outputs = [v] /\ v IN (set (fn_ir_vars f) DIFF {v | retpc_var f v}) /\
    resolve_phi lbl a.inst_operands = SOME op /\ op = Var w ==>
    w IN (set (fn_ir_vars f) DIFF {v | retpc_var f v})` by
    (rpt strip_tac >> metis_tac[dload_original_phi_input_tracked]) >>
  drule_at (Pat `dload_boundary_core _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    dload_normal_branch_block >> disch_then drule >>
  disch_then (drule_at (Pat `dload_control_match _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `active_inst _ _ _`)) >>
  disch_then (drule_at (Pat `fn_ptr_ok _ _`)) >> simp[MEM] >>
  impl_tac >- (gnvs[] >> metis_tac[]) >> strip_tac >>
  disj1_tac >>
  qexistsl_tac [`cs`, `PG`, `entry_prov f s1 G`, `entry_taint_vars f s1 tn`,
    `f`, `i'`, `s2`, `q`, `emitted'`, `0`, `0`, `t2`,
    `entry_prov g t1 H0`, `entry_taint_vars g t1 un0`, `fs`] >>
  simp[dload_prefix_zero] >> gnvs[]
QED

Finalise dload_joint_block_closed

(* Constructor interface audited against JointDispatch's normal quotation:
   the true guard is erased; scratch identities remain anchored at t0. *)
val _ = if null (hyp dload_joint_block_closed) then ()
  else raise Fail "joint block: nonempty hypotheses";
