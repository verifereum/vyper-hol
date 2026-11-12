(* Whole-boundary normal ASSIGN preservation. *)
Theory o1LowerDloadJointAssign
Ancestors
  o1LowerDloadJointRelation o1LowerDloadJointEntry o1ContractLowerDload
  lowerDloadDefs contextCodegenRel venomExecSemantics venomExecProps
  venomInst irSupply list finite_map venomState ptrDiscipline
  o1LowerDloadEnvironment o1LowerDloadOpaque o1LowerDloadOccurrence
  o1PassContract venomWf o1LowerDloadShared

Theorem ld_supply_insts_append:
  !u as u1 bs u2.
    lower_dload_insts_supply u xs = (as,u1) /\
    lower_dload_insts_supply u1 ys = (bs,u2) ==>
    lower_dload_insts_supply u (xs ++ ys) = (as ++ bs,u2)
Proof
  Induct_on `xs`
  >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def] >> gvs[]
QED

Theorem ld_supply_insts_index:
  !u outs w j pre v inst.
    lower_dload_insts_supply u ins = (outs,w) /\ j < LENGTH ins /\
    lower_dload_insts_supply u (TAKE j ins) = (pre,v) /\
    EL j ins = inst /\ lower_dload_inst_supply v inst = ([inst],v) ==>
    LENGTH pre < LENGTH outs /\ EL (LENGTH pre) outs = inst /\
    lower_dload_insts_supply u (TAKE (SUC j) ins) = (pre ++ [inst],v)
Proof
  Induct_on `ins`
  >- simp[] >>
  rpt gen_tac >> Cases_on `j`
  >- (simp[lower_dload_insts_supply_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[]) >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `lower_dload_insts_supply u (_::TAKE _ _) = _`
    (mp_tac o REWRITE_RULE [Once lower_dload_insts_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  simp[Once lower_dload_insts_supply_def, EL_APPEND_EQN, APPEND_ASSOC]
QED

Theorem ld_joint_control_unchanged_next:
  ld_joint_control u fn fn' s t /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\
  ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  active_inst fn next (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
  active_inst fn' inst t /\
  ld_joint_control u fn fn'
    (s with vs_inst_idx := SUC s.vs_inst_idx)
    (t with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[ld_joint_control_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply u1 bb` >>
  `MEM bb fn.fn_blocks` by (simp[MEM_EL] >> qexists_tac `k` >> simp[Abbr `bb`]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst /\
   SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `active_inst fn inst s` mp_tac >>
     qpat_x_assum `active_inst fn next _` mp_tac >>
     simp[active_inst_def] >> rpt strip_tac >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb''` by
       (irule MEM_lookup_block >> simp[]) >>
     `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  qpat_assum `lower_dload_block_supply _ _ = _`
    (mp_tac o REWRITE_RULE [lower_dload_block_supply_def]) >>
  simp[NoAsms, AllCaseEqs()] >> strip_tac >>
  `lower_dload_inst_supply u3 inst = ([inst],u3)` by
    (irule lower_dload_inst_supply_special >> simp[]) >>
  drule_all ld_supply_insts_index >> strip_tac >>
  conj_tac
  >- (simp[active_inst_def] >> qexists_tac `EL k fn'.fn_blocks` >>
      conj_tac >- (simp[MEM_EL] >> qexists_tac `k` >> simp[]) >>
      qpat_assum `_ with bb_instructions := _ = _` (SUBST1_TAC o SYM) >>
      simp[]) >>
  qexistsl [`k`,`pre`,`u1`,`u2`,`expanded ++ [inst]`,`u3`] >>
  gvs[Abbr `bb`]
QED

Theorem ld_assign_success_iff:
  inst.inst_opcode = ASSIGN ==>
  (step_inst fuel C inst s = OK s1 <=>
   ?op out x. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
     eval_operand op s = SOME x /\ s1 = update_var out x s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_env_assign_update:
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y ==>
  ld_env_agree sites fn (occurrence_step a HP H inst (update_var out x s))
    (step_taint inst s (update_var out x s) tn)
    (update_var out x s) (update_var out y t)
Proof
  strip_tac >>
  `~retpc_var fn out ==> ld_value_agree sites (op_prov H op) (op_taint tn op) x y` by
    (strip_tac >>
     `!v. op = Var v ==> ~retpc_var fn v` by
       (rpt strip_tac >> metis_tac[non_retpc_assign_input, MEM]) >>
     drule_all ld_env_operand_value >> simp[]) >>
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       occurrence_step_def, occurrence_out_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `out = v` >> gvs[ld_env_agree_def]) >>
  rpt gen_tac >> Cases_on `out = v`
  >- (gvs[] >> Cases_on `op_prov H op` >>
      gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> gvs[]) >>
  Cases_on `op_prov H op` >>
  gvs[set_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, ld_env_agree_def, op_taint_def]
QED

Theorem ld_joint_assign_step:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ active_inst fn inst s /\
  inst.inst_opcode = ASSIGN /\ step_inst fuel C inst s = OK s1 ==>
  ?op out x y. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
    s1 = update_var out x s /\
    step_inst fuel C' inst t = OK (update_var out y t) /\
    ld_env_agree sites fn (occurrence_step a HP H inst s1)
      (step_taint inst s s1 tn) s1 (update_var out y t)
Proof
  strip_tac >>
  `?op out x. inst.inst_operands = [op] /\ inst.inst_outputs = [out] /\
     eval_operand op s = SOME x /\ s1 = update_var out x s` by
    metis_tac[ld_assign_success_iff] >>
  rename1 `inst.inst_operands = [op]` >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `!v. op = Var v ==> MEM v (fn_ir_vars fn)` by
    (rpt strip_tac >>
     fs[fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
        inst_uses_def, MEM_FLAT, MEM_MAP, fn_insts_def,
        o1PassContractTheory.fn_insts_blocks_MEM] >>
     qexists_tac `FLAT (MAP inst_ir_vars bb.bb_instructions)` >>
     conj_tac >- (qexists_tac `bb` >> simp[]) >>
     simp[MEM_FLAT, MEM_MAP] >> qexists_tac `inst_ir_vars inst` >>
     conj_tac >- (qexists_tac `inst` >> simp[]) >>
     simp[inst_ir_vars_def, inst_uses_def, operand_vars_def, operand_var_def]) >>
  drule_all ld_joint_operand_defined >>
  Cases_on `eval_operand op t` >> simp[] >>
  conj_tac >- (simp[ld_assign_success_iff] >> metis_tac[]) >>
  irule ld_env_assign_update >> simp[] >>
  metis_tac[ld_joint_environment, ld_joint_labels]
QED

Theorem ld_joint_var_update_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ ~MEM inst.inst_opcode [DLOAD; DLOADBYTES] /\
  s1 = update_var out x (s with vs_gas_readings := rs) /\
  t1 = update_var out y (t with vs_gas_readings := rs) /\
  G1 = step_prov PG G inst s1 /\ H1 = occurrence_step a HP H inst s1 /\
  tn1 = step_taint inst s s1 tn /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  occ_frame_reachable vs C stk PG G1 tn1 fn inst2
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) n a U B HP H1 /\
  occurrence_annotation_ok (dyn_floor C vs) n a U B HP H1 stk PG G1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
  ld_env_agree sites fn H1 tn1 s1 t1 /\
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
  tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm ==>
  ?u fn'. lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG G1 tn1 fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP H1 sites X ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_joint_assign_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\
  active_inst fn inst s /\ inst.inst_opcode = ASSIGN /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?t1 u fn'. step_inst fuel C' inst t = OK t1 /\
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    ld_joint_control u fn fn' s t /\ active_inst fn' inst t /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED
