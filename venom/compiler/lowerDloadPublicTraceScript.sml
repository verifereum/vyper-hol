(* Evaluations recovered from the actual public-copy expansion trace. *)
Theory lowerDloadPublicTrace
Ancestors
  lowerDloadExpansionExit lowerDloadSafetyAllocation lowerDloadSafetyKernel lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyUpdates
  lowerDloadSafetyWriteAssembly lowerDloadConfiguredOrigins lowerDloadOracleCallAssembly lowerDloadSafetyAssemblyPremises lowerDloadSafetyAllocBounds o1PassLift memSafeRun venomExecProps venomExecProofs contextRawReachable o1PassContract
  lowerDloadSafetyLocations venomFnScheduleRunner contextCodegenRel passSharedDefs lowerDloadSafetyRelation codegenRel lowerDloadDefs irSupply ptrDiscipline pointerConfinedDefs memLocDefs pred_set unitShapeDefs
  venomExecSemantics venomState venomInst finite_map list words

Theorem ld_dloadbytes_prefix_observations:
  X = [<|inst_id := ai; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [dest; Var z; len]; inst_outputs := []|>] /\
  dest <> Var z /\ len <> Var z /\
  ld_prefix C' fn' X p 1 t0 t1 ==>
  eval_operand dest t1 = eval_operand dest t0 /\
  eval_operand len t1 = eval_operand len t0 /\
  t1.vs_alloca_next = t0.vs_alloca_next /\
  t1.vs_code = t0.vs_code /\ t1.vs_labels = t0.vs_labels /\
  ?ow basew. eval_operand off t0 = SOME ow /\
    eval_operand (Label "code_end") t0 = SOME basew /\
    eval_operand (Var z) t1 = SOME (ow + basew)
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `v` (qx_choose_then `w` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  qpat_x_assum `step_inst 0 _ _ _ = OK w` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  map_every Cases_on [`dest`, `len`] >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ld_dloadbytes_trace_operands:
  X = [<|inst_id := ai; inst_opcode := ADD;
         inst_operands := [off; Label "code_end"]; inst_outputs := [z]|>;
       <|inst_id := ci; inst_opcode := CODECOPY;
         inst_operands := [dest; Var z; len]; inst_outputs := []|>] /\
  dest <> Var z /\ len <> Var z /\
  ld_prefix C' fn' X p 1 t0 t1 /\
  step_inst fuel C' (EL 1 X) t1 = OK u ==>
  ?ow basew dw nw.
    eval_operand off t0 = SOME ow /\
    eval_operand (Label "code_end") t0 = SOME basew /\
    eval_operand dest t0 = SOME dw /\ eval_operand len t0 = SOME nw /\
    eval_operand dest t1 = SOME dw /\
    eval_operand (Var z) t1 = SOME (ow + basew) /\
    eval_operand len t1 = SOME nw /\
    t1.vs_code = t0.vs_code /\ t1.vs_labels = t0.vs_labels
Proof
  strip_tac >>
  drule_all ld_dloadbytes_prefix_observations >> strip_tac >>
  qpat_x_assum `step_inst fuel _ _ _ = OK u` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  metis_tac[]
QED

val _ = if null (hyp ld_dloadbytes_trace_operands) then ()
  else raise Fail "public trace has hypotheses";

Theorem ld_dloadbytes_supply_temporary:
  inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dest;off;len] /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v supply.irs_used_vars) /\
  lower_dload_inst_supply supply inst = (X,rest) ==>
  ?ai ci z. X =
    [<|inst_id := ai; inst_opcode := ADD;
       inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
     <|inst_id := ci; inst_opcode := CODECOPY;
       inst_operands := [dest;Var z;len]; inst_outputs := []|>] /\
    ~MEM z supply.irs_used_vars /\ dest <> Var z /\ len <> Var z
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
  imp_res_tac (cj 1 fresh_ir_var_contract) >>
  imp_res_tac (cj 2 fresh_ir_var_contract) >>
  gvs[] >> metis_tac[]
QED

Theorem ld_dloadbytes_scalar_nonpointer:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  (off = Var v \/ len = Var v) ==> v NOTIN fn_pv P fn
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by fs[fn_ptr_ok_def] >>
  qpat_x_assum `fn_ptr_ok _ _` kall_tac >>
  rpt strip_tac >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  Cases_on `dest = Var v` >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ld_dloadbytes_scalar_observation:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dest;off;len] /\ (op = off \/ op = len) /\
  tn.t_var = f.lf_tv /\ taint_ok f.lf_fn tn inst f.lf_src /\
  eval_operand op f.lf_src = SOME x /\ eval_operand op f.lf_tgt = SOME y ==>
  x = y
Proof
  strip_tac >>
  `MEM op inst.inst_operands` by gvs[] >>
  `op_taint tn op = {}` by
    (irule ld_numeric_operand_untainted >>
     qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[]) >>
  `op_prov f.lf_H op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     irule ld_vars_unselected >> qexistsl_tac [`A`,`P`] >> simp[] >>
     irule ld_dloadbytes_scalar_nonpointer >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by simp[] >>
  drule_all ld_write_address_observation >> simp[]
QED

Theorem ld_dloadbytes_destinations:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ MEM inst (fn_insts f.lf_fn) /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  tn.t_var = f.lf_tv /\ taint_ok f.lf_fn tn inst f.lf_src /\
  access_ok lo (ld_erase A o_f f.lf_H) f.lf_fn inst f.lf_src /\
  ~in_revert_forward f.lf_fn f.lf_src /\
  eval_operand dest f.lf_src = SOME dw /\
  eval_operand dest f.lf_tgt = SOME dw' /\
  eval_operand len f.lf_src = SOME nw /\
  eval_operand off f.lf_src = SOME ow /\
  (!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)) ==>
  w2n nw = 0 \/
  (w2n dw = w2n dw' /\ w2n dw + w2n nw <= lo) \/
  (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
    w2n dw = b+delta /\ w2n dw' = c+delta /\ delta+w2n nw <= sz)
Proof
  strip_tac >> Cases_on `nw = 0w` >- simp[] >> simp[] >>
  `MEM dest inst.inst_operands` by simp[] >>
  `op_taint tn dest = {}` by
    (irule ld_numeric_operand_untainted >>
     qexistsl_tac [`f.lf_fn`,`inst`,`f.lf_src`] >> simp[]) >>
  `~MEM inst.inst_opcode [ASSIGN;PHI;RET;RETFMP;DRET]` by simp[] >>
  drule_all ld_write_address_observation >> strip_tac >>
  `mem_write_ops inst = SOME <|iao_ofst := dest; iao_size := SOME len; iao_max_size := SOME len|>` by
    simp[mem_write_ops_def] >>
  `MEM (w2n dw,w2n nw) (source_memory_write_ranges inst f.lf_src)` by
    simp[source_memory_write_ranges_def, sized_source_write_range_def] >>
  `0 < w2n nw` by (Cases_on `w2n nw` >> gvs[]) >>
  drule ld_write_access_classified >> simp[] >>
  disch_then (qspecl_then [`dw'`,`dw`,`w2n nw`] mp_tac) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem ld_envelope_supply_reserved:
  ld_envelope supply fn s j X p ==>
  ?ui rest inst. lower_dload_inst_supply ui inst = (X,rest) /\
    (!v. MEM v supply.irs_used_vars ==> MEM v ui.irs_used_vars) /\
    (?bb. MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
          EL j bb.bb_instructions = inst /\ bb.bb_label = s.vs_current_bb)
Proof
  strip_tac >> gvs[ld_envelope_def] >>
  Cases_on `lower_dload_blocks_supply supply (TAKE bi fn.fn_blocks)` >>
  rename1 `lower_dload_blocks_supply supply _ = (pre,ub)` >>
  Cases_on `lower_dload_insts_supply ub (TAKE j (EL bi fn.fn_blocks).bb_instructions)` >>
  rename1 `lower_dload_insts_supply ub _ = (middle,ui)` >>
  Cases_on `lower_dload_inst_supply ui (EL j (EL bi fn.fn_blocks).bb_instructions)` >>
  rename1 `lower_dload_inst_supply ui _ = (ys,rest)` >> gvs[] >>
  qexistsl_tac [`ui`,`rest`,`EL j (EL bi fn.fn_blocks).bb_instructions`] >> simp[] >>
  conj_tac
  >- (drule lower_dload_blocks_supply_flat >> strip_tac >>
      metis_tac[lower_dload_insts_supply_used_vars_mono]) >>
  qexists_tac `EL bi fn.fn_blocks` >> simp[] >> metis_tac[MEM_EL]
QED

Theorem ld_active_envelope_origin:
  ir_supply_covers_fn supply fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn inst s /\ ld_envelope supply fn s s.vs_inst_idx X p ==>
  ?bi bb ub ui.
    bi < LENGTH fn.fn_blocks /\ EL bi fn.fn_blocks = bb /\
    bb.bb_label = s.vs_current_bb /\ s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst /\
    ub = SND (lower_dload_blocks_supply supply (TAKE bi fn.fn_blocks)) /\
    ui = SND (lower_dload_insts_supply ub (TAKE s.vs_inst_idx bb.bb_instructions)) /\
    X = FST (lower_dload_inst_supply ui inst) /\
    (!v. MEM v (fn_ir_vars fn) ==> MEM v ui.irs_used_vars) /\
    MEM inst (fn_insts fn)
Proof
  strip_tac >>
  qpat_x_assum `ld_envelope _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ld_envelope_def] >> strip_tac >>
  qpat_x_assum `active_inst _ _ _` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `bb = bb'` by
    (irule ld_block_label_unique >> conj_tac >- simp[] >>
     qexists_tac `fn.fn_blocks` >> simp[] >> metis_tac[MEM_EL]) >> gvs[] >>
  qexists_tac `bi` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM v supply.irs_used_vars` by
        fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >>
      Cases_on `lower_dload_blocks_supply supply (TAKE bi fn.fn_blocks)` >>
      drule lower_dload_blocks_supply_flat >> strip_tac >>
      Cases_on `lower_dload_insts_supply r (TAKE s.vs_inst_idx (EL bi fn.fn_blocks).bb_instructions)` >>
      gvs[] >> metis_tac[lower_dload_insts_supply_used_vars_mono]) >>
  simp[fn_insts_def] >>
  `MEM (EL bi fn.fn_blocks) fn.fn_blocks` by metis_tac[MEM_EL] >>
  qpat_x_assum `s.vs_inst_idx < LENGTH _` mp_tac >>
  qpat_x_assum `MEM _ fn.fn_blocks` mp_tac >>
  qspec_tac (`EL bi fn.fn_blocks`,`bbx`) >> gen_tac >>
  qspec_tac (`fn.fn_blocks`,`bbs`) >> Induct >>
  simp[fn_insts_blocks_def] >> metis_tac[MEM_EL]
QED

Theorem ld_dloadbytes_envelope_temporary:
  ir_supply_covers_fn supply fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope supply fn s s.vs_inst_idx X p /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] ==>
  ?ai ci z. X =
    [<|inst_id := ai; inst_opcode := ADD;
       inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
     <|inst_id := ci; inst_opcode := CODECOPY;
       inst_operands := [dest;Var z;len]; inst_outputs := []|>] /\
    ~MEM z (fn_ir_vars fn) /\ dest <> Var z /\ len <> Var z
Proof
  strip_tac >> drule_all ld_active_envelope_origin >> strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> MEM v ui.irs_used_vars` by
    (rpt strip_tac >> first_x_assum irule >> irule ld_inst_input_ir >>
     qexists_tac `inst` >> gvs[]) >>
  `lower_dload_inst_supply ui inst = (X, SND (lower_dload_inst_supply ui inst))` by
    metis_tac[pairTheory.PAIR] >>
  drule_all ld_dloadbytes_supply_temporary >> strip_tac >>
  qexistsl_tac [`ai`,`ci`,`z`] >> simp[] >> metis_tac[]
QED

Theorem ld_dload_supply_temporary:
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v supply.irs_used_vars) /\
  MEM out supply.irs_used_vars /\ lower_dload_inst_supply supply inst = (X,rest) ==>
  ?ai zi ci mi a z. X =
    [<|inst_id := ai; inst_opcode := ALLOCA;
       inst_operands := [Lit 32w]; inst_outputs := [a]|>;
     <|inst_id := zi; inst_opcode := ADD;
       inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
     <|inst_id := ci; inst_opcode := CODECOPY;
       inst_operands := [Var a;Var z;Lit 32w]; inst_outputs := []|>;
     <|inst_id := mi; inst_opcode := MLOAD;
       inst_operands := [Var a]; inst_outputs := [out]|>] /\
    a <> z /\ out <> a /\ out <> z /\ off <> Var a /\
    ~MEM a supply.irs_used_vars /\ ~MEM z supply.irs_used_vars
Proof
  strip_tac >>
  gvs[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
  imp_res_tac (cj 1 fresh_ir_var_contract) >>
  imp_res_tac (cj 2 fresh_ir_var_contract) >>
  gvs[] >> metis_tac[]
QED

Theorem ld_dload_envelope_temporary:
  ir_supply_covers_fn f.lf_supply fn /\ f.lf_fn = fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ inst.inst_operands = [off] /\ inst.inst_outputs = [out] ==>
  ?ai zi ci mi a z. X =
    [<|inst_id := ai; inst_opcode := ALLOCA;
       inst_operands := [Lit 32w]; inst_outputs := [a]|>;
     <|inst_id := zi; inst_opcode := ADD;
       inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
     <|inst_id := ci; inst_opcode := CODECOPY;
       inst_operands := [Var a;Var z;Lit 32w]; inst_outputs := []|>;
     <|inst_id := mi; inst_opcode := MLOAD;
       inst_operands := [Var a]; inst_outputs := [out]|>] /\
    a <> z /\ out <> a /\ out <> z /\ off <> Var a /\
    ~MEM a (fn_ir_vars fn) /\ ~MEM z (fn_ir_vars fn) /\
    ld_private f inst.inst_id ai
Proof
  strip_tac >> drule_all ld_active_envelope_origin >> strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> MEM v ui.irs_used_vars` by
    (rpt strip_tac >> first_x_assum irule >> irule ld_inst_input_ir >>
     qexists_tac `inst` >> gvs[]) >>
  `MEM out ui.irs_used_vars` by
    (qpat_x_assum `!v. MEM v (fn_ir_vars fn) ==> _` irule >> irule ld_inst_output_ir >>
     qexists_tac `inst` >> simp[]) >>
  `lower_dload_inst_supply ui inst = (X,SND (lower_dload_inst_supply ui inst))` by
    metis_tac[pairTheory.PAIR] >>
  drule_all ld_dload_supply_temporary >> strip_tac >>
  qexistsl_tac [`ai`,`zi`,`ci`,`mi`,`a`,`z`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  pure_rewrite_tac[ld_private_def] >>
  qexistsl_tac [`bb`,`s.vs_inst_idx`,`bi`,`ub`,`ui`,`inst`,`X`] >>
  asm_simp_tac std_ss [LENGTH, HD] >>
  conj_tac >- (qexistsl_tac [`off`,`out`] >> rewrite_tac[]) >>
  conj_tac >- metis_tac[] >> simp[]
QED

Theorem ld_dload_operand_equal:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = DLOAD /\
  inst.inst_operands = [off] /\ tn.t_var = f.lf_tv /\
  taint_ok f.lf_fn tn inst f.lf_src ==>
  eval_operand off f.lf_src = eval_operand off f.lf_tgt
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==>
    MEM v (fn_ir_vars f.lf_fn) /\ v NOTIN fn_pv P f.lf_fn` by
    (gen_tac >> disch_tac >> conj_tac
     >- (irule ld_inst_input_ir >> qexists_tac `inst` >> simp[]) >>
     irule ld_ptr_use_scalar >> reverse conj_tac >- simp[] >> qexists_tac `inst` >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def]) >>
  `~MEM inst.inst_opcode
    [ASSIGN; PHI; RET; RETFMP; DRET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by simp[] >>
  drule_all ld_vars_numeric_operands_equal >>
  simp[eval_operands_def, AllCaseEqs()] >>
  Cases_on `eval_operand off f.lf_src` >> Cases_on `eval_operand off f.lf_tgt` >> simp[]
QED

Theorem ld_dload_trace_offset:
  (EL 0 X).inst_opcode = ALLOCA /\ (EL 0 X).inst_outputs = [a] /\
  (EL 1 X).inst_opcode = ADD /\
  (EL 1 X).inst_operands = [off; Label "code_end"] /\
  off <> Var a /\ ld_prefix C' fn' X p 3 t0 t ==>
  ?ow basew. eval_operand off t0 = SOME ow /\
    eval_operand (Label "code_end") t0 = SOME basew
Proof
  strip_tac >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `2`] |> SRULE []) >>
  disch_then (qx_choose_then `t2` (qx_choose_then `u2` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `1`] |> SRULE []) >>
  disch_then (qx_choose_then `t1` (qx_choose_then `u1` strip_assume_tac)) >>
  dxrule (ld_prefix_predecessor |> Q.INST [`h` |-> `0`] |> SRULE []) >>
  disch_then (qx_choose_then `tzero` (qx_choose_then `u0` strip_assume_tac)) >>
  gvs[ld_prefix_zero] >>
  `?sz:bytes32. exec_alloca (HD X) t0 sz = OK u0` by
    (qpat_x_assum `step_inst 0 _ _ _ = OK u0` mp_tac >>
     simp[ld_alloca_step] >> metis_tac[]) >>
  qpat_x_assum `step_inst 0 _ _ _ = OK u1` mp_tac >>
  simp[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `exec_alloca _ _ _ = OK u0` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `off` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_raw_reachable_code_data:
  !vs C fn inst s. raw_reachable vs C fn inst s ==>
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section
Proof
  ho_match_mp_tac raw_reachable_ind >>
  rw[enters_block_def, setup_callee_def] >>
  imp_res_tac step_inst_ok_code_data >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  gvs[setup_callee_def, AllCaseEqs()] >>
  qpat_x_assum `s_phi = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

Theorem ld_sync_source_code_layout:
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N ==>
  code_layout_valid s
Proof
  strip_tac >> drule ld_sync_source >> strip_tac >>
  drule_all ld_frame_raw_reachable >> strip_tac >>
  drule ld_raw_reachable_code_data >> strip_tac >>
  drule raw_reachable_labels >> strip_tac >>
  gvs[o1_run_state_ok_def, code_layout_valid_def]
QED

Theorem ld_sync_dload_code_offset:
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A frames N /\
  mem_inv dload_offset_ok C vs0 /\
  ((inst.inst_opcode = DLOAD /\ inst.inst_operands = [off]) \/
   (inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len])) /\
  eval_operand off s = SOME ow ==>
  ?basew. code_layout_valid s /\
    eval_operand (Label "code_end") s = SOME basew /\
    w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256)
Proof
  strip_tac >>
  `code_layout_valid s` by (irule ld_sync_source_code_layout >> metis_tac[]) >>
  `dload_offset_ok C fn inst s` by
    (irule ld_sync_source_mem_inv >> metis_tac[]) >>
  simp[] >>
  fs[code_layout_valid_def, eval_operand_def] >>
  qpat_x_assum `dload_offset_ok _ _ _ _` mp_tac >>
  simp[dload_offset_ok_def] >>
  disch_then (qspecl_then [`off`,`ow`] mp_tac) >> simp[]
QED

Theorem ld_dloadbytes_source_operands:
  ld_vars P A f /\ f.lf_src.vs_labels = f.lf_tgt.vs_labels /\
  fn_shape_ok f.lf_fn /\ fn_ptr_ok P f.lf_fn /\
  MEM inst (fn_insts f.lf_fn) /\ inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dest;off;len] /\
  tn.t_var = f.lf_tv /\ taint_ok f.lf_fn tn inst f.lf_src /\
  eval_operand dest f.lf_tgt = SOME dw' /\
  eval_operand off f.lf_tgt = SOME ow /\
  eval_operand len f.lf_tgt = SOME nw ==>
  ?dw. eval_operand dest f.lf_src = SOME dw /\
    eval_operand off f.lf_src = SOME ow /\
    eval_operand len f.lf_src = SOME nw
Proof
  strip_tac >>
  `?dw. eval_operand dest f.lf_src = SOME dw` by
    (irule ld_write_operand_defined >> metis_tac[listTheory.MEM]) >>
  `?ow0. eval_operand off f.lf_src = SOME ow0` by
    (irule ld_write_operand_defined >> metis_tac[listTheory.MEM]) >>
  `?nw0. eval_operand len f.lf_src = SOME nw0` by
    (irule ld_write_operand_defined >> metis_tac[listTheory.MEM]) >>
  `ow0 = ow` by (irule ld_dloadbytes_scalar_observation >> metis_tac[]) >>
  `nw0 = nw` by (irule ld_dloadbytes_scalar_observation >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ld_sync_dloadbytes_trace_evaluations:
  ld_sync lo P C vs0 stk PG G tn fn inst s t0 A (f::fs) N /\
  o1_ctx_shape C /\ o1_run_state_ok vs0 /\ ptr_discipline lo C vs0 /\
  mem_inv dload_offset_ok C vs0 /\ ir_supply_covers_fn f.lf_supply fn /\
  ld_envelope f.lf_supply fn s s.vs_inst_idx X p /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  ld_prefix C' fn' X p 1 t0 t1 /\ step_inst fuel C' (EL 1 X) t1 = OK u ==>
  ?ai ci z dw dw' ow nw basew.
    X = [<|inst_id := ai; inst_opcode := ADD;
           inst_operands := [off;Label "code_end"]; inst_outputs := [z]|>;
         <|inst_id := ci; inst_opcode := CODECOPY;
           inst_operands := [dest;Var z;len]; inst_outputs := []|>] /\
    ~MEM z (fn_ir_vars fn) /\
    eval_operand dest s = SOME dw /\ eval_operand off s = SOME ow /\
    eval_operand len s = SOME nw /\
    eval_operand dest t0 = SOME dw' /\
    eval_operand off t0 = SOME ow /\ eval_operand len t0 = SOME nw /\
    eval_operand dest t1 = SOME dw' /\
    eval_operand (Var z) t1 = SOME (ow+basew) /\
    eval_operand len t1 = SOME nw /\
    code_layout_valid s /\ eval_operand (Label "code_end") s = SOME basew /\
    t1.vs_code = s.vs_code /\
    w2n ow + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256)
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule_all ld_dloadbytes_envelope_temporary >> strip_tac >>
  drule_all ld_dloadbytes_trace_operands >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `fn_ptr_ok P fn` by metis_tac[ld_sync_ptr_ok] >>
  `s.vs_labels = t0.vs_labels` by metis_tac[ld_sync_labels] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  `?dw. eval_operand dest s = SOME dw /\
        eval_operand off s = SOME ow /\ eval_operand len s = SOME nw` by
    (drule ld_dloadbytes_source_operands >> simp[] >>
     disch_then drule >> simp[] >>
     disch_then (qspec_then `tn` mp_tac) >> simp[]) >>
  qpat_assum `ld_sync _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_sync_dload_code_offset) >> simp[] >>
  strip_tac >>
  `basew = basew'` by gvs[eval_operand_def] >>
  `t0.vs_code = s.vs_code` by
    (drule ld_sync_memory >> simp[ld_nonghost_def]) >>
  simp[]
QED

Theorem ld_sync_dloadbytes_destination_cases:
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ld_global lo A (f::fs) /\ o1_ctx_shape C /\ ptr_discipline lo C vs0 /\
  mem_inv dload_headroom_ok C vs0 /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ inst.inst_operands = [dest;off;len] /\
  eval_operand dest s = SOME dw /\ eval_operand dest t = SOME dw' /\
  eval_operand len s = SOME nw /\ eval_operand off s = SOME ow ==>
  (w2n nw = 0 \/
   (w2n dw = w2n dw' /\ w2n dw + w2n nw <= lo) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n dw = b+delta /\ w2n dw' = c+delta /\ delta+w2n nw <= sz)) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> lo <= b /\ lo <= c) /\
  (!k k' b c sz b' c' sz'.
    FLOOKUP A k = SOME (b,c,sz) /\ FLOOKUP A k' = SOME (b',c',sz') /\
    k <> k' /\ 0 < sz /\ 0 < sz' ==>
    (b+sz <= b' \/ b'+sz' <= b) /\ (c+sz <= c' \/ c'+sz' <= c))
Proof
  strip_tac >>
  drule ld_sync_active >> simp[] >> strip_tac >>
  drule_all ld_sync_fn_shape >> strip_tac >>
  drule o1_fn_shape_components >> strip_tac >>
  drule ld_sync_source >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[ld_active_inst_member] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ld_sync_labels] >>
  `taint_ok fn tn inst s` by metis_tac[ld_sync_taint_ok] >>
  drule_all ld_sync_access_ok >> strip_tac >>
  drule ld_sync_ghosts >> simp[] >> strip_tac >>
  `FDOM A = ld_slots A (f::fs)` by metis_tac[ld_sync_slots] >>
  `EVERY (ld_maps A) (f::fs)` by metis_tac[ld_sync_maps] >>
  `t.vs_alloca_next < dimword(:256)` by metis_tac[ld_sync_ambient_headroom] >>
  `!a b c sz. FLOOKUP A a = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (drule ld_alloc_target_no_wrap >> simp[]) >>
  conj_tac
  >- (drule ld_dloadbytes_destinations >> simp[] >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `tn` mp_tac) >> simp[] >>
      disch_then (qspec_then `lo` mp_tac) >> gvs[] >>
      disch_then irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[ld_alloc_bounds] >>
  metis_tac[ld_alloc_separate]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "public trace boundary has hypotheses")
  [ld_dloadbytes_supply_temporary, ld_dloadbytes_scalar_nonpointer,
   ld_dloadbytes_scalar_observation, ld_dloadbytes_destinations,
   ld_envelope_supply_reserved, ld_dloadbytes_envelope_temporary,
   ld_raw_reachable_code_data, ld_sync_source_code_layout,
   ld_sync_dload_code_offset, ld_dloadbytes_source_operands,
   ld_sync_dloadbytes_trace_evaluations, ld_sync_dloadbytes_destination_cases];

val _ = app (fn th => if null (hyp th) then () else
  raise Fail "active envelope boundary has hypotheses")
  [ld_active_envelope_origin, ld_dloadbytes_envelope_temporary,
   ld_dload_supply_temporary, ld_dload_envelope_temporary, ld_dload_operand_equal];
