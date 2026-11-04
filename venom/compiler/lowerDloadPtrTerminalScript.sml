Theory lowerDloadPtrTerminal
Ancestors
  lowerDloadPtrForward lowerDloadPtrJointClosureProbe lowerDloadPtrJointNext
  lowerDloadPtrRel o1ContractLowerDload lowerDloadPtrCopy frameRawReachable
  lowerDloadDefs venomInst list rich_list unitShapeDefs lowerDloadPtrStatic
  lowerDloadPtrAggregate lowerDloadPtrPhi lowerDloadPtrCall venomState ptrDiscipline
  venomExecSemantics o1PassContract venomWf contextCodegenRel lowerDloadPtrOrdinary
  lowerDloadPtrBlockEntry finite_map pred_set

(* Reverse prefix origin is independent of resolver equalities and freshness.
   Even malformed DLOAD branches cannot begin with ASSIGN or REVERT. *)
Theorem lower_dload_terminal_prefix_origin:
  !pre q xs rest q'.
    EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) pre /\
    lower_dload_insts_supply q xs = (pre ++ rest,q') ==>
    ?tail. xs = pre ++ tail /\ lower_dload_insts_supply q tail = (rest,q')
Proof
  Induct_on `pre`
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `xs`
  >- gvs[lower_dload_insts_supply_def] >>
  rename1 `lower_dload_insts_supply q (i::is) = _` >>
  Cases_on `lower_dload_inst_supply q i` >>
  rename1 `lower_dload_inst_supply q i = (out,q1)` >>
  Cases_on `lower_dload_insts_supply q1 is` >>
  rename1 `lower_dload_insts_supply q1 is = (outs,q2)` >>
  `out <> []` by metis_tac[lower_dload_inst_supply_nonempty] >>
  gvs[lower_dload_insts_supply_def] >>
  Cases_on `out` >- gvs[] >>
  gvs[] >>
  `h = i` by
    (irule lower_dload_inst_supply_control >>
     conj_tac >- (goal_assum $ drule_at Any >> simp[]) >>
     simp[is_terminator_def]) >>
  gvs[] >>
  rename1 `lower_dload_inst_supply q i = (i::t,q1)` >>
  `lower_dload_inst_supply q i = ([i],q)` by
    (irule lower_dload_inst_supply_special >> simp[] >> metis_tac[]) >>
  gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists `tail` >> simp[]
QED

Theorem lower_dload_terminal_boundary_origin:
  lower_dload_insts_supply q (left ++ src) = (pre ++ mid ++ rest,q') /\
  lower_dload_insts_supply q left = (pre,u) /\
  EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) mid ==>
  ?tail. src = mid ++ tail /\
    lower_dload_insts_supply u tail = (rest,q') /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply q (TAKE (LENGTH left + k) (left ++ src)) =
        (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
  drule_all lower_dload_terminal_prefix_origin >> strip_tac >>
  qexists `tail` >> simp[TAKE_APPEND] >> rpt strip_tac >>
  simp[TAKE_APPEND] >>
  `lower_dload_insts_supply u (TAKE k mid) = (TAKE k mid,u)` by
    (irule lower_dload_insts_supply_unchanged >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     `MEM q'' mid` by metis_tac[MEM_TAKE] >>
     qpat_x_assum `!i. MEM i mid ==> _` drule >> simp[]) >>
  Cases_on `lower_dload_insts_supply q (left ++ TAKE k mid)` >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
  `k - LENGTH mid = 0` by decide_tac >>
  simp[TAKE_LENGTH_TOO_LONG]
QED

Theorem lower_dload_terminal_index_origin:
  lower_dload_insts_supply q xs = (pre ++ mid ++ rest,q') /\
  n <= LENGTH xs /\
  lower_dload_insts_supply q (TAKE n xs) = (pre,u) /\
  EVERY (\i. i.inst_opcode = ASSIGN \/ i.inst_opcode = REVERT) mid ==>
  n + LENGTH mid <= LENGTH xs /\
  TAKE (LENGTH mid) (DROP n xs) = mid /\
  (!k. k <= LENGTH mid ==>
    lower_dload_insts_supply q (TAKE (n+k) xs) = (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  `?tail. DROP n xs = mid ++ tail /\
    lower_dload_insts_supply u tail = (rest,q') /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply q
        (TAKE (LENGTH (TAKE n xs) + k) (TAKE n xs ++ DROP n xs)) =
        (pre ++ TAKE k mid,u))` by
    (match_mp_tac lower_dload_terminal_boundary_origin >> simp[]) >>
  `LENGTH (DROP n xs) = LENGTH mid + LENGTH tail` by
    metis_tac[LENGTH_APPEND] >>
  gvs[TAKE_DROP, LENGTH_DROP, LENGTH_TAKE] >> simp[TAKE_APPEND]
QED

Theorem dload_control_terminal_slice_origin:
  dload_control_match q f g s t i emitted 0 /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  lookup_block t.vs_current_bb g.fn_blocks = SOME tb /\
  d <= LENGTH (DROP t.vs_inst_idx tb.bb_instructions) /\
  mid = TAKE d (DROP t.vs_inst_idx tb.bb_instructions) /\
  EVERY (\j. j.inst_opcode = ASSIGN \/ j.inst_opcode = REVERT) mid ==>
  ?bb bs pre u.
    MEM bb f.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx + LENGTH mid <= LENGTH bb.bb_instructions /\
    TAKE (LENGTH mid) (DROP s.vs_inst_idx bb.bb_instructions) = mid /\
    t.vs_inst_idx = LENGTH pre /\
    lower_dload_insts_supply bs (TAKE s.vs_inst_idx bb.bb_instructions) = (pre,u) /\
    (!k. k < LENGTH mid ==>
      EL (s.vs_inst_idx+k) bb.bb_instructions =
      EL (t.vs_inst_idx+k) tb.bb_instructions) /\
    (!k. k <= LENGTH mid ==>
      lower_dload_insts_supply bs (TAKE (s.vs_inst_idx+k) bb.bb_instructions) =
        (pre ++ TAKE k mid,u))
Proof
  strip_tac >>
  qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_control_match_def] >> strip_tac >>
  `?aq. lower_dload_blocks_supply q f.fn_blocks = (g.fn_blocks,aq)` by
    (gvs[lower_dload_function_supply_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all dload_blocks_supply_el >> strip_tac >>
  qmatch_asmsub_abbrev_tac `lower_dload_block_supply bs _ = (gb,_)` >>
  `gb.bb_label = (EL bi f.fn_blocks).bb_label /\
   ?aq. lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
     (gb.bb_instructions,aq)` by
    (qpat_x_assum `lower_dload_block_supply _ _ = _` mp_tac >>
     simp[lower_dload_block_supply_def, AllCaseEqs()] >> strip_tac >> gvs[]) >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME gb` by
    (irule venomExecProofsTheory.MEM_lookup_block >> simp[Abbr `gb`, EL_MEM]) >>
  gvs[] >>
  `?outs. gb.bb_instructions = before ++ outs` by
    (`lower_dload_insts_supply bs
        (TAKE s.vs_inst_idx (EL bi f.fn_blocks).bb_instructions ++
         DROP s.vs_inst_idx (EL bi f.fn_blocks).bb_instructions) =
       (gb.bb_instructions,aq')` by simp[] >>
     drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  gvs[DROP_APPEND] >>
  `lower_dload_insts_supply bs (EL bi f.fn_blocks).bb_instructions =
    (before ++ TAKE d outs ++ DROP d outs,aq')` by simp[TAKE_DROP] >>
  `s.vs_inst_idx <= LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  drule_all lower_dload_terminal_index_origin >> strip_tac >>
  qexistsl [`EL bi f.fn_blocks`,`bs`,`before`,`is`] >>
  gvs[EL_MEM, LENGTH_TAKE, arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> simp[EL_APPEND_EQN] >>
  qpat_x_assum `TAKE d _ = TAKE d _` mp_tac >>
  qpat_x_assum `k < d` mp_tac >>
  qpat_x_assum `d + s.vs_inst_idx <= _` mp_tac >>
  qpat_x_assum `d <= LENGTH outs` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  `k < LENGTH outs /\ k + s.vs_inst_idx <
    LENGTH (EL bi f.fn_blocks).bb_instructions` by decide_tac >>
  metis_tac[EL_TAKE, EL_DROP, arithmeticTheory.ADD_COMM]
QED

(* Actual original operand membership also rules out opaque return PCs. *)
Theorem dload_copy_operand_origin:
  opaque_use_ok f /\ MEM i (fn_insts f) /\
  i.inst_opcode = RETURNDATACOPY /\ MEM (Var v) i.inst_operands ==>
  v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}
Proof
  strip_tac >> simp[] >> conj_tac
  >- metis_tac[fn_ir_vars_operand] >>
  strip_tac >> drule_all opaque_use_ok_retpc_use >>
  simp[retpc_use_ok_def]
QED

Theorem dload_copy_boundary_scalar_origin:
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ opaque_use_ok f /\
  FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) ==>
  eval_operand off s = eval_operand off t /\
  eval_operand sz s = eval_operand sz t /\
  (eval_operand dst s = NONE <=> eval_operand dst t = NONE) /\
  LENGTH s.vs_returndata = LENGTH t.vs_returndata
Proof
  strip_tac >>
  `s.vs_labels = t.vs_labels /\ s.vs_returndata = t.vs_returndata` by
    (drule dload_boundary_environment >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  `!v. MEM (Var v) i.inst_operands ==>
     v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by
    (rpt strip_tac >> irule dload_copy_operand_origin >> metis_tac[]) >>
  `!op. MEM op i.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)` by
    (rpt strip_tac >> irule eval_operand_definedness >> simp[] >>
     metis_tac[fn_ir_vars_operand]) >>
  `op_prov G off = NONE /\ op_prov G sz = NONE /\
   op_taint tn dst = {} /\ op_taint tn off = {} /\ op_taint tn sz = {}` by
    (irule external_copy_scalar_clean >> simp[] >> metis_tac[]) >>
  `dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
     G H tn un s t` by metis_tac[dload_boundary_vars] >>
  simp[] >>
  `eval_operand dst s = NONE <=> eval_operand dst t = NONE` by metis_tac[MEM] >>
  simp[] >> conj_tac >> irule scalar_operand_equal >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM]
QED

Theorem dload_copy_boundary_terminal_fields:
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  i.inst_outputs = [] /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ opaque_use_ok f /\
  FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) = op_taint tn (Var v)) /\
    (!v. op_taint (step_taint i t t' un) (Var v) = op_taint un (Var v)) /\
    dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  drule_all dload_copy_boundary_scalar_origin >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `eval_operand dst s <> NONE` by metis_tac[optionTheory.NOT_SOME_NONE] >>
  Cases_on `eval_operand dst s` >- gvs[] >>
  rename1 `eval_operand dst s = SOME d` >>
  rename1 `eval_operand off s = SOME a` >>
  rename1 `eval_operand sz s = SOME z` >>
  qexists `write_memory_with_expansion (w2n d)
    (TAKE (w2n z) (DROP (w2n a) s.vs_returndata)) s` >>
  `s.vs_labels = t.vs_labels /\
   dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
     G H tn un s t` by
    (conj_tac
     >- (drule dload_boundary_environment >>
         simp[dload_equal_environment_def, venom_state_component_equality]) >>
     irule dload_boundary_vars >> goal_assum (drule_at Any)) >>
  `!bs. step_prov PG G i (write_memory_with_expansion (w2n d) bs s) = G /\
    step_taint i s (write_memory_with_expansion (w2n d) bs s) tn =
      tn with t_mem := tn.t_mem DIFF {j | w2n d <= j /\ j < w2n d + w2n z}` by
    (gen_tac >> irule external_copy_ghosts >> simp[] >> metis_tac[]) >>
  `!bs. step_prov PH H i (write_memory_with_expansion (w2n destOffset) bs t) = H /\
    step_taint i t (write_memory_with_expansion (w2n destOffset) bs t) un =
      un with t_mem := un.t_mem DIFF {j | w2n destOffset <= j /\ j < w2n destOffset + w2n z}` by
    (gen_tac >> irule external_copy_ghosts >> simp[] >> metis_tac[]) >>
  simp[write_memory_with_expansion_def, lookup_var_def,
       dload_vars_match_def, op_taint_def] >>
  gvs[dload_vars_match_def, op_taint_def, lookup_var_def]
QED

(* All scalar/shape/success premises above now come from the actual source
   contract and phase-zero control, rather than a new terminal assumption. *)
Theorem dload_actual_copy_terminal_fields:
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  i.inst_opcode = RETURNDATACOPY /\ i.inst_operands = [dst;off;sz] /\
  FDOM G SUBSET fn_pv P f /\
  dload_boundary_core lo fs
    (set (fn_ir_vars f) DIFF {v | retpc_var f v}) Ws
    PG PH G H tn un s t cs ds /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    (!v. op_taint (step_taint i s s' tn) (Var v) = op_taint tn (Var v)) /\
    (!v. op_taint (step_taint i t t' un) (Var v) = op_taint un (Var v)) /\
    dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `MEM f C.ctx_functions` by
    (drule frame_reachable_raw_certificate >> simp[] >> strip_tac >> simp[]) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  `fn_ptr_ok P f` by metis_tac[EVERY_MEM] >>
  `fn_inst_wf f /\ opaque_use_ok f` by
    (qpat_x_assum `o1_ctx_shape C` mp_tac >>
     simp[o1_ctx_shape_def, EVERY_MEM] >> strip_tac >>
     first_x_assum drule >> simp[o1_fn_shape_def, fn_shape_ok_def]) >>
  `inst_wf i` by
    (gvs[fn_inst_wf_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  `i.inst_outputs = []` by gvs[inst_wf_def] >>
  `taint_ok f tn i s` by
    (qpat_x_assum `ptr_discipline _ _ _` mp_tac >>
     simp[ptr_discipline_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  irule dload_copy_boundary_terminal_fields >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Success reflection is independent of opaque-variable ghost matching. *)
Theorem dload_terminal_assign_definedness:
  i.inst_opcode = ASSIGN /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE))
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  simp[assign_step_success] >> strip_tac >> gvs[] >>
  `eval_operand op s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `op` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand op s` >- gvs[] >>
  qexists `update_var out x s` >>
  simp[assign_step_success, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = out` >> gvs[lookup_var_def]
QED

Theorem dload_terminal_assign_vars_match:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  eval_operand op s = SOME a /\ eval_operand op t = SOME b /\
  s.vs_labels = t.vs_labels /\
  dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    G H tn un s t ==>
  dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    (step_prov PG G i (update_var out a s))
    (step_prov PH H i (update_var out b t))
    (step_taint i s (update_var out a s) tn)
    (step_taint i t (update_var out b t) un)
    (update_var out a s) (update_var out b t)
Proof
  strip_tac >>
  `out IN set (fn_ir_vars f) DIFF {v | retpc_var f v} ==>
    op_taint tn op = op_taint un op /\
    dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) a b` by
    (strip_tac >>
     `!v. op = Var v ==> v IN set (fn_ir_vars f) DIFF {v | retpc_var f v}` by
       (simp[] >> gen_tac >> strip_tac >> conj_tac
        >- metis_tac[fn_ir_vars_operand, MEM] >>
        irule retpc_assign_input_tracked >> qexistsl [`i`,`out`] >> gvs[]) >>
     conj_tac
     >- (Cases_on `op` >> gvs[op_taint_def, dload_vars_match_def]) >>
     irule dload_matched_operand >>
     qexistsl [`set (fn_ir_vars f) DIFF {v | retpc_var f v}`,`s`,`t`,`un`] >> simp[]) >>
  `step_prov PG G i (update_var out a s) = set_prov G [out] (op_prov G op) /\
   step_taint i s (update_var out a s) tn =
     tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op)` by
    (irule assign_ghost_updates >> simp[]) >>
  `step_prov PH H i (update_var out b t) = set_prov H [out] (op_prov H op) /\
   step_taint i t (update_var out b t) un =
     un with t_var := set_var_taint un.t_var [out] (op_taint un op)` by
    (irule assign_ghost_updates >> simp[]) >>
  simp[] >> irule dload_vars_match_write >> simp[]
QED

Theorem dload_terminal_assign_fields:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. v IN set (fn_ir_vars f) ==>
    (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
    G H tn un s t /\ step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel C i s = OK s' /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    t'.vs_allocas = t.vs_allocas /\ t'.vs_alloca_next = t.vs_alloca_next /\
    s'.vs_labels = t'.vs_labels /\
    (!v. v IN set (fn_ir_vars f) ==>
      (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_vars_match fs (set (fn_ir_vars f) DIFF {v | retpc_var f v})
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!v. MEM (Var v) i.inst_operands ==> v IN set (fn_ir_vars f)` by
    metis_tac[fn_ir_vars_operand] >>
  drule_all dload_terminal_assign_definedness >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  qexists `s'` >> simp[] >>
  qpat_x_assum `step_inst _ _ _ t = _` mp_tac >>
  qpat_x_assum `step_inst _ _ _ s = _` mp_tac >>
  simp[assign_step_success] >> rpt strip_tac >> gvs[] >>
  irule dload_terminal_assign_vars_match >>
  goal_assum (drule_at Any) >> simp[]
QED
