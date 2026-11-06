Theory fnPlanLineageEntryProduction
Ancestors
  fnPlanLineageCallers fnPlanLineageSetup fnPlanLineagePath
  stackPlanGen venomWf venomInst passSharedDefs removeUnusedProofs removeUnusedSsaProofs list rich_list finite_map bag

(* Chronological origins include dead definitions retained by native emission.
   They are deliberately independent of the liveness set. *)
Definition prefix_inventory_origins_def:
  prefix_inventory_origins bb i ps <=>
    !v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      ?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs
End

Definition entry_boundary_resources_def:
  entry_boundary_resources fn bb i ps <=>
    prefix_inventory_origins bb i ps /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1)
End

Theorem prefix_inventory_outputs_fresh:
  !fn bb i ps v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\ prefix_inventory_origins bb i ps /\
    MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[prefix_inventory_origins_def] >>
  CCONTR_TAC >> gvs[] >>
  `?j. j < i /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `i = j` by metis_tac[ssa_form_position] >> decide_tac
QED

Theorem initialized_entry_boundary_resources:
  !fn ch growth spill_base lbl_ctr ps.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) ==>
    entry_boundary_resources fn (HD fn.fn_blocks)
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >>
  disch_then (qspecl_then [`ch`, `growth`, `spill_base`, `lbl_ctr`] strip_assume_tac) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `fn_reachable fn (HD fn.fn_blocks).bb_label` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_reachable_def, fn_entry_label_def, entry_block_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <=
    LENGTH (HD fn.fn_blocks).bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp_tac bool_ss [entry_boundary_resources_def] >>
  conj_tac
  >- (simp_tac bool_ss [prefix_inventory_origins_def] >>
      rpt strip_tac >>
      `MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))` by
        (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
      drule_at (Pat `MEM _ (live_vars_at _ _ _)`) interval_live_origin >>
      disch_then (qspec_then `0` mp_tac) >>
      simp[fnPlanLineageDemandTheory.analyzed_hd_live_empty] >>
      strip_tac >> qexists_tac `k` >> simp[] >> decide_tac) >>
  conj_tac
  >- (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
  gvs[] >> metis_tac[fnPlanLineageInventoryTheory.all_distinct_elem_count_le_one]
QED

Theorem entry_regular_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    entry_boundary_resources fn bb i ps /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = (ops,qs) ==>
    entry_boundary_resources fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    (irule codegen_ready_inst_outputs_distinct >>
     qexists_tac `fn` >>
     simp[fn_insts_def, removeUnusedSsaProofsTheory.fn_insts_blocks_flat,
       MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]) >>
  `prefix_inventory_origins bb i ps` by gvs[entry_boundary_resources_def] >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (gvs[entry_boundary_resources_def] >>
     metis_tac[analyzed_computed_operand_demand]) >>
  `!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    metis_tac[prefix_inventory_outputs_fresh] >>
  `EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
    ~MEM (Var v) (compute_operands (EL i bb.bb_instructions)))
    (EL i bb.bb_instructions).inst_outputs` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  `!v. MEM v (operand_vars (compute_operands (EL i bb.bb_instructions)) ++
      live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by
    (rpt strip_tac >>
     Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
     >- (`~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
         `LIST_ELEM_COUNT (Var v) ps.ps_stack = 0` by
           metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF,
             arithmeticTheory.NOT_ZERO_LT_ZERO] >> simp[]) >>
     `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
       (irule analyzed_computed_operand_demand >>
        gvs[MEM_APPEND, reorderSimTheory.input_mem_operand_vars, MEM_operand_vars_eq_Var]) >>
     gvs[entry_boundary_resources_def]) >>
  simp_tac bool_ss [entry_boundary_resources_def] >>
  conj_tac
  >- (simp_tac bool_ss [prefix_inventory_origins_def] >> rpt strip_tac >>
      drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        native_regular_variable_origins >> simp[] >>
      disch_tac >>
      `MEM v (EL i bb.bb_instructions).inst_outputs \/
       MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
      (Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
       >- (qexists_tac `i` >> simp[])) >>
      `?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs` by
        metis_tac[prefix_inventory_origins_def] >>
      qexists_tac `j` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all native_regular_live_lower >> simp[]) >>
  rpt strip_tac >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_next_live_upper >>
  simp[MEM_APPEND, reorderSimTheory.input_mem_operand_vars, MEM_operand_vars_eq_Var]
QED

Theorem entry_inst_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode /\
    entry_boundary_resources fn bb i ps /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    entry_boundary_resources fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      `prefix_inventory_origins bb i ps` by gvs[entry_boundary_resources_def] >>
      `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
        (irule prefix_inventory_outputs_fresh >>
         qexistsl_tac [`bb`, `fn`, `i`] >> simp[]) >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\ v <> out ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, generate_offset_plan_def,
        stackModelTheory.stack_push_def, SNOC_APPEND] >>
      simp_tac bool_ss [entry_boundary_resources_def] >>
      conj_tac
      >- (simp[prefix_inventory_origins_def, MEM_APPEND] >>
          qx_gen_tac `w` >> Cases_on `w = out`
          >- (rpt strip_tac >> qexists_tac `i` >> simp[]) >>
          rpt strip_tac >>
          `?j. j < i /\ j < LENGTH bb.bb_instructions /\
            MEM w (EL j bb.bb_instructions).inst_outputs` by
            metis_tac[prefix_inventory_origins_def] >>
          qexists_tac `j` >> simp[]) >>
      conj_tac
      >- (gvs[entry_boundary_resources_def] >> qx_gen_tac `w` >> strip_tac >>
          Cases_on `w = out` >> simp[] >> metis_tac[]) >>
      qx_gen_tac `w` >> strip_tac >> Cases_on `w = out`
      >- (gvs[] >>
          `LIST_ELEM_COUNT (Var out) ps.ps_stack = 0` by
            (qpat_x_assum `~MEM (Var out) ps.ps_stack` mp_tac >>
             simp_tac std_ss [GSYM LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
          simp[reorderSimTheory.elem_count_append, LIST_ELEM_COUNT_THM]) >>
      `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label i)` by metis_tac[] >>
      gvs[entry_boundary_resources_def, reorderSimTheory.elem_count_append,
        LIST_ELEM_COUNT_THM]) >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode = NOP`
  >- (`(EL i bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[]) >>
      gvs[generate_inst_plan_def, entry_boundary_resources_def] >>
      gvs[prefix_inventory_origins_def] >> rpt strip_tac >>
      `?j. j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
      qexists_tac `j` >> simp[]) >>
  irule entry_regular_boundary_step >>
  goal_assum (drule_at Any) >>
  gvs[generate_inst_plan_def, AllCaseEqs()] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* Exact native prefix: the unexecuted tail, not a truncated list, determines
   both next-live and next-terminator arguments. No resource premise occurs. *)
Inductive native_inst_prefix:
  (!lv dfg cfg fn label halting n len xs ps.
    native_inst_prefix lv dfg cfg fn label halting n len xs ps 0 ps) /\
  (!lv dfg cfg fn label halting n len xs ps0 k ps inst rest ops qs.
    native_inst_prefix lv dfg cfg fn label halting n len xs ps0 k ps /\
    DROP k xs = inst::rest /\
    generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv label len
       else live_vars_at lv label (k+n+1)) halting
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      label ps = SOME (ops,qs) ==>
    native_inst_prefix lv dfg cfg fn label halting n len xs ps0 (SUC k) qs)
End

Theorem native_inst_prefix_zero:
  native_inst_prefix lv dfg cfg fn label halting n len xs ps 0 qs <=> qs = ps
Proof
  simp[Once native_inst_prefix_cases] >> metis_tac[]
QED

Theorem native_inst_prefix_bound:
  !lv dfg cfg fn label halting n len xs ps k qs.
    native_inst_prefix lv dfg cfg fn label halting n len xs ps k qs ==>
    k <= LENGTH xs
Proof
  ho_match_mp_tac native_inst_prefix_ind >> conj_tac >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
  simp[] >> decide_tac
QED

Theorem native_inst_prefix_one:
  native_inst_prefix lv dfg cfg fn label halting n len (inst::rest) ps 1 qs <=>
    ?ops. generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv label len
       else live_vars_at lv label (n+1)) halting
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      label ps = SOME (ops,qs)
Proof
  simp[Once native_inst_prefix_cases, native_inst_prefix_zero] >> metis_tac[]
QED

Theorem native_inst_prefix_resources:
  !lv dfg cfg fn label halting n len xs ps0 k ps.
    native_inst_prefix lv dfg cfg fn label halting n len xs ps0 k ps ==>
    !bb. lv = liveness_analyze fn /\ label = bb.bb_label /\
      n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      entry_boundary_resources fn bb n ps0 /\
      (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\
                       (EL j xs).inst_opcode <> PHI) ==>
      entry_boundary_resources fn bb (n+k) ps
Proof
  ho_match_mp_tac native_inst_prefix_ind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k (non_param_insts bb)` by
    metis_tac[listTheory.HD_DROP, listTheory.HD] >>
  `inst = EL (LENGTH (get_params bb.bb_instructions) + k) bb.bb_instructions` by
    metis_tac[ready_block_suffix_index] >>
  `entry_boundary_resources fn bb (LENGTH (get_params bb.bb_instructions)+k) ps` by
    (simp[arithmeticTheory.ADD_COMM] >> first_x_assum irule >> simp[]) >>
  `LENGTH (get_params bb.bb_instructions)+k < LENGTH bb.bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `~is_param_opcode inst.inst_opcode` by
    (`MEM inst (non_param_insts bb)` by metis_tac[EL_MEM] >>
     gvs[non_param_insts_def, MEM_FILTER]) >>
  `(if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label
      (k + LENGTH (get_params bb.bb_instructions) + 1)) =
    live_vars_at (liveness_analyze fn) bb.bb_label
      (SUC (LENGTH (get_params bb.bb_instructions) + k))` by
    (irule ready_block_suffix_next_live >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `!bb'. _ ==> entry_boundary_resources _ _ _ _` kall_tac >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
  irule entry_inst_boundary_step >>
  goal_assum (drule_at Any) >>
  simp_tac bool_ss [] >>
  rule_assum_tac (REWRITE_RULE [GSYM arithmeticTheory.ADD_ASSOC]) >>
  qpat_x_assum `inst = EL _ bb.bb_instructions`
    (fn th => rewrite_tac[GSYM th]) >>
  asm_simp_tac bool_ss [] >>
  qexistsl_tac [`cfg`, `dfg`, `halting`, `ops`, `ps`,
    `case rest of [] => F | h::t => is_terminator h.inst_opcode`] >>
  conj_tac >- (qpat_x_assum `_ = live_vars_at _ _ _`
    (fn th => fs[th])) >>
  asm_simp_tac bool_ss []
QED

Theorem jmp_no_target_state:
  !lv dfg cfg fn inst next halt term cur ps ops qs succ.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    inst.inst_operands = [Label succ] /\
    join_target_ops lv fn cur inst = NONE /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) ==>
    qs = release_dead_spills next ps
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       venomInstTheory.is_param_opcode_def] >>
  simp[generate_regular_inst_plan_def, compute_operands_def,
       asmIRTheory.get_non_label_operands_def, emit_input_plan_def,
       stackPlanTypesTheory.is_label_operand_def,
       venomEffectsTheory.is_commutative_def,
       generate_emit_ops_def, asmIRTheory.venom_to_evm_name_def,
       stackModelTheory.stack_pop_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem entry_jmp_no_target_boundary_step:
  !fn bb i ps dfg cfg halting term ops qs succ.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = JMP /\
    (EL i bb.bb_instructions).inst_outputs = [] /\
    (EL i bb.bb_instructions).inst_operands = [Label succ] /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (EL i bb.bb_instructions) = NONE /\
    entry_boundary_resources fn bb i ps /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    entry_boundary_resources fn bb (SUC i) qs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all jmp_no_target_state >> strip_tac >> gvs[] >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (rpt strip_tac >> irule analyzed_computed_operand_demand >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp_tac bool_ss [entry_boundary_resources_def] >>
  conj_tac
  >- (gvs[entry_boundary_resources_def, prefix_inventory_origins_def,
          fnPlanLineageInventoryTheory.release_dead_spills_stack,
          fnPlanLineageInventoryTheory.release_dead_spills_domain] >>
      rpt strip_tac >>
      qpat_x_assum `!v. MEM (Var v) ps.ps_stack \/ _ ==> _`
        (qspec_then `v` mp_tac) >> simp[] >>
      strip_tac >> qexists_tac `j` >> simp[]) >>
  conj_tac
  >- (gvs[entry_boundary_resources_def,
          fnPlanLineageInventoryTheory.release_dead_spills_stack,
          fnPlanLineageInventoryTheory.release_dead_spills_domain,
          MEM_MAP] >>
      metis_tac[]) >>
  rpt strip_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  irule_at Any fnPlanLineageInventoryTheory.release_dead_spills_resource_nonincrease >>
  gvs[entry_boundary_resources_def]
QED
