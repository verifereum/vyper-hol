Theory fnPlanLineageEntryProduction
Ancestors
  fnPlanLineagePhiInputExclusion fnPlanLineagePhiLiveBudget
  fnPlanLineageLiveness fnPlanLineageJoinEntry fnPlanLineageNativeResources fnPlanLineageNativeOrigins
  fnPlanLineageCallers fnPlanLineageSetup fnPlanLineagePath fnPlanLineageSuffix fnPlanLineagePrefix
  callLayoutDefs stackPlanGen venomWf venomInst passSharedDefs removeUnusedProofs removeUnusedSsaProofs list rich_list finite_map bag

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
  `native_live_boundary fn bb i ps` by
    gvs[entry_boundary_resources_def, native_live_boundary_def] >>
  `!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    metis_tac[entry_boundary_resources_def, prefix_inventory_outputs_fresh] >>
  `native_live_boundary fn bb (SUC i) qs` by
    (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       native_regular_live_boundary_step >> simp[]) >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[native_live_boundary_operands] >>
  simp_tac bool_ss [entry_boundary_resources_def] >> reverse conj_tac
  >- gvs[native_live_boundary_def] >>
  simp_tac bool_ss [prefix_inventory_origins_def] >> rpt strip_tac >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_regular_variable_origins >> simp[] >> disch_tac >>
  (Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
   >- (qexists_tac `i` >> simp[]) >>
   `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
   `?j. j < i /\ j < LENGTH bb.bb_instructions /\
     MEM v (EL j bb.bb_instructions).inst_outputs` by
     (gvs[entry_boundary_resources_def] >> metis_tac[prefix_inventory_origins_def]) >>
   qexists_tac `j` >> simp[])
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
  `native_live_boundary fn bb i ps` by
    gvs[entry_boundary_resources_def, native_live_boundary_def] >>
  `!v. MEM v (EL i bb.bb_instructions).inst_outputs ==>
    ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled` by
    metis_tac[entry_boundary_resources_def, prefix_inventory_outputs_fresh] >>
  `native_live_boundary fn bb (SUC i) qs` by
    (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       native_inst_live_boundary_step >> simp[]) >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `((EL i bb.bb_instructions).inst_opcode = PHI \/
    (EL i bb.bb_instructions).inst_opcode = OFFSET) ==>
    (EL i bb.bb_instructions).inst_outputs <> []` by
    (strip_tac >> drule_all inst_wf_offset_shape >> strip_tac >> simp[]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[native_live_boundary_operands] >>
  simp_tac bool_ss [entry_boundary_resources_def] >> reverse conj_tac
  >- gvs[native_live_boundary_def] >>
  simp_tac bool_ss [prefix_inventory_origins_def] >> rpt strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    native_inst_variable_origins >> simp[] >> disch_tac >>
  (Cases_on `MEM v (EL i bb.bb_instructions).inst_outputs`
   >- (qexists_tac `i` >> simp[]) >>
   `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
   `?j. j < i /\ j < LENGTH bb.bb_instructions /\
     MEM v (EL j bb.bb_instructions).inst_outputs` by
     (gvs[entry_boundary_resources_def] >> metis_tac[prefix_inventory_origins_def]) >>
   qexists_tac `j` >> simp[])
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

(* Conservative operation-carrying refinement, retaining original-tail flags. *)
Inductive native_inst_ops_prefix:
  (!lv dfg cfg fn lbl halt np bl xs p0.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 0 [] p0) /\
  (!lv dfg cfg fn lbl halt np bl xs p0 j ops p inst rest step_ops q.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 j ops p /\
    DROP j xs = inst::rest /\
    generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv lbl bl
       else live_vars_at lv lbl (j+np+1)) halt
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      lbl p = SOME (step_ops,q) ==>
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 (SUC j) (ops ++ step_ops) q)
End

Theorem native_inst_ops_prefix_zero:
  native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 0 ops q <=>
    ops = [] /\ q = p0
Proof
  simp[Once native_inst_ops_prefix_cases] >> metis_tac[]
QED

Theorem native_inst_ops_prefix_suc:
  native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 (SUC j) ops q <=>
  ?pre p inst rest step_ops.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 j pre p /\
    DROP j xs = inst::rest /\
    generate_inst_plan lv dfg cfg fn inst
      (if rest = [] then live_vars_at lv lbl bl
       else live_vars_at lv lbl (j+np+1)) halt
      (case rest of [] => F | h::t => is_terminator h.inst_opcode)
      lbl p = SOME (step_ops,q) /\ ops = pre ++ step_ops
Proof
  simp[Once native_inst_ops_prefix_cases] >> metis_tac[]
QED

Theorem native_inst_ops_prefix_erase:
  !lv dfg cfg fn lbl halt np bl xs p0 k ops q.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops q ==>
    native_inst_prefix lv dfg cfg fn lbl halt np bl xs p0 k q
Proof
  ho_match_mp_tac native_inst_ops_prefix_ind >>
  metis_tac[native_inst_prefix_rules]
QED

Theorem native_inst_prefix_ops:
  !lv dfg cfg fn lbl halt np bl xs p0 k q.
    native_inst_prefix lv dfg cfg fn lbl halt np bl xs p0 k q <=>
    ?ops. native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops q
Proof
  reverse (rpt gen_tac >> eq_tac)
  >- metis_tac[native_inst_ops_prefix_erase] >>
  map_every qid_spec_tac [`q`,`k`,`p0`,`xs`,`bl`,`np`,`halt`,`lbl`,`fn`,`cfg`,`dfg`,`lv`] >>
  ho_match_mp_tac native_inst_prefix_ind >>
  metis_tac[native_inst_ops_prefix_rules]
QED

Theorem native_inst_ops_prefix_exec:
  !k lv dfg cfg fn lbl halt np bl xs p0 ops q.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops q <=>
    fnPlanLineagePrefix$generate_block_insts_prefix
      lv dfg cfg fn lbl halt np bl 0 k xs p0 = SOME (ops,q)
Proof
  Induct_on `k`
  >- (simp[native_inst_ops_prefix_zero,
           fnPlanLineagePrefixTheory.generate_block_insts_prefix_def] >>
      metis_tac[]) >>
  simp[native_inst_ops_prefix_suc,
       fnPlanLineagePrefixTheory.generate_block_insts_prefix_suc]
QED

Theorem native_inst_ops_prefix_split:
  !k xs lv dfg cfg fn lbl halt np bl p0 ops q.
    k <= LENGTH xs ==>
    (generate_block_insts_plan lv dfg cfg fn lbl halt np bl 0 xs p0 =
       SOME (ops,q) <=>
     ?pre mid post.
       native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k pre mid /\
       generate_block_insts_plan lv dfg cfg fn lbl halt np bl k
         (DROP k xs) mid = SOME (post,q) /\ ops = pre ++ post)
Proof
  rpt strip_tac >> rewrite_tac[native_inst_ops_prefix_exec] >>
  irule (SRULE [] (Q.INST [`i` |-> `0`]
    (SPEC_ALL fnPlanLineagePrefixTheory.generate_block_insts_plan_split))) >>
  simp[]
QED

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

(* Capacity audit: the out-of-range bulk-swap branch grows a short stack.
   This is reduced-branch evidence, not a counterexample to a ready run. *)
Theorem short_bulk_swap_capacity_probe:
  !ps. LENGTH (SND (do_swap 17 (ps with ps_stack := [Var "x"]))).ps_stack = 18
Proof
  gen_tac >> simp[stackPlanOpsTheory.do_swap_def] >>
  pairarg_tac >> simp[]
QED

Theorem short_reorder_capacity_probe:
  !dfg ps.
    SND (reorder_one dfg (REPLICATE 18 (Var "x")) 0 (Var "x")
      (ps with ps_stack := [Var "x"])) =
    SND (do_swap 17 (ps with ps_stack := [Var "x"]))
Proof
  simp[stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def, stackModelTheory.stack_peek_def,
       stackModelTheory.stack_find_def] >>
  simp[Q.SPEC `0` stackPlanOpsTheory.do_swap_def] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

(* Out-of-range reads are deliberately left as the unspecified operand HD []. *)
Theorem short_bulk_swap_stack_probe:
  !ps. (SND (do_swap 17 (ps with ps_stack := [Var "x"]))).ps_stack =
    [EL 16 ([] : operand list); HD []; EL 1 []; EL 2 []; EL 3 [];
     EL 4 []; EL 5 []; EL 6 []; EL 7 []; EL 8 []; EL 9 []; EL 10 [];
     EL 11 []; EL 12 []; EL 13 []; EL 14 []; EL 15 []; Var "x"]
Proof
  gen_tac >> simp[stackPlanOpsTheory.do_swap_def] >>
  pairarg_tac >> gvs[] >> EVAL_TAC
QED

Theorem repeated18_reorder_one_probe[local]:
  !dfg ps i.
    ps.ps_stack = REPLICATE 18 (Var "x") /\
    MEM i [0;1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17] ==>
    reorder_one dfg (REPLICATE 18 (Var "x")) i (Var "x") ps = ([], ps)
Proof
  rpt gen_tac >> Cases_on `ps` >> simp_tac pure_ss [MEM] >> strip_tac >> gvs[] >>
  simp[stackPlanOpsTheory.reorder_one_def,
       stackModelTheory.stack_get_unfixed_depth_def,
       stackModelTheory.stack_get_depth_def, stackModelTheory.stack_find_def,
       stackModelTheory.stack_peek_def, dfgDefsTheory.operand_equiv_def,
       stackModelTheory.stack_poke_def] >> EVAL_TAC >>
  simp[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem repeated18_reorder_plan_probe:
  !dfg ps.
    reorder_plan dfg (REPLICATE 18 (Var "x"))
      (ps with ps_stack := REPLICATE 18 (Var "x")) =
    ([], ps with ps_stack := REPLICATE 18 (Var "x"))
Proof
  rpt gen_tac >>
  rewrite_tac[stackPlanOpsTheory.reorder_plan_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV EVAL)) >>
  simp[repeated18_reorder_one_probe]
QED

Theorem short_bulk_swap_homogeneous_probe[local]:
  !ps.
    HD ([] : operand list) = Var "x" /\
    (!i. 0 < i /\ i < 17 ==> EL i ([] : operand list) = Var "x") ==>
    (SND (do_swap 17 (ps with ps_stack := [Var "x"]))).ps_stack =
      REPLICATE 18 (Var "x")
Proof
  rpt strip_tac >> simp[short_bulk_swap_stack_probe] >> EVAL_TAC
QED

(* Conditional reduced-state diagnostic only: no claim that these unspecified
   reads equal x, nor that this state occurs in a ready function. *)
Theorem short_full_reorder_homogeneous_probe:
  !dfg ps.
    HD ([] : operand list) = Var "x" /\
    (!i. 0 < i /\ i < 17 ==> EL i ([] : operand list) = Var "x") ==>
    (SND (reorder_plan dfg (REPLICATE 18 (Var "x"))
      (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>))).ps_stack =
      REPLICATE 18 (Var "x")
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stackPlanOpsTheory.reorder_plan_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (RAND_CONV EVAL)))) >>
  pure_once_rewrite_tac[FOLDL] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >> simp_tac (srw_ss()) [] >>
  `ps'.ps_stack = REPLICATE 18 (Var "x")` by
    (qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
     simp[short_reorder_capacity_probe] >> strip_tac >> gvs[] >>
     qspec_then `ps with ps_spilled := FEMPTY` mp_tac
       short_bulk_swap_homogeneous_probe >> simp[]) >>
  simp[repeated18_reorder_one_probe]
QED

Theorem short_full_reorder_conditional_guard_probe:
  !dfg ps qs.
    HD ([] : operand list) = Var "x" /\
    (!i. 0 < i /\ i < 17 ==> EL i ([] : operand list) = Var "x") /\
    qs = SND (reorder_plan dfg (REPLICATE 18 (Var "x"))
      (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>)) ==>
    stack_pop 18 qs.ps_stack ++ REPLICATE 18 (Var "x") = qs.ps_stack /\
    LIST_ELEM_COUNT (Var "x") qs.ps_stack = 18
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all short_full_reorder_homogeneous_probe >> strip_tac >>
  simp[] >> EVAL_TAC
QED

Theorem short_full_reorder_count_probe[local]:
  !dfg ps qs.
    qs = SND (reorder_plan dfg (REPLICATE 18 (Var "x"))
      (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>)) ==>
    LIST_ELEM_COUNT (Var "x") qs.ps_stack <=
    LIST_ELEM_COUNT (Var "x")
      (SND (do_swap 17 (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>))).ps_stack
Proof
  rpt gen_tac >> rewrite_tac[reorderSimTheory.reorder_plan_eq_plan_steps] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV (RATOR_CONV (RAND_CONV EVAL))))) >>
  pure_once_rewrite_tac[foldlSimTheory.plan_steps_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  pure_rewrite_tac[LET_THM] >> pairarg_tac >>
  pure_asm_rewrite_tac[] >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qmatch_goalsub_abbrev_tac `plan_steps f items ps1` >>
  Cases_on `plan_steps f items ps1` >> simp_tac (srw_ss()) [] >>
  strip_tac >> gvs[] >>
  `ps1 = SND (do_swap 17
     (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>))` by
    (qpat_x_assum `reorder_one _ _ _ _ _ = _`
      (mp_tac o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
     simp[short_reorder_capacity_probe]) >>
  `LENGTH ps1.ps_stack = 18 /\ ps1.ps_spilled = FEMPTY` by
    (gvs[] >>
     qspec_then `ps with ps_spilled := FEMPTY` mp_tac short_bulk_swap_stack_probe >>
     simp[reorderSimTheory.do_swap_spilled_unchanged]) >>
  gvs[Abbr `f`] >>
  drule_at (Pos last) fnPlanLineageInventoryTheory.plan_steps_reorder_resource_nonincrease >>
  simp[Abbr `items`] >> disch_then (qspec_then `Var "x"` mp_tac) >>
  simp[] >> strip_tac >> Cases_on `Var "x" IN FDOM qs.ps_spilled` >> gvs[]
QED

Theorem elem_count_full_length_iff:
  !xs x. LENGTH xs <= LIST_ELEM_COUNT x xs <=> EVERY (\y. y = x) xs
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt gen_tac >>
  Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM] >>
  `LIST_ELEM_COUNT x xs <= LENGTH xs` by
    simp[LIST_ELEM_COUNT_DEF, LENGTH_FILTER_LEQ] >> decide_tac
QED

Theorem short_full_reorder_guard_iff:
  !dfg ps qs.
    qs = SND (reorder_plan dfg (REPLICATE 18 (Var "x"))
      (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>)) ==>
    (stack_pop 18 qs.ps_stack ++ REPLICATE 18 (Var "x") = qs.ps_stack <=>
     HD ([] : operand list) = Var "x" /\
     (!i. 0 < i /\ i < 17 ==> EL i ([] : operand list) = Var "x"))
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- (strip_tac >>
      `LIST_ELEM_COUNT (Var "x") (REPLICATE 18 (Var "x")) = 18` by EVAL_TAC >>
      `18 <= LIST_ELEM_COUNT (Var "x") qs.ps_stack` by
        (qpat_x_assum `stack_pop _ _ ++ _ = _`
          (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var "x")``) >>
         simp[reorderSimTheory.elem_count_append]) >>
      drule short_full_reorder_count_probe >> strip_tac >>
      `EVERY (\y. y = Var "x")
        (SND (do_swap 17
          (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>))).ps_stack` by
        (rewrite_tac[GSYM elem_count_full_length_iff] >>
         qspec_then `ps with ps_spilled := FEMPTY` mp_tac short_bulk_swap_capacity_probe >>
         simp[] >> strip_tac >> decide_tac) >>
      qspec_then `ps with ps_spilled := FEMPTY` mp_tac short_bulk_swap_stack_probe >>
      strip_tac >> gvs[] >>
      `EVERY (\y. y = Var "x")
         (GENLIST (\i. EL i ([] : operand list)) 17)` by
        (CONV_TAC (RAND_CONV EVAL) >> simp[]) >>
      gvs[EVERY_GENLIST]) >>
  strip_tac >> drule_all short_full_reorder_conditional_guard_probe >> simp[]
QED

(* Live names have no resources in the residual prefix. Native targets may
   repeat: membership alone suffices for the truncated-subtraction bound. *)
Theorem generate_inst_plan_jmp_live_residual_zero:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) /\
    set (MAP Var next) SUBSET set targets /\
    (!v. MEM v next ==> LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) ==>
    !v. MEM v next ==>
      LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH targets) qs.ps_stack) = 0
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `MEM (Var v) targets` by
    (gvs[pred_setTheory.SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  `0 < LIST_ELEM_COUNT (Var v) targets` by
    gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  drule_all fnPlanLineageInventoryTheory.generate_inst_plan_jmp_residual_count >>
  disch_then (qspec_then `Var v` mp_tac) >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >> decide_tac
QED

Theorem generate_inst_plan_jmp_live_target_count:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) /\
    set (MAP Var next) SUBSET set targets /\
    (!v. MEM v next ==> LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) ==>
    !v. MEM v next ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack = LIST_ELEM_COUNT (Var v) targets
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  drule_all generate_inst_plan_jmp_live_residual_zero >> strip_tac >>
  drule_all generate_inst_plan_jmp_suffix >> strip_tac >>
  gvs[stackModelTheory.stack_pop_def, TAKE_APPEND,
      reorderSimTheory.elem_count_append]
QED

Theorem generate_inst_plan_jmp_live_terminal:
  !lv dfg cfg fn inst next halt term cur ps targets ops qs.
    inst.inst_opcode = JMP /\ inst.inst_outputs = [] /\
    join_target_ops lv fn cur inst = SOME targets /\
    generate_inst_plan lv dfg cfg fn inst next halt term cur ps = SOME (ops,qs) /\
    set (MAP Var next) SUBSET set targets /\
    (!v. MEM v next ==> LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) ==>
    qs.ps_spilled = FEMPTY /\
    (!v. MEM v next ==>
      LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH targets) qs.ps_stack) = 0) /\
    (!v. MEM v next ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack = LIST_ELEM_COUNT (Var v) targets)
Proof
  metis_tac[generate_inst_plan_jmp_live_residual_zero,
    generate_inst_plan_jmp_live_target_count,
    fnPlanLineageInventoryTheory.generate_inst_plan_jmp_spilled_empty]
QED

(* Demand transport needs a reachable instruction position. This is not an
   arbitrary-block initialization or an all-operands residual budget. *)
Theorem entry_jmp_live_terminal:
  !fn bb i ps dfg cfg halt term targets ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = JMP /\
    (EL i bb.bb_instructions).inst_outputs = [] /\
    entry_boundary_resources fn bb i ps /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (EL i bb.bb_instructions) = SOME targets /\
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)))
      SUBSET set targets /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halt term bb.bb_label ps = SOME (ops,qs) ==>
    qs.ps_spilled = FEMPTY /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH targets) qs.ps_stack) = 0) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack = LIST_ELEM_COUNT (Var v) targets)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1` by
    (rpt strip_tac >>
     `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
       (irule analyzed_computed_operand_demand >> simp[]) >>
     gvs[entry_boundary_resources_def]) >>
  drule_all generate_inst_plan_jmp_live_terminal >> simp[]
QED

(* Exact incoming-resource transport, not incoming-resource initialization. *)
Theorem analyzed_single_pred_cleanup_resource:
  !fn lbl bb ps ops qs v.
    codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\
    MEM v (live_vars_at (liveness_analyze fn) lbl 0) /\
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb ps = (ops,qs) ==>
    LIST_ELEM_COUNT (Var v) qs.ps_stack +
      (if Var v IN FDOM qs.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `NULL (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >> simp[]) >>
  `?pred. cfg_preds_of (cfg_analyze fn) lbl = [pred]` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    simp[livenessDefsTheory.input_vars_from_def] >>
  drule fnPlanLineageInventoryTheory.clean_stack_plan_spilled_unchanged >> strip_tac >>
  simp[] >> irule fnPlanLineageInventoryTheory.clean_stack_plan_input_elem_count >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`cfg_analyze fn`,`fn`,`ops`] >> simp[]
QED

Theorem analyzed_ordinary_step_available:
  !fn bb i inst dfg cfg halt term ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    ~is_param_opcode inst.inst_opcode /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halt term
      bb.bb_label ps = SOME (ops,qs) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `LENGTH (compute_operands inst) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands inst) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[analyzed_computed_operand_demand] >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      `qs = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack) ps [out]` by
        (drule_all fnPlanLineageStagesTheory.generate_offset_plan_frame >>
         disch_then (qspec_then `ps` mp_tac) >>
         gvs[generate_inst_plan_def, stackModelTheory.stack_push_def, SNOC_APPEND]) >>
      gvs[stackModelTheory.stack_push_def, SNOC_APPEND] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (gvs[generate_inst_plan_def, inst_wf_def] >> metis_tac[]) >>
  gvs[generate_inst_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> irule native_regular_live_lower >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem native_ordinary_interval_available:
  !lv dfg cfg fn label halt n len xs ps0 k ps.
    native_inst_prefix lv dfg cfg fn label halt n len xs ps0 k ps ==>
    !bb a. lv = liveness_analyze fn /\ label = bb.bb_label /\
      n = LENGTH (get_params bb.bb_instructions) + a /\
      len = LENGTH bb.bb_instructions /\ xs = DROP a (non_param_insts bb) /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      (!v. MEM v (live_vars_at lv label n) ==>
        MEM (Var v) ps0.ps_stack \/ Var v IN FDOM ps0.ps_spilled) /\
      (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI) ==>
      !v. MEM v (live_vars_at lv label (n+k)) ==>
        MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  ho_match_mp_tac native_inst_prefix_ind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `DROP (a+k) (non_param_insts bb) = inst::rest` by
    gvs[DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
  `a+k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP (a+k) _ = _`
      (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[] >> decide_tac) >>
  `inst = EL (a+k) (non_param_insts bb)` by metis_tac[HD_DROP, HD] >>
  `inst = EL (LENGTH (get_params bb.bb_instructions)+(a+k)) bb.bb_instructions` by
    metis_tac[ready_block_suffix_index] >>
  `LENGTH (get_params bb.bb_instructions)+(a+k) < LENGTH bb.bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `~is_param_opcode inst.inst_opcode` by
    (`MEM inst (non_param_insts bb)` by metis_tac[EL_MEM] >> gvs[non_param_insts_def, MEM_FILTER]) >>
  `EL k (DROP a (non_param_insts bb)) = inst` by
    (`k < LENGTH (DROP a (non_param_insts bb))` by simp[] >>
     metis_tac[HD_DROP, HD]) >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >>
     pure_asm_rewrite_tac[] >> simp[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
       (LENGTH (get_params bb.bb_instructions)+(a+k))) ==>
       MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (first_x_assum (qspecl_then [`bb`,`a`] mp_tac) >>
     asm_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  `(if rest = [] then live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label
       (k + (LENGTH (get_params bb.bb_instructions)+a) + 1)) =
     live_vars_at (liveness_analyze fn) bb.bb_label
       (SUC (LENGTH (get_params bb.bb_instructions)+(a+k)))` by
    (`k + (LENGTH (get_params bb.bb_instructions)+a) + 1 =
        (a+k) + LENGTH (get_params bb.bb_instructions) + 1` by decide_tac >>
     pop_assum (fn th => pure_rewrite_tac[th]) >>
     irule ready_block_suffix_next_live >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  rule_assum_tac (SIMP_RULE bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `_ = live_vars_at _ _ (SUC _)`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  rpt strip_tac >> irule analyzed_ordinary_step_available >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  asm_simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM,
    arithmeticTheory.ADD_CLAUSES] >>
  qpat_x_assum `MEM v (live_vars_at _ _ _)` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem analyzed_live_coverage_computed_operands:
  !fn bb i ps.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    !v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  metis_tac[analyzed_computed_operand_demand]
QED

Theorem native_inst_ops_prefix_complete:
  !lv dfg cfg fn lbl halt np bl xs p0 ops q.
    native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 (LENGTH xs) ops q <=>
    generate_block_insts_plan lv dfg cfg fn lbl halt np bl 0 xs p0 = SOME (ops,q)
Proof
  rpt gen_tac >>
  qspecl_then [`LENGTH xs`,`xs`] mp_tac native_inst_ops_prefix_split >>
  simp[generate_block_insts_plan_def] >> metis_tac[]
QED

Theorem generate_block_insts_plan_index_sum:
  !rest lv dfg cfg fn label halt n len i n' i' ps.
    n + i = n' + i' ==>
    generate_block_insts_plan lv dfg cfg fn label halt n len i rest ps =
    generate_block_insts_plan lv dfg cfg fn label halt n' len i' rest ps
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[generate_block_insts_plan_def] >>
  `i + n + 1 = i' + n' + 1` by decide_tac >>
  `!ps. generate_block_insts_plan lv dfg cfg fn label halt n len (i+1) rest ps =
    generate_block_insts_plan lv dfg cfg fn label halt n' len (i'+1) rest ps` by
    (gen_tac >> first_x_assum irule >> decide_tac) >>
  simp[generate_block_insts_plan_def]
QED

(* Factor the actual worker, retaining its full-tail lookahead. *)
Theorem native_worker_prefix_split:
  !j rest lv dfg cfg fn label halt n len i ps ops after xs ps0.
    j <= LENGTH rest /\ DROP i xs = rest /\
    native_inst_prefix lv dfg cfg fn label halt n len xs ps0 i ps /\
    generate_block_insts_plan lv dfg cfg fn label halt n len i rest ps =
      SOME (ops,after) ==>
    ?mid suffix_ops.
      native_inst_prefix lv dfg cfg fn label halt n len xs ps0 (i+j) mid /\
      generate_block_insts_plan lv dfg cfg fn label halt n len (i+j)
        (DROP (i+j) xs) mid = SOME (suffix_ops,after)
Proof
  Induct >- (rpt strip_tac >> qexistsl_tac [`ps`,`ops`] >> simp[]) >>
  Cases_on `rest` >- simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >>
  `DROP (i+1) xs = t` by
    (`DROP (i+1) xs = DROP 1 (DROP i xs)` by simp[DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
     pop_assum SUBST1_TAC >> asm_rewrite_tac[] >> simp[]) >>
  `native_inst_prefix lv dfg cfg fn label halt n len xs ps0 (i+1) ps'` by
    (`i+1 = SUC i` by simp[] >> pop_assum SUBST1_TAC >>
     irule (cj 2 native_inst_prefix_rules) >> goal_assum (drule_at Any) >>
     qexistsl_tac [`h`,`step_ops`,`t`] >> simp[]) >>
  `i + SUC j = (i+1)+j` by simp[] >> pop_assum SUBST1_TAC >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (qpat_x_assum `DROP (i+1) xs = t`
        (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  qexistsl_tac [`rest_ops`,`ps'`] >> simp[]
QED

Theorem native_worker_prefix_boundary:
  !lv dfg cfg fn label halt n len xs ps ops after k.
    generate_block_insts_plan lv dfg cfg fn label halt n len 0 xs ps =
      SOME (ops,after) /\ k <= LENGTH xs ==>
    ?mid suffix_ops.
      native_inst_prefix lv dfg cfg fn label halt n len xs ps k mid /\
      generate_block_insts_plan lv dfg cfg fn label halt n len k
        (DROP k xs) mid = SOME (suffix_ops,after)
Proof
  rpt strip_tac >>
  drule_at (Pos last) native_worker_prefix_split >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[native_inst_prefix_zero]
QED

Theorem native_worker_prefix_endpoint:
  !lv dfg cfg fn label halt n len xs ps ops after.
    generate_block_insts_plan lv dfg cfg fn label halt n len 0 xs ps =
      SOME (ops,after) ==>
    native_inst_prefix lv dfg cfg fn label halt n len xs ps (LENGTH xs) after
Proof
  rpt strip_tac >> drule native_worker_prefix_boundary >>
  disch_then (qspec_then `LENGTH xs` mp_tac) >>
  simp[generate_block_insts_plan_def] >> metis_tac[]
QED

Theorem native_worker_terminal_prefix:
  !rest lv dfg cfg fn label halt n len k ps ops qs xs ps0.
    rest <> [] /\ DROP k xs = rest /\ k + LENGTH rest = LENGTH xs /\
    native_inst_prefix lv dfg cfg fn label halt n len xs ps0 k ps /\
    generate_block_insts_plan lv dfg cfg fn label halt n len k rest ps =
      SOME (ops,qs) ==>
    ?before chunk.
      native_inst_prefix lv dfg cfg fn label halt n len xs ps0
        (PRE (LENGTH xs)) before /\
      generate_inst_plan lv dfg cfg fn (LAST xs) (live_vars_at lv label len)
        halt F label before = SOME (chunk,qs)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `rest`
  >- (gvs[generate_block_insts_plan_def] >>
      `k = PRE (LENGTH xs)` by decide_tac >>
      `LAST xs = h` by
        (`xs = TAKE k xs ++ [h]` by metis_tac[TAKE_DROP] >>
         pop_assum (fn th => once_rewrite_tac[th]) >> simp[LAST_APPEND]) >> gvs[AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
  gvs[] >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`k+1`, `rest_ops`, `ps'`] >> simp[] >>
  conj_tac
  >- (`DROP (k+1) xs = DROP 1 (DROP k xs)` by simp[DROP_DROP] >> simp[]) >>
  `k+1 = SUC k` by decide_tac >> pop_assum SUBST1_TAC >>
  irule (cj 2 native_inst_prefix_rules) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`h`, `step_ops`, `h'::t`] >> simp[GSYM arithmeticTheory.ADD_ASSOC]

QED

Theorem ready_entry_static_boundary:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = [] /\
    collect_phis (HD fn.fn_blocks).bb_instructions = [] /\
    bb_well_formed (HD fn.fn_blocks) /\
    fn_reachable fn (HD fn.fn_blocks).bb_label
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[NULL_EQ]) >>
  conj_tac
  >- (gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[NULL_EQ]) >>
  conj_tac
  >- (gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def] >>
      Cases_on `fn.fn_blocks` >> gvs[NULL_EQ]) >>
  conj_tac >- metis_tac[codegen_ready_fn_def, wf_function_def] >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_reachable_def, fn_entry_label_def, entry_block_def] >>
  metis_tac[relationTheory.RTC_REFL]
QED

Theorem well_formed_no_collected_phi:
  !bb i. bb_well_formed bb /\ collect_phis bb.bb_instructions = [] /\
    i < LENGTH bb.bb_instructions ==>
    (EL i bb.bb_instructions).inst_opcode <> PHI
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  `h.inst_opcode <> PHI` by (gvs[livenessDefsTheory.collect_phis_def, AllCaseEqs()]) >>
  Cases_on `i` >- simp[] >>
  gvs[bb_well_formed_def] >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

(* Initialization uses the real spill base, even when parameter cleanup
   performs deep swaps and advances the allocator. *)
Theorem prepare_params_structural_budget:
  !lv fn ps spillbase.
    ps.ps_stack = [] /\ ps.ps_spilled = FEMPTY /\
    residual_budget_wf spillbase [] ps /\
    ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions)) ==>
    residual_budget_wf spillbase [] (SND (prepare_params_plan lv fn ps))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `get_params (HD fn.fn_blocks).bb_instructions = []`
  >- simp[prepare_params_plan_def] >>
  `residual_budget_wf spillbase []
    (ps with ps_stack := MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    (irule reorderSimTheory.residual_budget_wf_canonical >>
     gvs[reorderSimTheory.residual_budget_wf_def,
       planSpillBoundsTheory.plan_slots_bounded_def] >>
     `MAP (\inst. Var (HD inst.inst_outputs))
        (get_params (HD fn.fn_blocks).bb_instructions) =
      MAP Var (MAP (\inst. HD inst.inst_outputs)
        (get_params (HD fn.fn_blocks).bb_instructions))` by
        simp[MAP_MAP_o, combinTheory.o_DEF] >>
     pop_assum SUBST1_TAC >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  simp[prepare_params_plan_def, parameter_push_fold] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _`
    (mp_tac o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
  simp[] >> disch_then (SUBST1_TAC o SYM) >>
  irule residual_budget_wf_optimistic_swap_plan >>
  qpat_x_assum `popmany_plan _ _ = _`
    (assume_tac o GSYM o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
  drule_at (Pat `_ = SND (popmany_plan _ _)`) popmany_plan_core_resource >>
  disch_then (qspecl_then [`[]`, `MAP (\inst. Var (HD inst.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions)`, `spillbase`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem initialized_entry_structural_budget:
  !fn ch growth spill_base lbl_ctr ps.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) ==>
    (?core. lineage_core 0 core ps /\
      residual_budget_wf spill_base [] (ps with ps_stack := core))
Proof
  rpt gen_tac >> strip_tac >>
  `residual_budget_wf spill_base [] ps` by
    (gvs[] >> irule prepare_params_structural_budget >>
     simp[fnPlanLineageInventoryTheory.init_cleanup_residual_budget] >>
     simp[init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
     irule ready_parameter_names_distinct >> simp[]) >>
  drule_all native_parameter_lineage_inventory >>
  disch_then (qspecl_then [`ch`, `growth`, `spill_base`, `lbl_ctr`] mp_tac) >>
  simp[fnPlanLineageInventoryTheory.lineage_inventory_def] >> strip_tac >>
  qexists_tac `ps.ps_stack` >>
  simp[fnPlanLineageInventoryTheory.lineage_core_def] >>
  gvs[fnPlanLineageInventoryTheory.lineage_core_def]
QED

Theorem prefix_inventory_demand_available:
  !fn bb i ps v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    prefix_inventory_origins bb i ps /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    fnPlanLineageDemandSupport$demand_available fn bb i v
Proof
  rpt gen_tac >> strip_tac >>
  `?j. j < i /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs` by
    metis_tac[prefix_inventory_origins_def] >>
  irule fnPlanLineageDemandSupportTheory.demand_available_mono >>
  qexists_tac `SUC j` >> simp[] >>
  irule fnPlanLineageDemandSupportTheory.current_output_demand_available_suc >>
  simp[] >> gvs[codegen_ready_fn_def]
QED

Theorem entry_inst_structural_step:
  !fn bb i ps dfg cfg halting term ops qs m core spillbase.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    ~is_param_opcode (EL i bb.bb_instructions).inst_opcode /\
    entry_boundary_resources fn bb i ps /\ lineage_core m core ps /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))
      halting term bb.bb_label ps = SOME (ops,qs) ==>
    ?rest. lineage_core m rest qs /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
    fnPlanLineageDemandSupport$demand_available fn bb i v` by
    metis_tac[entry_boundary_resources_def, prefix_inventory_demand_available] >>
  `ps.ps_stack = REPLICATE m dead_stack_marker ++ core` by
    gvs[fnPlanLineageInventoryTheory.lineage_core_def] >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
  gvs[]
  >- (drule_at (Pat `generate_offset_plan _ _ = _`) offset_position_invariant >>
      disch_then (qspecl_then [`fn`, `m`, `core`, `spillbase`] mp_tac) >>
      simp[] >> (impl_tac >- (gvs[entry_boundary_resources_def] >> metis_tac[])) >> simp[])
  >- (qexists_tac `core` >> simp[]) >>
  `EVERY (\x. x <> dead_stack_marker)
      (compute_operands (EL i bb.bb_instructions))` by
    (`codegen_ready_inst (EL i bb.bb_instructions)` by
       (gvs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
     gvs[codegen_ready_inst_def, EVERY_MEM, compute_operands_def,
       asmIRTheory.get_non_label_operands_def] >>
     rpt strip_tac >>
     Cases_on `(EL i bb.bb_instructions).inst_opcode = DJMP \/
       (EL i bb.bb_instructions).inst_opcode = JNZ \/
       (EL i bb.bb_instructions).inst_opcode = INVOKE`
     >- gvs[MEM_FILTER] >>
     Cases_on `(EL i bb.bb_instructions).inst_opcode = LOG` >>
     gvs[] >> metis_tac[MEM_TL]) >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    ordinary_position_invariant >>
  disch_then (qspecl_then [`m`, `core`, `spillbase`] mp_tac) >>
  simp[] >> (impl_tac >- (gvs[entry_boundary_resources_def] >> metis_tac[])) >> simp[]
QED

Theorem native_inst_prefix_structural:
  !lv dfg cfg fn label halting n len xs ps0 k ps.
    native_inst_prefix lv dfg cfg fn label halting n len xs ps0 k ps ==>
    !bb spillbase. lv = liveness_analyze fn /\ label = bb.bb_label /\
      n = LENGTH (get_params bb.bb_instructions) /\
      len = LENGTH bb.bb_instructions /\ xs = non_param_insts bb /\
      codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      entry_boundary_resources fn bb n ps0 /\
      (?m core. lineage_core m core ps0 /\
        residual_budget_wf spillbase [] (ps0 with ps_stack := core)) /\
      (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\
                       (EL j xs).inst_opcode <> PHI) ==>
      ?m core. lineage_core m core ps /\
        residual_budget_wf spillbase [] (ps with ps_stack := core)
Proof
  ho_match_mp_tac native_inst_prefix_strongind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k (non_param_insts bb)` by
    metis_tac[listTheory.HD_DROP, listTheory.HD] >>
  `inst = EL (LENGTH (get_params bb.bb_instructions) + k) bb.bb_instructions` by
    metis_tac[ready_block_suffix_index] >>
  `?m core. lineage_core m core ps /\
    residual_budget_wf spillbase [] (ps with ps_stack := core)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `entry_boundary_resources fn bb (LENGTH (get_params bb.bb_instructions)+k) ps` by
    (drule native_inst_prefix_resources >> disch_then irule >> simp[] >> metis_tac[]) >>
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
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> PHI` by
    (qpat_x_assum `!j. j < SUC k ==> _` (qspec_then `k` mp_tac) >>
     simp_tac (srw_ss()) [] >> metis_tac[]) >>
  qexists_tac `m'` >> irule entry_inst_structural_step >>
  rpt (goal_assum (drule_at Any)) >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED

Theorem initialized_entry_prefix_structural:
  !fn dfg ch growth spill_base lbl_ctr k ps.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
      (LENGTH (HD fn.fn_blocks).bb_instructions)
      (non_param_insts (HD fn.fn_blocks))
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr))) k ps /\
    (!j. j < k ==> (EL j (non_param_insts (HD fn.fn_blocks))).inst_opcode <> JMP /\
      (EL j (non_param_insts (HD fn.fn_blocks))).inst_opcode <> PHI) ==>
    entry_boundary_resources fn (HD fn.fn_blocks)
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)+k) ps /\
    ?m core. lineage_core m core ps /\
      residual_budget_wf spill_base [] (ps with ps_stack := core)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  `entry_boundary_resources fn (HD fn.fn_blocks)
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
    (SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)))` by
    (irule initialized_entry_boundary_resources >>
     metis_tac[]) >>
  conj_tac
  >- (drule native_inst_prefix_resources >> disch_then irule >> simp[]) >>
  drule native_inst_prefix_structural >> disch_then irule >> simp[] >>
  conj_tac
  >- metis_tac[initialized_entry_structural_budget] >>
  qexists_tac `HD fn.fn_blocks` >> simp[]
QED

Theorem initialized_entry_preterminal:
  !fn dfg ch growth spill_base lbl_ctr ops qs.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) ==>
    ?before chunk.
      entry_boundary_resources fn (HD fn.fn_blocks)
        (PRE (LENGTH (HD fn.fn_blocks).bb_instructions)) before /\
      (?m core. lineage_core m core before /\
        residual_budget_wf spill_base [] (before with ps_stack := core)) /\
      generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (LAST (HD fn.fn_blocks).bb_instructions)
        (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
          (LENGTH (HD fn.fn_blocks).bb_instructions))
        (bb_is_halting (HD fn.fn_blocks)) F (HD fn.fn_blocks).bb_label before =
        SOME (chunk,qs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> gvs[] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `non_param_insts (HD fn.fn_blocks) <> []` by
    (`MEM (LAST (HD fn.fn_blocks).bb_instructions)
        (non_param_insts (HD fn.fn_blocks))` suffices_by metis_tac[MEM] >>
     `~is_param_opcode (LAST (HD fn.fn_blocks).bb_instructions).inst_opcode` by
       (gvs[bb_well_formed_def] >>
        Cases_on `(LAST (HD fn.fn_blocks).bb_instructions).inst_opcode` >>
        gvs[is_terminator_def, is_param_opcode_def]) >>
     simp[non_param_insts_def, MEM_FILTER] >>
     `(HD fn.fn_blocks).bb_instructions <> []` by metis_tac[bb_well_formed_def] >>
     Cases_on `(HD fn.fn_blocks).bb_instructions` >> gvs[MEM_LAST]) >>
  `?before chunk.
     native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn
       (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
       (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
       (LENGTH (HD fn.fn_blocks).bb_instructions)
       (non_param_insts (HD fn.fn_blocks)) ps1
       (PRE (LENGTH (non_param_insts (HD fn.fn_blocks)))) before /\
     generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
       (LAST (non_param_insts (HD fn.fn_blocks)))
       (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
         (LENGTH (HD fn.fn_blocks).bb_instructions))
       (bb_is_halting (HD fn.fn_blocks)) F (HD fn.fn_blocks).bb_label before =
       SOME (chunk,qs)` by
    (irule native_worker_terminal_prefix >>
     goal_assum (drule_at Any) >> simp[native_inst_prefix_zero]) >>
  drule_all ready_block_parameter_suffix >> disch_tac >>
  `LENGTH (HD fn.fn_blocks).bb_instructions =
     LENGTH (get_params (HD fn.fn_blocks).bb_instructions) +
     LENGTH (non_param_insts (HD fn.fn_blocks))` by metis_tac[LENGTH_APPEND] >>
  `LAST (HD fn.fn_blocks).bb_instructions =
     LAST (non_param_insts (HD fn.fn_blocks))` by
    (qpat_x_assum `(HD fn.fn_blocks).bb_instructions = _`
      (fn th => once_rewrite_tac[th]) >>
     Cases_on `non_param_insts (HD fn.fn_blocks)` >> gvs[LAST_APPEND]) >>
  qexistsl_tac [`before`, `chunk`] >>
  `PRE (LENGTH (HD fn.fn_blocks).bb_instructions) =
     LENGTH (get_params (HD fn.fn_blocks).bb_instructions) +
     PRE (LENGTH (non_param_insts (HD fn.fn_blocks)))` by
    (Cases_on `non_param_insts (HD fn.fn_blocks)` >> gvs[]) >>
  `!j. j < PRE (LENGTH (non_param_insts (HD fn.fn_blocks))) ==>
    (EL j (non_param_insts (HD fn.fn_blocks))).inst_opcode <> JMP /\
    (EL j (non_param_insts (HD fn.fn_blocks))).inst_opcode <> PHI` by
    (qx_gen_tac `j` >> strip_tac >>
     `j < LENGTH (non_param_insts (HD fn.fn_blocks))` by decide_tac >>
     drule_all ready_block_suffix_index >> disch_then SUBST1_TAC >>
     conj_tac
     >- (gvs[bb_well_formed_def] >>
         `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) + j <
          LENGTH (HD fn.fn_blocks).bb_instructions` by decide_tac >>
         CCONTR_TAC >> fs[] >>
         qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
           (qspec_then `j + LENGTH (get_params (HD fn.fn_blocks).bb_instructions)` mp_tac) >>
         asm_simp_tac std_ss [is_terminator_def] >> decide_tac) >>
     irule well_formed_no_collected_phi >> simp[] >> decide_tac) >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` (mp_tac o AP_TERM ``SND : stack_op list # plan_state -> plan_state``) >>
  simp[] >> disch_then (SUBST_ALL_TAC o SYM) >>
  drule_all initialized_entry_prefix_structural >> strip_tac >>
  metis_tac[]
QED

Theorem initialized_entry_jmp_residual_zero:
  !fn dfg ch growth spill_base lbl_ctr ops qs targets.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    (LAST (HD fn.fn_blocks).bb_instructions).inst_opcode = JMP /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
      SOME (ops,qs) /\
    join_target_ops (liveness_analyze fn) fn (HD fn.fn_blocks).bb_label
      (LAST (HD fn.fn_blocks).bb_instructions) = SOME targets ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
          (LENGTH (HD fn.fn_blocks).bb_instructions)) ==>
      LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH targets) qs.ps_stack) = 0
Proof
  rpt gen_tac >> strip_tac >>
  drule_all initialized_entry_preterminal >> strip_tac >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `inst_wf (LAST (HD fn.fn_blocks).bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >>
     metis_tac[LAST_MEM, bb_well_formed_def]) >>
  `?succ. (LAST (HD fn.fn_blocks).bb_instructions).inst_operands = [Label succ] /\
      (LAST (HD fn.fn_blocks).bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (HD fn.fn_blocks).bb_instructions))) SUBSET set targets` by
    (qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
     simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
     `lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks = SOME (HD fn.fn_blocks)` by
       (Cases_on `fn.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
     `cfg_reachable_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label` by
       metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze, codegen_ready_fn_def] >>
     `(HD fn.fn_blocks).bb_instructions <> []` by metis_tac[bb_well_formed_def] >>
     `set (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (HD fn.fn_blocks).bb_instructions)) =
      set (input_vars_from (HD fn.fn_blocks).bb_label target_bb.bb_instructions
        (live_vars_at (liveness_analyze fn) succ 0))` by
       (irule fnPlanLineageLivenessTheory.analyzed_live_out_jmp >> simp[]) >>
     gvs[pred_setTheory.EXTENSION, pred_setTheory.SUBSET_DEF, MEM_MAP] >> metis_tac[]) >>
  `(HD fn.fn_blocks).bb_instructions <> []` by metis_tac[bb_well_formed_def] >>
  `SUC (PRE (LENGTH (HD fn.fn_blocks).bb_instructions)) =
    LENGTH (HD fn.fn_blocks).bb_instructions` by
    (Cases_on `(HD fn.fn_blocks).bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH (HD fn.fn_blocks).bb_instructions))
     (HD fn.fn_blocks).bb_instructions = LAST (HD fn.fn_blocks).bb_instructions` by
    metis_tac[LAST_EL] >>
  drule_at (Pat `entry_boundary_resources _ _ _ _`)
    (INST_TYPE [alpha |-> ``:cfg_analysis``] entry_jmp_live_terminal) >>
  simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem analyzed_single_pred_physical_live_boundary:
  !fn pred pred_bb lbl bb after incoming.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\
    native_live_boundary fn pred_bb (LENGTH pred_bb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled ==>
    native_live_boundary fn bb 0 incoming
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\ pred_bb.bb_label = pred` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `NULL (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all fnPlanLineageLivenessTheory.analyzed_live_out_edge_subset >>
  simp[livenessDefsTheory.input_vars_from_def, pred_setTheory.SUBSET_DEF] >> disch_tac >>
  gvs[native_live_boundary_def] >> metis_tac[]
QED

Theorem analyzed_single_pred_physical_clean_live_boundary:
  !fn pred pred_bb lbl bb after incoming ops cleaned.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 /\
    native_live_boundary fn pred_bb (LENGTH pred_bb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming = (ops,cleaned) ==>
    native_live_boundary fn bb 0 cleaned
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  drule_all analyzed_single_pred_physical_live_boundary >> disch_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
    LIST_ELEM_COUNT (Var v) cleaned.ps_stack +
      (if Var v IN FDOM cleaned.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0)` by
    (rpt strip_tac >> drule_all analyzed_single_pred_cleanup_resource >> simp[]) >>
  gvs[native_live_boundary_def] >> rpt strip_tac >>
  Cases_on `Var v IN FDOM cleaned.ps_spilled` >> simp[] >>
  `LIST_ELEM_COUNT (Var v) cleaned.ps_stack =
    LIST_ELEM_COUNT (Var v) after.ps_stack +
    (if Var v IN FDOM after.ps_spilled then 1 else 0)` by
    (qpat_x_assum `!v. _ ==> _ = _` drule >> simp[]) >>
  `MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled` by metis_tac[] >>
  `0 < LIST_ELEM_COUNT (Var v) cleaned.ps_stack` by
    (Cases_on `Var v IN FDOM after.ps_spilled` >>
     gvs[] >> metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
  metis_tac[LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]
QED

Theorem native_inst_prefix_phi_member:
  !lv dfg cfg fn label halt n len xs ps k qs.
    native_inst_prefix lv dfg cfg fn label halt n len xs ps k qs ==>
    !v. MEM (Var v) ps.ps_stack /\
      (!i. i < k ==> (EL i xs).inst_opcode = PHI /\
        ~MEM (Var v) (EL i xs).inst_operands /\
        v <> HD (EL i xs).inst_outputs) ==>
      MEM (Var v) qs.ps_stack
Proof
  ho_match_mp_tac native_inst_prefix_ind >> conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `k < LENGTH xs` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[] >> decide_tac) >>
  `inst = EL k xs` by metis_tac[listTheory.HD_DROP, listTheory.HD] >>
  rename1 `generate_inst_plan _ _ _ _ _ _ _ _ _ mid = SOME (ops,final)` >>
  `MEM (Var v) mid.ps_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     `i < SUC k` by decide_tac >> metis_tac[]) >>
  qpat_x_assum `!i. i < SUC k ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[stackPlanGenTheory.generate_inst_plan_def,
      stackPlanGenTheory.is_pre_codegen_opcode_def] >>
  drule_at (Pat `generate_phi_plan _ _ _ _ = _`)
    fnPlanLineagePhiResourcesTheory.generate_phi_plan_other_elem_mem >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

(* The real unexecuted tail remains in xs, so worker liveness arguments do
   not change when selecting a prefix. Initial candidates are local inputs. *)
Theorem ready_native_phi_prefix_candidate:
  !dfg cfg fn label halt n len xs ps k qs bb tail j v.
    native_inst_prefix (liveness_analyze fn) dfg cfg fn label halt n len xs ps k qs /\
    xs = collect_phis bb.bb_instructions ++ tail /\
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
    k <= j /\ j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
    MEM (Var v) ps.ps_stack ==>
    MEM (Var v) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `phi_block_ready (liveness_analyze fn) bb` by
    metis_tac[phi_codegen_block_ready] >>
  `EVERY inst_wf bb.bb_instructions` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule native_inst_prefix_phi_member >>
  disch_then (qspec_then `v` irule) >> simp[] >>
  qx_gen_tac `i` >> strip_tac >>
  `i < j /\ i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `EL i xs = EL i (collect_phis bb.bb_instructions)` by
    simp[rich_listTheory.EL_APPEND1] >>
  `MEM (EL i (collect_phis bb.bb_instructions)) bb.bb_instructions /\
   (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[livenessProofsTheory.collect_phis_mem, listTheory.EL_MEM] >>
  `inst_wf (EL i (collect_phis bb.bb_instructions))` by
    metis_tac[listTheory.EVERY_MEM] >>
  `~MEM (Var v) (EL i (collect_phis bb.bb_instructions)).inst_operands` by
    metis_tac[fnPlanLineageLivenessTheory.ready_phi_later_operand_isolated] >>
  `v <> HD (EL i (collect_phis bb.bb_instructions)).inst_outputs` by
    (`(EL i (collect_phis bb.bb_instructions)).inst_outputs <> []` by
       (fs[venomWfTheory.inst_wf_def] >>
        Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[]) >>
     `MEM (HD (EL i (collect_phis bb.bb_instructions)).inst_outputs)
        (EL i (collect_phis bb.bb_instructions)).inst_outputs` by
       (Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[]) >>
     metis_tac[phi_prefix_output_not_operand, listTheory.EL_MEM]) >>
  gvs[]
QED

Theorem ready_native_phi_prefix_selection:
  !dfg cfg fn label halt n len xs ps k qs bb tail j v.
    native_inst_prefix (liveness_analyze fn) dfg cfg fn label halt n len xs ps k qs /\
    xs = collect_phis bb.bb_instructions ++ tail /\
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
    k <= j /\ j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
    MEM (Var v) ps.ps_stack ==>
    ?d w.
      stack_get_phi_depth
        (FILTER is_var_operand (EL j (collect_phis bb.bb_instructions)).inst_operands)
        qs.ps_stack = SOME d /\
      stack_peek d qs.ps_stack = Var w /\
      MEM (Var w) (EL j (collect_phis bb.bb_instructions)).inst_operands
Proof
  rpt strip_tac >> drule_all ready_native_phi_prefix_candidate >> strip_tac >>
  irule fnPlanLineagePhiInventoryTheory.phi_selection_from_present_operand >>
  qexists_tac `v` >> simp[]
QED

Theorem non_param_insts_phi_prefix:
  !bb. ?tail. non_param_insts bb = collect_phis bb.bb_instructions ++ tail
Proof
  gen_tac >>
  qspec_then `bb.bb_instructions` (qx_choose_then `rest` assume_tac)
    fnPlanLineageLivenessTheory.collect_phis_prefix >>
  `FILTER (\inst. ~is_param_opcode inst.inst_opcode)
      (collect_phis bb.bb_instructions) = collect_phis bb.bb_instructions` by
    (rewrite_tac[listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >>
     metis_tac[livenessTransferProofsTheory.collect_phis_mem, is_param_opcode_def]) >>
  qexists_tac `FILTER (\inst. ~is_param_opcode inst.inst_opcode) rest` >>
  pure_rewrite_tac[non_param_insts_def] >>
  metis_tac[listTheory.FILTER_APPEND_DISTRIB]
QED

Theorem generate_join_block_worker:
  bb <> HD fn.fn_blocks /\ 1 < LENGTH (cfg_preds_of cfg bb.bb_label) /\
  generate_block_plan lv dfg cfg fn bb ps = SOME (ops,qs) ==>
  ?inst_ops.
    generate_block_insts_plan lv dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps = SOME (inst_ops,qs) /\
    ops = SOLabel bb.bb_label :: inst_ops
Proof
  strip_tac >>
  gvs[generate_block_plan_def, AllCaseEqs()]
QED

Theorem incoming_join_native_phi_prefix_selection:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,ps) /\
  incoming.ps_stack = ps.ps_stack /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs /\
  k <= j /\ j < LENGTH (collect_phis bb.bb_instructions) ==>
  ?d w.
    stack_get_phi_depth
      (FILTER is_var_operand (EL j (collect_phis bb.bb_instructions)).inst_operands)
      qs.ps_stack = SOME d /\
    stack_peek d qs.ps_stack = Var w /\
    MEM (Var w) (EL j (collect_phis bb.bb_instructions)).inst_operands
Proof
  strip_tac >>
  `?v. MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
       MEM (Var v) ps.ps_stack` by
    (irule successful_join_edge_phi_candidate >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `?tail. non_param_insts bb = collect_phis bb.bb_instructions ++ tail` by
    metis_tac[non_param_insts_phi_prefix] >>
  `MEM (Var v) incoming.ps_stack` by simp[] >>
  drule_all ready_native_phi_prefix_selection >> simp[]
QED

Theorem analyzed_join_live_through_physical_seed:
  !fn pred pb lbl bb after incoming v.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    phi_block_ready (liveness_analyze fn) bb /\
    native_live_boundary fn pb (LENGTH pb.bb_instructions) after /\
    incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
    MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH (collect_phis bb.bb_instructions))) /\
    EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions) ==>
    (MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled) /\
    LIST_ELEM_COUNT (Var v) incoming.ps_stack +
      (if Var v IN FDOM incoming.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_label = lbl /\ pb.bb_label = pred` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[analyzed_ready_phi_live_through_edge] >>
  drule_all analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> disch_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))` by
    metis_tac[] >>
  metis_tac[native_live_boundary_coverage, native_live_boundary_count]
QED

(* Positive join seeds do not require chronological origins or resource counts.
   The candidate seed is already successful_join_edge_phi_candidate in
   fnPlanLineageJoinEntry; stack-identical incoming states use it unchanged. *)
Theorem successful_join_live_through_stack_seed:
  codegen_ready_fn fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  phi_block_ready (liveness_analyze fn) bb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,after) /\
  incoming.ps_stack = after.ps_stack /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions) ==>
  MEM (Var v) incoming.ps_stack
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    metis_tac[analyzed_ready_phi_live_through_edge] >>
  drule_all fnPlanLineageEdgeTheory.generate_block_plan_join_edge_suffix >>
  strip_tac >> simp[listTheory.MEM_MAP_f]
QED


Theorem incoming_join_native_phi_positive_prefix:
  !k fn entry lbl bb pred pb dfg ps0 ops after incoming qs.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,after) /\
    incoming.ps_stack = after.ps_stack /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH (collect_phis bb.bb_instructions))) /\
      EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[native_inst_prefix_zero] >> rpt strip_tac >>
      `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
        metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
      `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by
        (gvs[codegen_ready_fn_def] >>
         metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre]) >>
      `phi_block_ready (liveness_analyze fn) bb` by metis_tac[phi_codegen_block_ready] >>
      disj1_tac >> irule successful_join_live_through_stack_seed >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  rename1 `native_inst_prefix _ _ _ _ _ _ _ _ _ _ k ps'` >>
  `k <= LENGTH (collect_phis bb.bb_instructions) /\
   k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH (collect_phis bb.bb_instructions))) /\
       EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions)) ==>
       MEM (Var v) ps'.ps_stack \/ Var v IN FDOM ps'.ps_spilled` by metis_tac[] >>
  `bb.bb_label = lbl /\ MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_label, venomExecPropsTheory.lookup_block_MEM] >>
  `?dist w. stack_get_phi_depth
      (FILTER is_var_operand (EL k (collect_phis bb.bb_instructions)).inst_operands)
      ps'.ps_stack = SOME dist /\ stack_peek dist ps'.ps_stack = Var w /\
      MEM (Var w) (EL k (collect_phis bb.bb_instructions)).inst_operands` by
    (irule incoming_join_native_phi_prefix_selection >>
     (conj_tac >- simp[]) >>
     goal_assum (drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
  `inst = EL k (non_param_insts bb)` by
    (qpat_x_assum `DROP k _ = _` mp_tac >> simp[DROP_CONS_EL] >> strip_tac >> gvs[]) >>
  `inst = EL k (collect_phis bb.bb_instructions)` by metis_tac[EL_APPEND_EQN] >>
  `MEM inst (collect_phis bb.bb_instructions)` by metis_tac[EL_MEM] >>
  `inst.inst_opcode = PHI /\ MEM inst bb.bb_instructions` by
    metis_tac[livenessTransferProofsTheory.collect_phis_mem] >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `?out. inst.inst_outputs = [out]` by
    (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, GSYM LENGTH_EQ_1]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `get_params bb.bb_instructions = [] /\ non_param_insts bb = bb.bb_instructions` by
    (qspecl_then [`fn`, `lbl`, `bb`] mp_tac nonentry_block_no_params >>
     simp[] >> (impl_tac >- gvs[codegen_ready_fn_def]) >> simp[]) >>
  `k < LENGTH (non_param_insts bb)` by
    (qpat_x_assum `non_param_insts bb = _ ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  qspecl_then [`fn`, `bb`, `liveness_analyze fn`] mp_tac ready_block_suffix_next_live >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!fn entry lbl bb pred pb dfg ps0 ops after incoming qs. _` kall_tac >>
  rpt strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))` by
    (irule analyzed_phi_protected_demand >> simp[] >> metis_tac[]) >>
  `v <> out ==> EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions))` by
    (qspecl_then [`collect_phis bb.bb_instructions`, `k`, `v`] mp_tac
       phi_protected_demand_step >> simp[] >> gvs[inst_defs_def] >> metis_tac[]) >>
  `generate_phi_plan inst (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k))
     (bb_is_halting bb) ps' = (ops',qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def] >> gvs[]) >>
  irule generate_phi_plan_live_available >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem incoming_join_native_post_phi_available:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (ops,after) /\
  incoming.ps_stack = after.ps_stack /\
  native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) (non_param_insts bb) incoming
    (LENGTH (collect_phis bb.bb_instructions)) qs /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  strip_tac >> drule_at (Pat `native_inst_prefix _ _ _ _ _ _ _ _ _ _ _ _`)
    incoming_join_native_phi_positive_prefix >>
  simp[] >> metis_tac[]
QED

(* Positive singleton-edge setup: spill-only witnesses are retained too.
   No restriction is imposed on incoming cleanup height or promises. *)
Theorem analyzed_single_pred_clean_available:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  cfg_preds_of (cfg_analyze fn) lbl = [pred] /\
  EVERY (\v. MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled)
    (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) /\
  incoming.ps_stack = after.ps_stack /\ incoming.ps_spilled = after.ps_spilled /\
  clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming = (ops,cleaned) ==>
  EVERY (\v. MEM (Var v) cleaned.ps_stack \/ Var v IN FDOM cleaned.ps_spilled)
    (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `NULL (collect_phis bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all analyzed_live_out_edge_subset >>
  simp[pred_setTheory.SUBSET_DEF] >> disch_tac >>
  `EVERY (\v. MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled)
    (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0))` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`)
    fnPlanLineageInventoryTheory.clean_stack_plan_input_coverage >>
  gvs[livenessDefsTheory.input_vars_from_def] >> metis_tac[]
QED

(* Shared terminal target fact, relocated from NativeTerminal to avoid a cycle. *)
Theorem native_terminal_jmp_target_set:
  !fn bb targets.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    join_target_ops (liveness_analyze fn) fn bb.bb_label
      (LAST bb.bb_instructions) = SOME targets ==>
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions))) = set targets
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `cfg_reachable_of (cfg_analyze fn) bb.bb_label` by
    metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze] >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
  simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
  `set (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) =
    set (input_vars_from bb.bb_label target_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule analyzed_live_out_jmp >> simp[]) >>
  simp[LIST_TO_SET_MAP]
QED

Theorem analyzed_terminal_jmp_live_available:
  !fn bb dfg ps ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    bb.bb_instructions <> [] /\ (LAST bb.bb_instructions).inst_opcode = JMP /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (PRE (LENGTH bb.bb_instructions))) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (LAST bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
      (bb_is_halting bb) F bb.bb_label ps = SOME (ops,qs) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `inst_wf (LAST bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[LAST_MEM]) >>
  `?succ. (LAST bb.bb_instructions).inst_operands = [Label succ] /\
    (LAST bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions /\
    PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[LAST_EL] >>
  Cases_on `join_target_ops (liveness_analyze fn) fn bb.bb_label (LAST bb.bb_instructions)`
  >- (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) jmp_no_target_state >>
      simp[] >> strip_tac >> gvs[] >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (LENGTH bb.bb_instructions)) ==>
        MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
          (PRE (LENGTH bb.bb_instructions)))` by
        (rpt strip_tac >> irule analyzed_computed_operand_demand >> simp[] >>
         disj2_tac >>
         `SUC (PRE (LENGTH bb.bb_instructions)) = LENGTH bb.bb_instructions` by decide_tac >>
         asm_rewrite_tac[]) >>
      gvs[fnPlanLineageInventoryTheory.release_dead_spills_stack,
          fnPlanLineageInventoryTheory.release_dead_spills_domain, MEM_MAP] >>
      metis_tac[]) >>
  rename1 `join_target_ops _ _ _ _ = SOME targets` >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))) = set targets` by
    (drule_at (Pat `join_target_ops _ _ _ _ = _`) native_terminal_jmp_target_set >> simp[]) >>
  drule_all generate_inst_plan_jmp_suffix >> strip_tac >>
  gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[MEM_APPEND]
QED

(* Shared structural split, relocated from ChronologicalPrefix. *)
Theorem native_inst_prefix_split:
  !k p lv dfg cfg fn lbl halt n total xs ps qs.
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps (p+k) qs ==>
    ?mid. native_inst_prefix lv dfg cfg fn lbl halt n total xs ps p mid /\
      native_inst_prefix lv dfg cfg fn lbl halt (n+p) total (DROP p xs) mid k qs
Proof
  Induct
  >- (rpt strip_tac >> qexists_tac `qs` >> fs[native_inst_prefix_zero]) >>
  rpt gen_tac >> rename1 `native_inst_prefix lv dfg cfg fn lbl halt n len xs ps _ qs` >>
  rewrite_tac[arithmeticTheory.ADD_CLAUSES] >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `?mid. native_inst_prefix lv dfg cfg fn lbl halt n len xs ps p mid /\
     native_inst_prefix lv dfg cfg fn lbl halt (n+p) len (DROP p xs) mid k ps'` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  qexists_tac `mid` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule (cj 2 native_inst_prefix_rules) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`inst`, `ops`, `rest`] >>
  `k + (n + p) + 1 = k + (n + (p + 1))` by decide_tac >>
  simp[rich_listTheory.DROP_DROP_T]
QED

Theorem native_inst_prefix_compose:
  !k p lv dfg cfg fn lbl halt n total xs ps mid qs.
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps p mid /\
    native_inst_prefix lv dfg cfg fn lbl halt (n+p) total (DROP p xs) mid k qs ==>
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps (p+k) qs
Proof
  Induct >- simp[native_inst_prefix_zero] >>
  rpt gen_tac >> rename1 `native_inst_prefix lv dfg cfg fn lbl halt n len xs ps _ _` >>
  strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) _` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  `native_inst_prefix lv dfg cfg fn lbl halt n len xs ps (p+k) ps'` by
    metis_tac[] >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  irule (cj 2 native_inst_prefix_rules) >>
  qexistsl_tac [`inst`,`ops`,`ps'`,`rest`] >>
  metis_tac[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD_ASSOC,
    arithmeticTheory.ADD_COMM]
QED

Theorem native_inst_prefix_deterministic:
  !k lv dfg cfg fn lbl halt n total xs ps qs rs.
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps k qs /\
    native_inst_prefix lv dfg cfg fn lbl halt n total xs ps k rs ==> qs = rs
Proof
  Induct >- simp[native_inst_prefix_zero] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) qs` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >>
  qpat_x_assum `native_inst_prefix _ _ _ _ _ _ _ _ _ _ (SUC _) rs` mp_tac >>
  simp[Once native_inst_prefix_cases] >> strip_tac >> gvs[] >>
  `ps' = ps''` by metis_tac[] >> gvs[]
QED

Theorem native_seeded_ordinary_prefix_available:
  !fn bb dfg a k incoming seed qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= k /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k qs /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) ==>
      MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled) /\
    (!j. a <= j /\ j < k ==>
      (EL j (non_param_insts bb)).inst_opcode <> JMP /\
      (EL j (non_param_insts bb)).inst_opcode <> PHI) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `k = a + (k-a)` by decide_tac >>
  `?mid. native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a mid /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions)+a)
      (LENGTH bb.bb_instructions) (DROP a (non_param_insts bb)) mid (k-a) qs` by
    (irule native_inst_prefix_split >> simp[]) >>
  `mid = seed` by metis_tac[native_inst_prefix_deterministic] >> gvs[] >>
  `!j. j < k-a ==>
    (EL j (DROP a (non_param_insts bb))).inst_opcode <> JMP /\
    (EL j (DROP a (non_param_insts bb))).inst_opcode <> PHI` by
    (rpt strip_tac >>
     `a+j < k /\ a <= a+j` by decide_tac >>
     `k <= LENGTH (non_param_insts bb)` by metis_tac[native_inst_prefix_bound] >>
     `j < LENGTH (DROP a (non_param_insts bb))` by (simp[] >> decide_tac) >>
     gvs[EL_DROP] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule native_ordinary_interval_available >>
  disch_then (qspecl_then [`bb`,`a`] mp_tac) >> simp[]
QED

Theorem native_seeded_worker_exit_available:
  !fn bb dfg a incoming seed ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= LENGTH (non_param_insts bb) /\
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) incoming = SOME (ops,qs) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) ==>
      MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled) /\
    (!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      (EL j (non_param_insts bb)).inst_opcode <> PHI /\
      ((EL j (non_param_insts bb)).inst_opcode = JMP ==>
        SUC j = LENGTH (non_param_insts bb))) ==>
    !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
    LENGTH (non_param_insts bb)` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming
      (LENGTH (non_param_insts bb)) qs` by metis_tac[native_worker_prefix_endpoint] >>
  Cases_on `a = LENGTH (non_param_insts bb)`
  >- (`seed = qs` by metis_tac[native_inst_prefix_deterministic] >> gvs[]) >>
  `a < LENGTH (non_param_insts bb) /\ non_param_insts bb <> []` by
    (conj_tac >- decide_tac >> CCONTR_TAC >> gvs[]) >>
  Cases_on `(LAST (non_param_insts bb)).inst_opcode = JMP`
  >- (`?before chunk.
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming
        (PRE (LENGTH (non_param_insts bb))) before /\
      generate_inst_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (LAST (non_param_insts bb))
        (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions))
        (bb_is_halting bb) F bb.bb_label before = SOME (chunk,qs)` by
      (irule native_worker_terminal_prefix >> goal_assum (drule_at Any) >>
       simp[native_inst_prefix_zero] >> metis_tac[]) >>
      `LAST bb.bb_instructions = LAST (non_param_insts bb)` by
        (drule_all ready_block_parameter_suffix >> disch_then SUBST1_TAC >>
         Cases_on `non_param_insts bb` >> gvs[LAST_APPEND]) >>
      `PRE (LENGTH bb.bb_instructions) = LENGTH (get_params bb.bb_instructions) +
        PRE (LENGTH (non_param_insts bb))` by
        (Cases_on `non_param_insts bb` >> gvs[]) >>
      `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (PRE (LENGTH bb.bb_instructions))) ==>
        MEM (Var v) before.ps_stack \/ Var v IN FDOM before.ps_spilled` by
        (asm_rewrite_tac[] >> rpt strip_tac >> irule native_seeded_ordinary_prefix_available >>
         goal_assum (drule_at Any) >> simp[] >>
         qexistsl_tac [`a`,`dfg`,`incoming`,`seed`] >> simp[] >>
         (conj_tac >- (rpt strip_tac >>
           `j < LENGTH (non_param_insts bb) /\ SUC j <> LENGTH (non_param_insts bb)` by decide_tac >>
           metis_tac[])) >> gvs[]) >>
      `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
      qpat_x_assum `LAST bb.bb_instructions = _`
        (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
      drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
        analyzed_terminal_jmp_live_available >>
      asm_simp_tac bool_ss []) >>
  `!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
    (EL j (non_param_insts bb)).inst_opcode <> JMP /\
    (EL j (non_param_insts bb)).inst_opcode <> PHI` by
    (rpt strip_tac >>
     `SUC j = LENGTH (non_param_insts bb)` by metis_tac[] >>
     `EL j (non_param_insts bb) = LAST (non_param_insts bb)` by
       (simp[LAST_EL] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >> metis_tac[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >> irule native_seeded_ordinary_prefix_available >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`a`,`dfg`,`incoming`,`seed`] >> gvs[]
QED

Theorem native_seeded_suffix_prefix_available:
  !fn bb dfg a k incoming seed ps.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= k /\ k < LENGTH (non_param_insts bb) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k ps /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) ==>
      MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled) /\
    (!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      (EL j (non_param_insts bb)).inst_opcode <> PHI /\
      ((EL j (non_param_insts bb)).inst_opcode = JMP ==>
        SUC j = LENGTH (non_param_insts bb))) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) (compute_operands
      (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `!j. a <= j /\ j < k ==>
    (EL j (non_param_insts bb)).inst_opcode <> JMP /\
    (EL j (non_param_insts bb)).inst_opcode <> PHI` by
    (rpt strip_tac >> `j < LENGTH (non_param_insts bb) /\
      SUC j <> LENGTH (non_param_insts bb)` by decide_tac >> metis_tac[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (metis_tac[native_seeded_ordinary_prefix_available]) >>
  conj_tac >- simp[] >>
  `LENGTH (get_params bb.bb_instructions)+k < LENGTH bb.bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  metis_tac[analyzed_live_coverage_computed_operands]
QED

Theorem ready_block_ordinary_suffix_layout:
  !fn bb a.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    LENGTH (collect_phis bb.bb_instructions) <=
      LENGTH (get_params bb.bb_instructions) + a ==>
    !j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      (EL j (non_param_insts bb)).inst_opcode <> PHI /\
      ((EL j (non_param_insts bb)).inst_opcode = JMP ==>
        SUC j = LENGTH (non_param_insts bb))
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by metis_tac[codegen_ready_fn_def, wf_function_def] >>
  `EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    (irule ordered_phis_ordinary_suffix >> gvs[bb_well_formed_def]) >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
      LENGTH (non_param_insts bb)` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `EL j (non_param_insts bb) =
    EL (LENGTH (get_params bb.bb_instructions)+j) bb.bb_instructions` by
    metis_tac[ready_block_suffix_index] >>
  simp[] >> conj_tac
  >- (gvs[EVERY_EL] >>
      first_x_assum (qspec_then
        `LENGTH (get_params bb.bb_instructions)+j-LENGTH (collect_phis bb.bb_instructions)` mp_tac) >>
      simp[EL_DROP]) >>
  strip_tac >>
  `is_terminator (EL (LENGTH (get_params bb.bb_instructions)+j)
      bb.bb_instructions).inst_opcode` by simp[is_terminator_def] >>
  fs[bb_well_formed_def] >>
  qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
    (qspec_then `LENGTH (get_params bb.bb_instructions)+j` mp_tac) >>
  simp[is_terminator_def] >> decide_tac
QED

(* One consumer for every concrete positive phase seed. *)
Theorem native_ready_seeded_worker_available:
  !fn bb dfg a incoming seed ops after.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    a <= LENGTH (non_param_insts bb) /\
    LENGTH (collect_phis bb.bb_instructions) <= LENGTH (get_params bb.bb_instructions)+a /\
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) incoming = SOME (ops,after) /\
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming a seed /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+a)) ==>
      MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k ps v. a <= k /\ k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k ps /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!k ps v. a <= k /\ k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k ps /\
      MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
        (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `!j. a <= j /\ j < LENGTH (non_param_insts bb) ==>
      (EL j (non_param_insts bb)).inst_opcode <> PHI /\
      ((EL j (non_param_insts bb)).inst_opcode = JMP ==>
        SUC j = LENGTH (non_param_insts bb))` by
    (qspecl_then [`fn`,`bb`,`a`] mp_tac ready_block_ordinary_suffix_layout >> simp[]) >>
  conj_tac
  >- metis_tac[native_seeded_worker_exit_available] >>
  conj_tac >> rpt strip_tac >> metis_tac[native_seeded_suffix_prefix_available]
QED

(* Parameter positivity depends only on the empty input stack, not on
   cleanup heights/promises or the input spill map. *)
Theorem ready_empty_stack_parameter_coverage:
  !fn ps.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\ ps.ps_stack = [] ==>
    EVERY (\v. MEM (Var v) (SND (prepare_params_plan (liveness_analyze fn) fn ps)).ps_stack)
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnPlanLineageSetupTheory.ready_parameter_names_distinct >> strip_tac >>
  drule_all fnPlanLineageDemandTheory.post_parameter_demand_ready >> strip_tac >>
  qspecl_then [`liveness_analyze fn`,`fn`,`ps`] mp_tac prepare_params_plan_inventory >>
  simp[] >> simp[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

(* General empty-stack input includes every cleanup override of initialization. *)
Theorem initialized_entry_block_available:
  !fn dfg initial param_ops incoming block_ops after.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\ initial.ps_stack = [] /\
    prepare_params_plan (liveness_analyze fn) fn initial = (param_ops,incoming) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks) initial =
        SOME (block_ops,after) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (HD fn.fn_blocks).bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k ps v. k < LENGTH (non_param_insts (HD fn.fn_blocks)) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn (HD fn.fn_blocks).bb_label
        (bb_is_halting (HD fn.fn_blocks)) (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
        (LENGTH (HD fn.fn_blocks).bb_instructions) (non_param_insts (HD fn.fn_blocks)) incoming k ps /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)+k)
          (HD fn.fn_blocks).bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!k ps v. k < LENGTH (non_param_insts (HD fn.fn_blocks)) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn (HD fn.fn_blocks).bb_label
        (bb_is_halting (HD fn.fn_blocks)) (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
        (LENGTH (HD fn.fn_blocks).bb_instructions) (non_param_insts (HD fn.fn_blocks)) incoming k ps /\
      MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_entry_static_boundary >> strip_tac >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `?inst_ops. generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
      (LENGTH (HD fn.fn_blocks).bb_instructions) 0
      (non_param_insts (HD fn.fn_blocks)) incoming = SOME (inst_ops,after)` by
    (qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_block_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
      MEM (Var v) incoming.ps_stack \/ Var v IN FDOM incoming.ps_spilled` by
    (qspecl_then [`fn`,`initial`] mp_tac ready_empty_stack_parameter_coverage >>
     simp[EVERY_MEM]) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    native_ready_seeded_worker_available >>
  disch_then (qspecl_then [`0`,`incoming`] mp_tac) >>
  simp[native_inst_prefix_zero] >> metis_tac[]
QED

Theorem incoming_singleton_block_available:
  !fn lbl pred bb pb dfg incoming before pred_ops pred_after clean_ops cleaned block_ops after.
    codegen_ready_fn fn /\ fn_reachable fn lbl /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb <> HD fn.fn_blocks /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    cfg_preds_of (cfg_analyze fn) lbl = [pred] /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb before =
      SOME (pred_ops,pred_after) /\
    EVERY (\v. MEM (Var v) pred_after.ps_stack \/ Var v IN FDOM pred_after.ps_spilled)
      (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) /\
    incoming.ps_stack = pred_after.ps_stack /\ incoming.ps_spilled = pred_after.ps_spilled /\
    clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming = (clean_ops,cleaned) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (block_ops,after) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k ps v. k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) cleaned k ps /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!k ps v. k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) cleaned k ps /\
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  drule_all nonentry_block_no_params >> strip_tac >>
  `collect_phis bb.bb_instructions = []` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
     first_x_assum (qspec_then `bb` mp_tac) >> simp[NULL_EQ]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
    MEM (Var v) cleaned.ps_stack \/ Var v IN FDOM cleaned.ps_spilled` by
    (drule_at (Pat `clean_stack_plan _ _ _ _ _ = _`)
       analyzed_single_pred_clean_available >> simp[EVERY_MEM] >>
     disch_then (qspecl_then [`pred`,`pb`,`lbl`,`pred_after`] mp_tac) >>
     gvs[EVERY_MEM]) >>
  `?inst_ops. generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
    bb.bb_label (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) 0 (non_param_insts bb) cleaned = SOME (inst_ops,after)` by
    (qpat_x_assum `generate_block_plan _ _ _ _ bb incoming = _` mp_tac >>
     simp[generate_block_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
    native_ready_seeded_worker_available >>
  disch_then (qspecl_then [`0`,`cleaned`] mp_tac) >>
  simp[native_inst_prefix_zero] >> metis_tac[]
QED

Theorem incoming_join_block_available:
  !fn entry lbl pred bb pb dfg incoming before pred_ops pred_after block_ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb before =
      SOME (pred_ops,pred_after) /\
    incoming.ps_stack = pred_after.ps_stack /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (block_ops,after) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k ps v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k ps /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!k ps v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) incoming k ps /\
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  drule_all nonentry_block_no_params >> strip_tac >>
  `?inst_ops. generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn
    bb.bb_label (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) 0 (non_param_insts bb) incoming = SOME (inst_ops,after)` by
    metis_tac[generate_join_block_worker] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH (non_param_insts bb)` by
    (qspec_then `bb` (qx_choose_then `tail` assume_tac) non_param_insts_phi_prefix >>
     qpat_x_assum `non_param_insts bb = _ ++ _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `?seed suffix_ops.
    native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (non_param_insts bb) incoming
      (LENGTH (collect_phis bb.bb_instructions)) seed /\
    generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (LENGTH (collect_phis bb.bb_instructions))
      (DROP (LENGTH (collect_phis bb.bb_instructions)) (non_param_insts bb)) seed =
      SOME (suffix_ops,after)` by metis_tac[native_worker_prefix_boundary] >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (get_params bb.bb_instructions)+LENGTH (collect_phis bb.bb_instructions))) ==>
    MEM (Var v) seed.ps_stack \/ Var v IN FDOM seed.ps_spilled` by
    (simp[] >> rpt strip_tac >>
     metis_tac[incoming_join_native_post_phi_available]) >>
  drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ 0 _ _ = _`)
    native_ready_seeded_worker_available >>
  disch_then (qspecl_then [`LENGTH (collect_phis bb.bb_instructions)`,`seed`] mp_tac) >>
  simp[] >> metis_tac[]
QED


(* The setup equation exposes the actual worker start, including arbitrary
   incoming cleanup bookkeeping. No execution is selected by this interface. *)
Theorem incoming_edge_block_available:
  !fn entry lbl pred bb pb dfg incoming before pred_ops pred_after setup_ops start block_ops after.
    codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
    fn_reachable fn lbl /\ lbl <> entry /\
    cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb before =
      SOME (pred_ops,pred_after) /\
    EVERY (\v. MEM (Var v) pred_after.ps_stack \/ Var v IN FDOM pred_after.ps_spilled)
      (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) /\
    incoming.ps_stack = pred_after.ps_stack /\ incoming.ps_spilled = pred_after.ps_spilled /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1 then
       clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming
     else ([],incoming)) = (setup_ops,start) /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb incoming =
      SOME (block_ops,after) ==>
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
      MEM (Var v) after.ps_stack \/ Var v IN FDOM after.ps_spilled) /\
    (!k ps v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start k ps /\
      MEM (Var v) (compute_operands
        (EL (LENGTH (get_params bb.bb_instructions)+k) bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!k ps v. LENGTH (collect_phis bb.bb_instructions) <= k /\
      k < LENGTH (non_param_insts bb) /\
      native_inst_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (non_param_insts bb) start k ps /\
      MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (get_params bb.bb_instructions)+k)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
     metis_tac[venomExecPropsTheory.lookup_block_label]) >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) = 1`
  >- (`cfg_preds_of (cfg_analyze fn) lbl = [pred]` by
        (gvs[LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
      `clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn bb incoming =
        (setup_ops,start)` by gvs[] >>
      metis_tac[incoming_singleton_block_available]) >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `start = incoming` by gvs[] >> gvs[] >>
  metis_tac[incoming_join_block_available, arithmeticTheory.ADD_COMM]
QED

(* Exact dispatcher frame for the ordinary interval, including OFFSET. *)
Theorem native_ordinary_shared_core_replay:
  !lv dfg cfg fn inst nl halt term lbl ps prefixP prefixQ.
    codegen_ready_inst inst /\ inst_wf inst /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    EVERY (\v. ~MEM (Var v) prefixP) (nl ++ inst.inst_outputs) /\
    EVERY (\v. ~MEM (Var v) prefixQ) (nl ++ inst.inst_outputs) ==>
    ?ops qs.
      generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
      generate_inst_plan lv dfg cfg fn inst nl halt term lbl
        (ps with ps_stack := prefixP ++ ps.ps_stack) =
        SOME (ops,qs with ps_stack := prefixP ++ qs.ps_stack) /\
      generate_inst_plan lv dfg cfg fn inst nl halt term lbl
        (ps with ps_stack := prefixQ ++ ps.ps_stack) =
        SOME (ops,qs with ps_stack := prefixQ ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >> fs[codegen_ready_inst_def] >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      drule_all fnPlanLineageStagesTheory.generate_offset_plan_frame >>
      disch_tac >>
      qexistsl_tac [`[SOPushOfst lbl' (w2n v)]`,
        `ps with ps_stack := ps.ps_stack ++ [Var out]`] >>
      simp[generate_inst_plan_def,APPEND_ASSOC]) >>
  Cases_on `is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP`
  >- (qexistsl_tac [`[]`,`ps`] >> gvs[generate_inst_plan_def,codegen_ready_inst_def]) >>
  gvs[generate_inst_plan_def] >>
  namedCases_on `generate_regular_inst_plan lv dfg cfg fn inst nl halt term lbl ps`
    ["ops qs"] >>
  qexistsl_tac [`ops`,`qs`] >> simp[] >> conj_tac >>
  irule native_regular_bottom_frame >> simp[]
QED

Theorem native_ordinary_paired_interval_replay:
  !k lv dfg cfg fn lbl halt np bl xs p0 prefixP prefixQ.
    k <= LENGTH xs /\
    (!j p inst rest.
      j < k /\ native_inst_prefix lv dfg cfg fn lbl halt np bl xs p0 j p /\
      DROP j xs = inst::rest ==>
      codegen_ready_inst inst /\ inst_wf inst /\
      inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
      (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
        MEM x p.ps_stack \/ x IN FDOM p.ps_spilled) /\
      EVERY (\v. ~MEM (Var v) prefixP)
        ((if rest = [] then live_vars_at lv lbl bl
          else live_vars_at lv lbl (j+np+1)) ++ inst.inst_outputs) /\
      EVERY (\v. ~MEM (Var v) prefixQ)
        ((if rest = [] then live_vars_at lv lbl bl
          else live_vars_at lv lbl (j+np+1)) ++ inst.inst_outputs)) ==>
    ?ops q.
      native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops q /\
      native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs
        (p0 with ps_stack := prefixP ++ p0.ps_stack) k ops
        (q with ps_stack := prefixP ++ q.ps_stack) /\
      native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs
        (p0 with ps_stack := prefixQ ++ p0.ps_stack) k ops
        (q with ps_stack := prefixQ ++ q.ps_stack)
Proof
  rpt gen_tac >> Induct_on `k`
  >- (rpt strip_tac >> qexistsl_tac [`[]`,`p0`] >>
      simp[native_inst_ops_prefix_zero]) >>
  strip_tac >> qpat_x_assum `_ ==> ?ops q. _` mp_tac >>
  (impl_tac >- (conj_tac >- simp[] >> rpt strip_tac >>
    `j < SUC k` by decide_tac >> metis_tac[])) >>
  strip_tac >>
  `native_inst_prefix lv dfg cfg fn lbl halt np bl xs p0 k q` by
    metis_tac[native_inst_ops_prefix_erase] >>
  Cases_on `DROP k xs`
  >- (fs[listTheory.DROP_EQ_NIL] >> decide_tac) >>
  rename1 `DROP k xs = inst::rest` >>
  qpat_x_assum `!j p inst rest. _` (qspecl_then [`k`,`q`,`inst`,`rest`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `nl = if rest = [] then live_vars_at lv lbl bl
    else live_vars_at lv lbl (k+np+1)` >>
  qabbrev_tac `term = case rest of [] => F | h::t => is_terminator h.inst_opcode` >>
  `?step qs.
     generate_inst_plan lv dfg cfg fn inst nl halt term lbl q = SOME (step,qs) /\
     generate_inst_plan lv dfg cfg fn inst nl halt term lbl
       (q with ps_stack := prefixP ++ q.ps_stack) =
       SOME (step,qs with ps_stack := prefixP ++ qs.ps_stack) /\
     generate_inst_plan lv dfg cfg fn inst nl halt term lbl
       (q with ps_stack := prefixQ ++ q.ps_stack) =
       SOME (step,qs with ps_stack := prefixQ ++ qs.ps_stack)` by
    (irule native_ordinary_shared_core_replay >> simp[Abbr `nl`]) >>
  rename1 `generate_inst_plan lv dfg cfg fn inst nl halt term lbl q = SOME (step_ops,qs)` >>
  qexistsl_tac [`ops ++ step_ops`,`qs`] >>
  simp[native_inst_ops_prefix_suc] >>
  rpt conj_tac >> rpt (first_assum $ irule_at Any) >>
  gvs[Abbr `nl`,Abbr `term`]
QED

Theorem native_inst_ops_prefix_deterministic:
  native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops q /\
  native_inst_ops_prefix lv dfg cfg fn lbl halt np bl xs p0 k ops' q' ==>
  ops = ops' /\ q = q'
Proof
  simp[native_inst_ops_prefix_exec] >> strip_tac >> gvs[]
QED

Theorem analyzed_ordinary_paired_interval_replay:
  !fn bb a xs n k dfg cfg halt p0 prefixP prefixQ.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    xs = DROP a (non_param_insts bb) /\
    n = LENGTH (get_params bb.bb_instructions) + a /\ k <= LENGTH xs /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label n) ==>
      MEM (Var v) p0.ps_stack \/ Var v IN FDOM p0.ps_spilled) /\
    (!j. j < k ==> (EL j xs).inst_opcode <> JMP /\ (EL j xs).inst_opcode <> PHI) /\
    (!j. j < k ==>
      EVERY (\v. ~MEM (Var v) prefixP)
        (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (n+j)) ++
         (EL j xs).inst_outputs) /\
      EVERY (\v. ~MEM (Var v) prefixQ)
        (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (n+j)) ++
         (EL j xs).inst_outputs)) ==>
    ?ops q.
      native_inst_ops_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label halt n
        (LENGTH bb.bb_instructions) xs p0 k ops q /\
      native_inst_ops_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label halt n
        (LENGTH bb.bb_instructions) xs (p0 with ps_stack := prefixP ++ p0.ps_stack)
        k ops (q with ps_stack := prefixP ++ q.ps_stack) /\
      native_inst_ops_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label halt n
        (LENGTH bb.bb_instructions) xs (p0 with ps_stack := prefixQ ++ p0.ps_stack)
        k ops (q with ps_stack := prefixQ ++ q.ps_stack)
Proof
  rpt gen_tac >> strip_tac >> irule native_ordinary_paired_interval_replay >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `j < LENGTH xs` by decide_tac >>
  `inst = EL j xs` by metis_tac[HD_DROP,HD] >>
  `a+j < LENGTH (non_param_insts bb)` by gvs[] >>
  `inst = EL (a+j) (non_param_insts bb)` by
    (gvs[] >> simp[EL_DROP]) >>
  `inst = EL (n+j) bb.bb_instructions` by
    (drule_all ready_block_suffix_index >> gvs[]) >>
  `n+j < LENGTH bb.bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[] >>
     gvs[] >> decide_tac) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (n+j)) ==>
    MEM (Var v) p.ps_stack \/ Var v IN FDOM p.ps_spilled` by
    (drule native_ordinary_interval_available >>
     disch_then (qspecl_then [`bb`,`a`] mp_tac) >>
     gvs[]) >>
  `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
  `inst_wf inst /\ codegen_ready_inst inst` by
    (drule_all fnPlanLineageQuarantineTheory.ready_member_instruction_shape >> simp[]) >>
  `DROP (a+j) (non_param_insts bb) = inst::rest` by
    gvs[DROP_DROP_T,arithmeticTheory.ADD_COMM] >>
  `!v. MEM (Var v) (compute_operands inst) ==>
    MEM (Var v) p.ps_stack \/ Var v IN FDOM p.ps_spilled` by
    (qpat_assum `inst = EL (n+j) _` SUBST1_TAC >>
     rpt strip_tac >> irule analyzed_live_coverage_computed_operands >>
     goal_assum (drule_at Any) >> qexists_tac `fn` >> simp[]) >>
  `!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
    MEM x p.ps_stack \/ x IN FDOM p.ps_spilled` by
    (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
  qpat_x_assum `!j. j < k ==> EVERY _ _ /\ _` (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!j. j < k ==> (EL j xs).inst_opcode <> JMP /\ _`
    (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  `((if rest = [] then
       live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at (liveness_analyze fn) bb.bb_label
       ((a+j) + LENGTH (get_params bb.bb_instructions) + 1)) =
     live_vars_at (liveness_analyze fn) bb.bb_label
       (SUC (LENGTH (get_params bb.bb_instructions) + (a+j))))` by
    (irule ready_block_suffix_next_live >> metis_tac[]) >>
  gvs[]
QED
