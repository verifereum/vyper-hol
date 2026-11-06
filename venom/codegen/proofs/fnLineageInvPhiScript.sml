Theory fnLineageInvPhi
Ancestors
  fnPlanLineagePhiInventory fnPlanPrefix fnPlanLineagePhiTemporal
  fnPlanLineageInventory genBlockSim rich_list fnPlanLineageSetup doSwapSim planSpillBounds reorderSim
  stackPlanOps stackModel stackPlanGen stackPlanTypes planAlign venomInst list finite_map

Theorem dead_input_live_output_phi_released_membership:
 !inst nl halting ps d x ops qs final.
 stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
 stack_peek d ps.ps_stack = x /\
 is_var_operand x /\
 LENGTH (FILTER (\op. op = x) ps.ps_stack) = 1 /\
 ~MEM (operand_to_string x) nl /\
 MEM (HD inst.inst_outputs) nl /\
 (!op. MEM op ps.ps_stack /\ op <> dead_stack_marker /\ op <> x ==> MEM op (MAP Var nl)) /\
 (!v. MEM v nl /\ v <> HD inst.inst_outputs ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
 generate_phi_plan inst nl halting ps = (ops,qs) /\
 final = release_dead_spills nl qs
 ==>
 (!op. ((MEM op final.ps_stack /\ op <> dead_stack_marker) \/ op IN FDOM final.ps_spilled) <=> MEM op (MAP Var nl))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`nl`, `halting`] mp_tac) >>
  simp[phi_write_phase_def] >> strip_tac >>
  gvs[] >> simp[release_dead_spills_stack, phi_release_dead_spills_domain] >>
  gen_tac >> eq_tac
  >- (strip_tac
      >- (drule_at (Pos last) stack_poke_unique_inventory >> simp[] >> strip_tac >> gvs[] >>
          metis_tac[MEM_MAP]) >>
      metis_tac[MEM_MAP]) >>
  simp[MEM_MAP] >> strip_tac >> gvs[] >> rename1 `MEM v nl` >>
  `Var v <> dead_stack_marker` by simp[dead_stack_marker_def] >>
  Cases_on `v = HD inst.inst_outputs`
  >- (gvs[] >> disj1_tac >> simp[stack_poke_def, MEM_LUPDATE]) >>
  `Var v <> stack_peek d ps.ps_stack` by
    (strip_tac >> qpat_x_assum `Var v = _` (mp_tac o GSYM) >>
     disch_then SUBST_ALL_TAC >> gvs[operand_to_string_def]) >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  metis_tac[stack_poke_preserves_other_member]
QED

Theorem fresh_poke_core_resource:
 !ps m core base d out.
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf base [] (ps with ps_stack := core) /\
 ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled /\
 d < LENGTH core ==>
 lineage_core m (stack_poke d (Var out) core)
   (ps with ps_stack := stack_poke d (Var out) ps.ps_stack) /\
 EVERY is_var_operand (stack_poke d (Var out) core) /\
 residual_budget_wf base [] (ps with ps_stack := stack_poke d (Var out) core)
Proof
 rpt gen_tac >> strip_tac >>
 drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
 `~MEM (Var out) core` by gvs[lineage_core_def, MEM_APPEND] >>
 conj_tac
 >- gvs[lineage_core_def, stack_poke_bottom_extension] >>
 conj_tac
 >- (gvs[EVERY_MEM, stack_poke_def, MEM_LUPDATE] >> rpt strip_tac >>
     gvs[is_var_operand_def] >> metis_tac[EL_MEM]) >>
 irule residual_budget_wf_canonical >>
 gvs[residual_budget_wf_def, plan_slots_bounded_def] >>
 metis_tac[phi_poke_fresh_distinct, phi_poke_fresh_disjoint]
QED

Theorem dup_fresh_poke_core_resource:
 !ps m core base d out ds p.
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf base [] (ps with ps_stack := core) /\
 ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled /\
 d < LENGTH ps.ps_stack /\ do_dup d ps = (ds,p) ==>
 lineage_core m (core ++ [Var out])
   (p with ps_stack := stack_poke 0 (Var out) p.ps_stack) /\
 EVERY is_var_operand (core ++ [Var out]) /\
 residual_budget_wf base [] (p with ps_stack := core ++ [Var out])
Proof
 rpt gen_tac >> strip_tac >>
 drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
 `~MEM (Var out) core` by gvs[lineage_core_def, MEM_APPEND] >>
 rename1 `residual_budget_wf spillbase [] (ps with ps_stack := core)` >>
 `plan_slots_bounded spillbase ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
   (gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]) >>
 drule_all do_dup_multiplicity_layout >> strip_tac >>
 drule_all do_dup_slots_bounded >> strip_tac >>
 `p.ps_stack = ps.ps_stack ++ [stack_peek d ps.ps_stack]` by
   (drule do_dup_stack_exact >> simp[]) >>
 conj_tac
 >- (gvs[lineage_core_def, stack_poke_def, LUPDATE_APPEND2, LUPDATE_def, APPEND_ASSOC]) >>
 conj_tac >- simp[EVERY_APPEND, is_var_operand_def] >>
 irule residual_budget_wf_canonical >>
 gvs[plan_slots_bounded_def, ALL_DISTINCT_APPEND, pred_setTheory.DISJOINT_DEF,
     pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem phi_write_phase_core_resource:
 !inst nl ps m core spillbase d ops qs.
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
 Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
 stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
 phi_write_phase inst nl d ps = (ops,qs) ==>
 ?rest. lineage_core m rest qs /\ EVERY is_var_operand rest /\
   residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
 rpt gen_tac >> strip_tac >>
 drule stack_get_phi_depth_var_not_marker >> strip_tac >>
 `d < LENGTH core` by
   (spose_not_then assume_tac >>
    gvs[lineage_core_def, stack_peek_def, EL_APPEND_EQN] >>
    gvs[EL_REPLICATE]) >>
 qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
 simp[phi_write_phase_def] >> IF_CASES_TAC
 >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     drule_all dup_fresh_poke_core_resource >> strip_tac >>
     qexists_tac `core ++ [Var (HD inst.inst_outputs)]` >> simp[]) >>
 strip_tac >> gvs[] >>
 drule_all fresh_poke_core_resource >> strip_tac >>
 qexists_tac `stack_poke d (Var (HD inst.inst_outputs)) core` >> simp[]
QED

Theorem generate_phi_plan_released_core_resource:
 !inst nl halting ps m core spillbase ops qs final.
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] (ps with ps_stack := core) /\
 ~MEM (Var (HD inst.inst_outputs)) ps.ps_stack /\
 Var (HD inst.inst_outputs) NOTIN FDOM ps.ps_spilled /\
 generate_phi_plan inst nl halting ps = (ops,qs) /\
 final = release_dead_spills nl qs ==>
 ?rest. lineage_core m rest final /\ EVERY is_var_operand rest /\
   residual_budget_wf spillbase [] (final with ps_stack := rest)
Proof
 rpt gen_tac >> strip_tac >> gvs[] >>
 `?rest. lineage_core m rest qs /\ EVERY is_var_operand rest /\
   residual_budget_wf spillbase [] (qs with ps_stack := rest)` by
   (Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
    >- (gvs[generate_phi_plan_def] >> metis_tac[]) >>
    rename1 `_ = SOME d` >>
    drule generate_phi_plan_write_phase >>
    disch_then (qspecl_then [`nl`, `halting`] mp_tac) >>
    simp[LET_THM] >> pairarg_tac >> simp[] >>
    drule_all phi_write_phase_core_resource >> strip_tac >>
    IF_CASES_TAC
    >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
        `DISJOINT (set (REPLICATE m dead_stack_marker))
           (set [Var (HD inst.inst_outputs)])` by
          simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
               MEM_REPLICATE, dead_stack_marker_def] >>
        qpat_x_assum `lineage_core m rest ps1` mp_tac >>
        pure_rewrite_tac[lineage_core_def] >> strip_tac >>
        drule popmany_plan_core_resource >>
        disch_then (qspecl_then [`spillbase`, `[Var (HD inst.inst_outputs)]`, `ps2`] mp_tac) >>
        simp[] >> strip_tac >>
        qexists_tac `rest'` >> simp[lineage_core_def] >>
        fs[EVERY_MEM, pred_setTheory.EXTENSION] >> metis_tac[]) >>
    strip_tac >> gvs[] >> metis_tac[]) >>
 qexists_tac `rest` >>
 simp[lineage_core_def, release_dead_spills_stack] >>
 metis_tac[residual_budget_wf_release_dead_spills_core, lineage_core_def]
QED

Theorem phi_write_phase_member_support:
 !inst nl d ps ops qs x.
 d < LENGTH ps.ps_stack /\
 phi_write_phase inst nl d ps = (ops,qs) ==>
 (MEM x ps.ps_stack /\ x <> stack_peek d ps.ps_stack ==>
    MEM x qs.ps_stack) /\
 (MEM x qs.ps_stack ==> MEM x ps.ps_stack \/ x = Var (HD inst.inst_outputs))
Proof
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
 simp[phi_write_phase_def] >> IF_CASES_TAC
 >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     drule do_dup_stack_exact >> simp[] >> strip_tac >>
     gvs[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def, MEM_APPEND] >>
     metis_tac[]) >>
 strip_tac >> gvs[] >> conj_tac
 >- metis_tac[stack_poke_preserves_other_member] >>
 simp[stack_poke_def, MEM_LUPDATE] >> metis_tac[EL_MEM]
QED

Theorem generate_phi_plan_released_member_support:
 !inst nl halting ps ops qs final x.
 generate_phi_plan inst nl halting ps = (ops,qs) /\
 final = release_dead_spills nl qs ==>
 (MEM x ps.ps_stack /\ ~MEM x (FILTER is_var_operand inst.inst_operands) /\
    x <> Var (HD inst.inst_outputs) ==> MEM x final.ps_stack) /\
 (MEM x final.ps_stack \/ x IN FDOM final.ps_spilled ==>
    MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled \/ x = Var (HD inst.inst_outputs))
Proof
 rpt gen_tac >> strip_tac >> gvs[] >>
 `qs.ps_spilled = ps.ps_spilled` by
   (mp_tac (Q.SPECL [`inst`, `nl`, `halting`, `ps`] generate_phi_plan_state_frame) >>
    simp[] >> disch_then (mp_tac o AP_TERM ``\p:plan_state. p.ps_spilled``) >> simp[]) >>
 simp[release_dead_spills_stack, phi_release_dead_spills_domain] >>
 Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
 >- (gvs[generate_phi_plan_def] >> metis_tac[]) >>
 rename1 `_ = SOME d` >>
 `d < LENGTH ps.ps_stack` by metis_tac[stack_get_phi_depth_var_not_marker] >>
 `MEM (stack_peek d ps.ps_stack) (FILTER is_var_operand inst.inst_operands)` by
   (fs[stack_get_phi_depth_def] >> drule stack_find_el >> strip_tac >>
    `stack_peek d ps.ps_stack = EL d (REVERSE ps.ps_stack)` by
      (simp[stack_peek_def, EL_REVERSE] >> AP_THM_TAC >> AP_TERM_TAC >> decide_tac) >>
    gvs[]) >>
 drule generate_phi_plan_write_phase >>
 disch_then (qspecl_then [`nl`, `halting`] mp_tac) >>
 Cases_on `phi_write_phase inst nl d ps` >> simp[] >>
 `r.ps_spilled = ps.ps_spilled` by
   (mp_tac (Q.SPECL [`inst`, `nl`, `d`, `ps`] phi_write_phase_state_frame) >>
    simp[] >> disch_then (mp_tac o AP_TERM ``\p:plan_state. p.ps_spilled``) >> simp[]) >>
 drule_all phi_write_phase_member_support >> strip_tac >>
 IF_CASES_TAC
 >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     conj_tac
     >- (strip_tac >>
         `MEM x r.ps_stack` by metis_tac[] >>
         qspecl_then [`[Var (HD inst.inst_outputs)]`, `r`, `x`] mp_tac
           popmany_plan_retains_other >> simp[]) >>
     drule popmany_plan_inventory_subset >> simp[] >> metis_tac[]) >>
 strip_tac >> gvs[] >> metis_tac[]
QED

Theorem released_phi_prefix_preservation:
 !steps s m core spillbase.
 lineage_core m core (s 0) /\ EVERY is_var_operand core /\
 residual_budget_wf spillbase [] ((s 0) with ps_stack := core) /\
 EVERY (\step. (FST step).inst_outputs <> []) steps /\
 ALL_DISTINCT (MAP (\step. HD (FST step).inst_outputs) steps) /\
 (!j. j < LENGTH steps ==>
   ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s 0).ps_stack /\
   Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s 0).ps_spilled) /\
 (!i j x. i < LENGTH steps /\ j < LENGTH steps /\ i <> j /\
   MEM x (FILTER is_var_operand (FST (EL i steps)).inst_operands) ==>
   ~MEM x (FILTER is_var_operand (FST (EL j steps)).inst_operands)) /\
 (!j. j < LENGTH steps ==> ?w.
   MEM w (FILTER is_var_operand (FST (EL j steps)).inst_operands) /\
   MEM w (s 0).ps_stack) /\
 (!j. j < LENGTH steps ==>
   s (SUC j) = release_dead_spills (FST (SND (EL j steps)))
     (SND (generate_phi_plan (FST (EL j steps)) (FST (SND (EL j steps)))
       (SND (SND (EL j steps))) (s j)))) ==>
 !k. k <= LENGTH steps ==>
   (!j w. k <= j /\ j < LENGTH steps /\
     MEM w (FILTER is_var_operand (FST (EL j steps)).inst_operands) /\
     MEM w (s 0).ps_stack ==> MEM w (s k).ps_stack) /\
   (!j. k <= j /\ j < LENGTH steps ==>
     ~MEM (Var (HD (FST (EL j steps)).inst_outputs)) (s k).ps_stack /\
     Var (HD (FST (EL j steps)).inst_outputs) NOTIN FDOM (s k).ps_spilled) /\
   (?rest. lineage_core m rest (s k) /\ EVERY is_var_operand rest /\
     residual_budget_wf spillbase [] ((s k) with ps_stack := rest))
Proof
 rpt gen_tac >> strip_tac >> Induct
 >- (simp[] >> metis_tac[]) >>
 strip_tac >> `k <= LENGTH steps /\ k < LENGTH steps` by decide_tac >>
 first_x_assum drule >> strip_tac >>
 Cases_on `generate_phi_plan (FST (EL k steps)) (FST (SND (EL k steps)))
   (SND (SND (EL k steps))) (s k)` >>
 `s (SUC k) = release_dead_spills (FST (SND (EL k steps))) r` by
   (qpat_x_assum `!j. j < LENGTH steps ==> s (SUC j) = _`
      (qspec_then `k` mp_tac) >> simp[]) >>
 drule generate_phi_plan_released_member_support >>
 disch_then (qspec_then `s (SUC k)` mp_tac) >> simp[] >> strip_tac >>
 conj_tac
 >- (rpt gen_tac >> strip_tac >>
     `k <= j /\ k <> j` by decide_tac >>
     `MEM w (s k).ps_stack` by metis_tac[] >>
     `~MEM w (FILTER is_var_operand (FST (EL k steps)).inst_operands)` by metis_tac[] >>
     `w <> Var (HD (FST (EL k steps)).inst_outputs)` by metis_tac[] >>
     metis_tac[]) >>
 conj_tac
 >- (gen_tac >> strip_tac >>
     `k <= j /\ k <> j` by decide_tac >>
     `HD (FST (EL k steps)).inst_outputs <> HD (FST (EL j steps)).inst_outputs` by
       (drule ALL_DISTINCT_EL_IMP >>
        disch_then (qspecl_then [`k`, `j`] mp_tac) >> simp[EL_MAP]) >>
     `Var (HD (FST (EL k steps)).inst_outputs) <>
      Var (HD (FST (EL j steps)).inst_outputs)` by simp[] >>
     metis_tac[]) >>
 `~MEM (Var (HD (FST (EL k steps)).inst_outputs)) (s k).ps_stack /\
  Var (HD (FST (EL k steps)).inst_outputs) NOTIN FDOM (s k).ps_spilled` by
   (qpat_x_assum `!j. k <= j /\ j < LENGTH steps ==> _`
      (qspec_then `k` mp_tac) >> simp[]) >>
 drule_all generate_phi_plan_released_core_resource >> simp[]
QED

Theorem halting_phi_retains_dead_output_probe:
 !inst ps.
 (release_dead_spills []
   (SND (generate_phi_plan
     (inst with <|inst_operands := [Var "x"]; inst_outputs := ["y"]|>) [] T
     (ps with <|ps_stack := [Var "x"]; ps_spilled := FEMPTY|>)))).ps_stack = [Var "y"]
Proof
 EVAL_TAC >> simp[]
QED
