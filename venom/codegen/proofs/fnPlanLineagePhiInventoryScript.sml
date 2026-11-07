Theory fnPlanLineagePhiInventory
Ancestors
  fnPlanLineagePhiTemporal fnPlanLineageInventory planAlign stackPlanGen
  stackPlanOps stackModel sorting list rich_list pred_set

(* Whole-list uniqueness, not uniqueness of only the active suffix. *)
Theorem lupdate_unique_inventory:
  !(xs:'a list) n x y z.
    n < LENGTH xs /\ EL n xs = x /\
    LENGTH (FILTER (\op. op = x) xs) = 1 /\
    MEM z (LUPDATE y n xs) ==>
    z = y \/ (MEM z xs /\ z <> x)
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> Cases_on `n`
  >- (pop_assum kall_tac >> simp[LUPDATE_def] >> rpt strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      `MEM h (FILTER (\op. op = h) xs)` by simp[MEM_FILTER] >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `n' < LENGTH xs` by fs[] >>
  Cases_on `h = x`
  >- (gvs[] >>
      `MEM (EL n' xs) xs` by simp[EL_MEM] >>
      `MEM (EL n' xs) (FILTER (\op. op = EL n' xs) xs)` by
        simp[MEM_FILTER] >> gvs[]) >>
  gvs[LUPDATE_def] >> metis_tac[]
QED

Theorem stack_poke_unique_inventory:
  !stk d x y op.
    d < LENGTH stk /\ stack_peek d stk = x /\
    LENGTH (FILTER (\v. v = x) stk) = 1 /\
    MEM op (stack_poke d y stk) ==>
    op = y \/ (MEM op stk /\ op <> x)
Proof
  rpt strip_tac >> gvs[stack_peek_def, stack_poke_def] >>
  irule lupdate_unique_inventory >> goal_assum (drule_at Any) >>
  qexists_tac `LENGTH stk - (d + 1)` >> simp[]
QED

Theorem dead_phi_spilled_unchanged:
  !inst next halting ps d x ops qs.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = x /\
    ~MEM (operand_to_string x) next /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    qs.ps_spilled = ps.ps_spilled
Proof
  rpt strip_tac >> drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] mp_tac) >>
  simp[phi_write_phase_def] >> strip_tac >>
  gvs[] >> Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `popmany_plan _ _ = _` (mp_tac o Q.AP_TERM `\r. (SND r).ps_spilled`) >>
  simp[popmany_plan_spilled_unchanged]
QED

(* Saturated stack_swap inventory is shared from fnPlanLineageInventory. *)

Theorem dead_phi_stack_inventory:
  !inst next halting ps d x ops qs.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = x /\
    LENGTH (FILTER (\op. op = x) ps.ps_stack) = 1 /\
    ~MEM (operand_to_string x) next /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    !op. MEM op qs.ps_stack ==>
      op = Var (HD inst.inst_outputs) \/ (MEM op ps.ps_stack /\ op <> x)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] mp_tac) >>
  simp[phi_write_phase_def] >> strip_tac >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> gvs[]
  >- (pairarg_tac >> gvs[] >>
      qmatch_asmsub_abbrev_tac `popmany_plan [ret] st = _` >>
      `!op. MEM op ps2.ps_stack ==> MEM op st.ps_stack` by
        (Cases_on `stack_get_depth ret st.ps_stack`
         >- (gvs[popmany_plan_def, popmany_individual_def,
                  is_contiguous_top_def, QSORT_DEF, PARTITION_DEF, PART_DEF] >> simp[]) >>
         drule popmany_singleton_stack_projection >> simp[] >> strip_tac >>
         gvs[] >> rpt strip_tac >>
         irule stack_swap_mem_subset >>
         metis_tac[MEM_TAKE, stack_pop_def]) >>
      rpt strip_tac >>
      `MEM op st.ps_stack` by metis_tac[] >>
      gvs[Abbr `st`, Abbr `ret`] >>
      irule stack_poke_unique_inventory >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule stack_poke_unique_inventory >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem dead_phi_inventory_support:
  !inst next halting ps d x ops qs P.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = x /\
    LENGTH (FILTER (\op. op = x) ps.ps_stack) = 1 /\
    ~MEM (operand_to_string x) next /\
    generate_phi_plan inst next halting ps = (ops,qs) /\
    (!v. (MEM (Var v) ps.ps_stack /\ Var v <> x) \/
         Var v IN FDOM ps.ps_spilled ==> P v) /\
    P (HD inst.inst_outputs) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==> P v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dead_phi_spilled_unchanged >> strip_tac >>
  gen_tac >> strip_tac
  >- (drule_all dead_phi_stack_inventory >> strip_tac >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

(* Origin test for the full native PHI, including live-input duplication
   and dead-output popping. No distinctness or multiplicity premise. *)
Theorem generate_phi_plan_inventory_origins:
  !inst next halting ps ops qs.
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    !at. MEM at qs.ps_stack \/ at IN FDOM qs.ps_spilled ==>
      at = Var (HD inst.inst_outputs) \/
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- simp[generate_phi_plan_def] >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`, `halting`] mp_tac) >>
  Cases_on `phi_write_phase inst next d ps` >> simp[] >> strip_tac >>
  rename1 `phi_write_phase inst next d ps = (wops,ws)` >>
  `!at. MEM at ws.ps_stack \/ at IN FDOM ws.ps_spilled ==>
      at = Var (HD inst.inst_outputs) \/
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    (qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
     simp[phi_write_phase_def] >> IF_CASES_TAC
     >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
         drule_at (Pat `do_dup _ _ = _`) do_dup_inventory_subset >>
         simp[] >> strip_tac >>
         metis_tac[stack_poke_mem_subset_nb]) >>
     strip_tac >> gvs[] >> metis_tac[stack_poke_mem_subset_nb]) >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[popmany_plan_inventory_subset]) >>
  strip_tac >> gvs[]
QED

Theorem generate_phi_plan_no_selection:
  !inst next halting ps.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = NONE ==>
    generate_phi_plan inst next halting ps = ([],ps)
Proof
  simp[generate_phi_plan_def]
QED

(* Exact copy from reorderSim: importing that frame theory here would cycle. *)
Theorem ALL_DISTINCT_LUPDATE_fresh[local]:
  !xs i x. ALL_DISTINCT xs /\ i < LENGTH xs /\ ~MEM x xs ==>
    ALL_DISTINCT (LUPDATE x i xs)
Proof
  rw[EL_ALL_DISTINCT_EL_EQ, EL_LUPDATE] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  metis_tac[ALL_DISTINCT_EL_IMP, MEM_EL]
QED

Theorem distinct_lupdate_set[local]:
  !(xs:'a list) i y. ALL_DISTINCT xs /\ i < LENGTH xs ==>
    set (LUPDATE y i xs) = y INSERT (set xs DELETE (EL i xs))
Proof
  Induct_on `xs` >- simp[] >>
  gen_tac >> Cases_on `i` >> simp[LUPDATE_def] >> rpt strip_tac >>
  gvs[] >> simp[EXTENSION] >> metis_tac[EL_MEM]
QED

Theorem fresh_poke_lineage_inventory:
  !S ps d v y.
    lineage_inventory S ps /\ d < LENGTH ps.ps_stack /\
    stack_peek d ps.ps_stack = Var v /\ Var y NOTIN S ==>
    lineage_inventory ((S DELETE (Var v)) UNION {Var y})
      (ps with ps_stack := stack_poke d (Var y) ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  fs[lineage_inventory_def, lineage_core_def] >>
  `d < LENGTH core` by
    (spose_not_then assume_tac >>
     `LENGTH ps.ps_stack - (d+1) < m` by (gvs[] >> decide_tac) >>
     qpat_x_assum `stack_peek d _ = Var v` mp_tac >>
     pure_asm_rewrite_tac[stack_peek_def] >>
     simp[EL_APPEND1, EL_REPLICATE, dead_stack_marker_def]) >>
  `stack_peek d core = Var v` by
    gvs[stack_peek_def, EL_APPEND2] >>
  simp[lineage_inventory_def, lineage_core_def] >>
  qexistsl_tac [`m`, `stack_poke d (Var y) core`] >>
  simp[stack_poke_bottom_extension] >>
  `~MEM (Var y) core` by gvs[] >>
  `set (stack_poke d (Var y) core) =
     Var y INSERT (set core DELETE (Var v))` by
    (simp[stack_poke_def] >> drule distinct_lupdate_set >>
     disch_then (qspecl_then [`LENGTH core - (d+1)`,`Var y`] mp_tac) >>
     gvs[stack_peek_def]) >>
  conj_tac
  >- (simp[stack_poke_def] >> irule ALL_DISTINCT_LUPDATE_fresh >> simp[]) >>
  conj_tac
  >- (simp[stack_poke_def] >> irule IMP_EVERY_LUPDATE >>
      simp[stackPlanTypesTheory.is_var_operand_def]) >>
  `MEM (Var v) core` by
    (qpat_x_assum `stack_peek d core = _` mp_tac >>
     simp[stack_peek_def] >> strip_tac >>
     `LENGTH core - (d+1) < LENGTH core` by decide_tac >>
     metis_tac[EL_MEM]) >>
  ASM_SET_TAC[]
QED

Theorem dup_fresh_rename_lineage_inventory:
  !S ps d y ops dup.
    lineage_inventory S ps /\ d < LENGTH ps.ps_stack /\
    Var y NOTIN S /\ stackPlanOps$do_dup d ps = (ops,dup) ==>
    lineage_inventory (S UNION {Var y})
      (dup with ps_stack := stack_poke 0 (Var y) dup.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  drule doSwapSimTheory.do_dup_stack_exact >> simp[] >> strip_tac >>
  drule deepResidualBudgetTheory.do_dup_spilled_eq >> strip_tac >>
  `stack_poke 0 (Var y) dup.ps_stack = ps.ps_stack ++ [Var y]` by
    simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def] >>
  fs[lineage_inventory_def, lineage_core_def] >>
  simp[lineage_inventory_def, lineage_core_def] >>
  qexistsl_tac [`m`,`core ++ [Var y]`] >>
  simp[ALL_DISTINCT_APPEND, EVERY_APPEND, stackPlanTypesTheory.is_var_operand_def] >>
  ASM_SET_TAC[]
QED

Theorem phi_write_phase_lineage_inventory:
  !S ps inst next d v ops qs.
    lineage_inventory S ps /\ d < LENGTH ps.ps_stack /\
    stack_peek d ps.ps_stack = Var v /\
    Var (HD inst.inst_outputs) NOTIN S /\
    phi_write_phase inst next d ps = (ops,qs) ==>
    lineage_inventory
      ((if MEM v next then S else S DELETE (Var v)) UNION
        {Var (HD inst.inst_outputs)}) qs /\
    MEM (Var (HD inst.inst_outputs)) qs.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `phi_write_phase _ _ _ _ = _` mp_tac >>
  simp[phi_write_phase_def, stackPlanTypesTheory.operand_to_string_def] >>
  Cases_on `MEM v next` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      conj_tac
      >- (irule dup_fresh_rename_lineage_inventory >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule doSwapSimTheory.do_dup_stack_exact >> simp[] >> strip_tac >>
      simp[stack_poke_def, LUPDATE_APPEND2, LUPDATE_def]) >>
  strip_tac >> gvs[] >> conj_tac
  >- (irule fresh_poke_lineage_inventory >> goal_assum (drule_at Any) >> simp[]) >>
  simp[stack_poke_def, MEM_LUPDATE]
QED

Theorem generate_phi_plan_lineage_inventory:
  !S ps inst next halting d v ops qs.
    lineage_inventory S ps /\
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
    stack_peek d ps.ps_stack = Var v /\
    Var (HD inst.inst_outputs) NOTIN S /\
    generate_phi_plan inst next halting ps = (ops,qs) ==>
    lineage_inventory
      (((if MEM v next then S else S DELETE (Var v)) UNION
        {Var (HD inst.inst_outputs)}) DIFF
       (if ~halting /\ ~MEM (HD inst.inst_outputs) next
        then {Var (HD inst.inst_outputs)} else {})) qs
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by
    (fs[stack_get_phi_depth_def] >> drule stack_find_bound >> simp[]) >>
  Cases_on `phi_write_phase inst next d ps` >>
  drule_all phi_write_phase_lineage_inventory >> strip_tac >>
  drule generate_phi_plan_write_phase >>
  disch_then (qspecl_then [`next`,`halting`] mp_tac) >> simp[] >>
  Cases_on `~halting /\ ~MEM (HD inst.inst_outputs) next` >> simp[]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      drule popmany_plan_lineage_inventory >>
      disch_then (qspec_then `[Var (HD inst.inst_outputs)]` mp_tac) >>
      `set [Var (HD inst.inst_outputs)] INTER set r.ps_stack =
        {Var (HD inst.inst_outputs)}` by (simp[EXTENSION] >> metis_tac[]) >>
      simp[dead_stack_marker_def]) >>
  strip_tac >> gvs[]
QED

(* Exact copy from genBlockSim, avoiding a frame-simulation import here. *)
Theorem stack_find_el[local]:
  !P l d. stack_find P l = SOME d ==> P (EL d l)
Proof
  Induct_on `l` >> simp[stack_find_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> gvs[arithmeticTheory.ADD1, EL_CONS]
QED

Theorem phi_selection_from_present_operand:
  !inst ps.
    (?v. MEM (Var v) inst.inst_operands /\ MEM (Var v) ps.ps_stack) ==>
    ?d v.
      stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
      stack_peek d ps.ps_stack = Var v /\ MEM (Var v) inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack`
  >- (gvs[stack_get_phi_depth_def, stack_find_NONE_EVERY, EVERY_MEM] >>
      first_x_assum (qspec_then `Var v` mp_tac) >>
      simp[MEM_FILTER, stackPlanTypesTheory.is_var_operand_def]) >>
  rename1 `stack_get_phi_depth _ _ = SOME d` >>
  `d < LENGTH ps.ps_stack /\
   MEM (stack_peek d ps.ps_stack) inst.inst_operands /\
   is_var_operand (stack_peek d ps.ps_stack)` by
    (gvs[stack_get_phi_depth_def] >>
     drule stack_find_bound >> simp[] >> strip_tac >>
     drule stack_find_el >>
     simp[MEM_FILTER, stack_peek_def, EL_REVERSE] >>
     `PRE (LENGTH ps.ps_stack - d) = LENGTH ps.ps_stack - (d+1)` by decide_tac >>
     simp[]) >>
  Cases_on `stack_peek d ps.ps_stack` >>
  gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]
QED
