Theory fnPlanLineagePhiInventory
Ancestors
  fnPlanLineagePhiTemporal fnPlanLineageInventory planAlign stackPlanGen
  stackPlanOps stackModel sorting list rich_list

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
         irule reorderSimTheory.stack_swap_mem_subset >>
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
