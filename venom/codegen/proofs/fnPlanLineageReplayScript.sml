Theory fnPlanLineageReplay
Ancestors
  stackPlanGen stackModel list rich_list

Theorem stack_find_append_excluded:
  !xs ys p. EVERY (\x. ~p x) ys ==>
    stack_find p (xs ++ ys) = stack_find p xs
Proof
  Induct_on `xs` >> simp[stack_find_def] >> rpt strip_tac
  >- (Induct_on `ys` >> simp[stack_find_def] >> rpt strip_tac >> gvs[])
  >> Cases_on `p h` >> simp[stack_find_def] >>
     Cases_on `stack_find p xs` >> gvs[]
QED

Theorem stack_get_depth_bottom_excluded:
  !prefix core op. ~MEM op prefix ==>
    stack_get_depth op (prefix ++ core) = stack_get_depth op core
Proof
  rpt strip_tac >>
  simp[stack_get_depth_def, REVERSE_APPEND,
       stack_find_append_excluded, EVERY_MEM]
QED

Theorem stack_get_depth_bottom_dead:
  !op stk n. op <> dead_stack_marker ==>
    stack_get_depth op (REPLICATE n dead_stack_marker ++ stk) =
    stack_get_depth op stk
Proof
  rpt strip_tac >> irule stack_get_depth_bottom_excluded >> simp[]
QED

Theorem stack_swap_bottom_extension:
  !prefix stk d. d < LENGTH stk ==>
    stack_swap d (prefix ++ stk) = prefix ++ stack_swap d stk
Proof
  rpt strip_tac >>
  `LENGTH (prefix ++ stk) - 1 = LENGTH prefix + (LENGTH stk - 1)` by
    simp[] >>
  `LENGTH (prefix ++ stk) - 1 - d =
     LENGTH prefix + (LENGTH stk - 1 - d)` by simp[] >>
  simp[stack_swap_def, EL_APPEND2, LUPDATE_APPEND2]
QED

Theorem cleanup_elision_safe_without_height[simp]:
  !growth cfg fn bb h. ~cleanup_elision_safe NONE growth cfg fn bb h
Proof
  simp[cleanup_elision_safe_def, cleanup_height_safe_def]
QED

(* The PHI rename-only boundary does not demand distinct incoming operands. *)
Theorem generate_phi_plan_rename_only:
  !inst next halting ps d.
    stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
      SOME d /\
    ~MEM (operand_to_string (stack_peek d ps.ps_stack)) next /\
    (halting \/ MEM (HD inst.inst_outputs) next) ==>
    generate_phi_plan inst next halting ps =
      ([SOPoke d (Var (HD inst.inst_outputs))],
       ps with ps_stack := stack_poke d (Var (HD inst.inst_outputs)) ps.ps_stack)
Proof
  rpt strip_tac >> simp[generate_phi_plan_def]
QED

Theorem release_dead_spills_live_domain:
  !next ps.
    (!op. op IN FDOM ps.ps_spilled ==> ?v. op = Var v /\ MEM v next) ==>
    release_dead_spills next ps = ps
Proof
  rpt strip_tac >>
  simp[stackPlanOpsTheory.release_dead_spills_def] >>
  `FILTER (\(op,off). case op of Var v => ~MEM v next | _ => T)
     (alist$fmap_to_alist ps.ps_spilled) = []` suffices_by simp[] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  Cases >> simp[] >> rpt strip_tac >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `op IN FDOM ps.ps_spilled` by
    (qpat_x_assum `FLOOKUP _ _ = SOME _` mp_tac >>
     simp[finite_mapTheory.FLOOKUP_DEF] >> IF_CASES_TAC >> simp[]) >>
  first_x_assum drule >> strip_tac >> gvs[]
QED
