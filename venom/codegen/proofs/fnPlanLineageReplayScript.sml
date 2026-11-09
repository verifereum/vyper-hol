Theory fnPlanLineageReplay
Ancestors
  stackPlanGen stackPlanOps stackPlanTypes stackModel list rich_list

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

(* Instruction planning cannot inspect cleanup bookkeeping.  These operation
   boundaries keep that fact separate from stack-layout replay. *)
Theorem do_spill_tos_cleanup_update:
  !ps h g b.
    do_spill_tos (ps with <|ps_cleanup_height := h; ps_cleanup_growth := g;
                            ps_cleanup_promised := b|>) =
    (FST (do_spill_tos ps), SND (do_spill_tos ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  simp[do_spill_tos_def] >> rpt gen_tac >> pairarg_tac >>
  simp[plan_state_component_equality]
QED

Theorem do_restore_cleanup_update:
  !op ps h g b.
    do_restore op (ps with <|ps_cleanup_height := h; ps_cleanup_growth := g;
                            ps_cleanup_promised := b|>) =
    (FST (do_restore op ps), SND (do_restore op ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[plan_state_component_equality]
QED

Theorem do_spill_at_cleanup_update:
  !d ps h g b.
    do_spill_at d (ps with <|ps_cleanup_height := h; ps_cleanup_growth := g;
                            ps_cleanup_promised := b|>) =
    (FST (do_spill_at d ps), SND (do_spill_at d ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> Cases_on `alloc_spill_slot ps.ps_alloc` >>
  Cases_on `d = 0` >>
  simp[do_spill_at_def, do_spill_tos_def, plan_state_component_equality]
QED

Theorem do_swap_cleanup_update:
  !d ps h g b.
    do_swap d (ps with <|ps_cleanup_height := h; ps_cleanup_growth := g;
                        ps_cleanup_promised := b|>) =
    (FST (do_swap d ps), SND (do_swap d ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  Cases_on `d = 0` >- simp[plan_state_component_equality] >>
  Cases_on `d <= 16` >- simp[plan_state_component_equality] >>
  simp[] >> pairarg_tac >> simp[plan_state_component_equality]
QED

Theorem do_dup_cleanup_update:
  !d ps h g b.
    do_dup d (ps with <|ps_cleanup_height := h; ps_cleanup_growth := g;
                       ps_cleanup_promised := b|>) =
    (FST (do_dup d ps), SND (do_dup d ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  Cases_on `d <= 15` >- simp[plan_state_component_equality] >>
  simp[] >> pairarg_tac >> simp[plan_state_component_equality]
QED

Theorem restore_spilled_plan_cleanup_update:
  !xs ps h g b.
    restore_spilled_plan xs (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (restore_spilled_plan xs ps), SND (restore_spilled_plan xs ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  Induct_on `xs` >- simp[restore_spilled_plan_def] >>
  rpt gen_tac >> simp[restore_spilled_plan_def, do_restore_cleanup_update] >>
  Cases_on `do_restore h ps` >> simp[pairTheory.UNCURRY_VAR]
QED

Theorem reduce_depth_plan_cleanup_update:
  !fuel targets op f n ps h g b.
    reduce_depth_plan fuel targets op f n (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (reduce_depth_plan fuel targets op f n ps),
     SND (reduce_depth_plan fuel targets op f n ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  Induct_on `fuel` >> rpt gen_tac >>
  simp[reduce_depth_plan_def, do_spill_at_cleanup_update, pairTheory.UNCURRY_VAR] >>
  rpt CASE_TAC >> simp[do_spill_at_cleanup_update, pairTheory.UNCURRY_VAR]
QED

