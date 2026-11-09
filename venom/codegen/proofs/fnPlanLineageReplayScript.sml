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


Theorem pair_bind_transport:
  !U k p p'.
    p' = (FST p, U (SND p)) /\
    (!a t. k a (U t) = (FST (k a t), U (SND (k a t)))) ==>
    UNCURRY k p' = (FST (UNCURRY k p), U (SND (UNCURRY k p)))
Proof
  rpt strip_tac >> simp[pairTheory.UNCURRY_VAR]
QED

Theorem reorder_one_cleanup_update:
  !dfg targets idx op ps h g b.
    reorder_one dfg targets idx op (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (reorder_one dfg targets idx op ps),
     SND (reorder_one dfg targets idx op ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >>
  simp[reorder_one_def, Excl "LET_THM"] >>
  irule (BETA_RULE (Q.ISPEC `(\s:plan_state. s with
    <|ps_cleanup_height := h; ps_cleanup_growth := g;
      ps_cleanup_promised := b|>)` pair_bind_transport)) >>
  reverse conj_tac
  >- (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
        (LENGTH targets) ps.ps_stack` >>
      Cases_on `FLOOKUP ps.ps_spilled op` >>
      simp[do_restore_cleanup_update]) >>
  rpt gen_tac >> simp[Excl "LET_THM"] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) t.ps_stack` >> simp[Excl "LET_THM"] >>
  irule (BETA_RULE (Q.ISPEC `(\s:plan_state. s with
    <|ps_cleanup_height := h; ps_cleanup_growth := g;
      ps_cleanup_promised := b|>)` pair_bind_transport)) >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[reduce_depth_plan_cleanup_update]) >>
  rpt gen_tac >> simp[Excl "LET_THM"] >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
    (LENGTH targets) t'.ps_stack` >> simp[Excl "LET_THM"] >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `LENGTH targets < idx + (LENGTH t'.ps_stack + 1) /\
            0 < LENGTH t'.ps_stack` >>
  simp[Excl "LET_THM"] >>
  TRY (IF_CASES_TAC >- simp[]) >> simp[Excl "LET_THM"] >>
  irule (BETA_RULE (Q.ISPEC `(\s:plan_state. s with
    <|ps_cleanup_height := h; ps_cleanup_growth := g;
      ps_cleanup_promised := b|>)` pair_bind_transport)) >>
  reverse conj_tac >- simp[do_swap_cleanup_update] >>
  rpt gen_tac >> simp[do_swap_cleanup_update, pairTheory.UNCURRY_VAR]
QED

Theorem reorder_plan_cleanup_update:
  !dfg targets ps h g b.
    reorder_plan dfg targets (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (reorder_plan dfg targets ps), SND (reorder_plan dfg targets ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[reorder_plan_def] >>
  qspec_tac (`MAPi (\i op. (i,op)) targets`, `items`) >>
  qspec_tac (`[]:stack_op list`, `ops`) >> qid_spec_tac `ps` >>
  Induct_on `items` >- simp[] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[reorder_one_cleanup_update] >>
  Cases_on `reorder_one dfg targets h'0 h'1 ps` >>
  simp[pairTheory.UNCURRY_VAR]
QED

Theorem release_dead_spills_cleanup_update:
  !next ps h g b.
    release_dead_spills next (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    release_dead_spills next ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>
Proof
  rpt gen_tac >> simp[release_dead_spills_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL _ _ dead` >>
  qid_spec_tac `ps` >> qid_spec_tac `dead` >>
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h'` >>
  simp[] >>
  first_x_assum (qspec_then `ps' with
    <|ps_spilled := ps'.ps_spilled \\ h'0;
      ps_alloc := free_spill_slot h'1 ps'.ps_alloc|>` mp_tac) >>
  simp[]
QED

Theorem popmany_individual_cleanup_update:
  !xs ps h g b.
    popmany_individual xs (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (popmany_individual xs ps), SND (popmany_individual xs ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[popmany_individual_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL step _ sorted` >>
  qid_spec_tac `ps` >> qspec_tac (`[]:stack_op list`, `ops`) >>
  qid_spec_tac `sorted` >> Induct >> simp[] >> rpt gen_tac >>
  simp[Abbr `step`, Excl "LET_THM"] >>
  Cases_on `stack_get_depth h' ps'.ps_stack` >> simp[Excl "LET_THM"] >>
  IF_CASES_TAC
  >- (simp[] >> first_x_assum (qspecl_then
        [`ops ++ [SOPop 1]`, `ps' with ps_stack := stack_pop 1 ps'.ps_stack`] mp_tac) >>
      simp[]) >>
  Cases_on `do_swap x ps'` >> simp[do_swap_cleanup_update] >>
  first_x_assum (qspecl_then
    [`ops ++ q ++ [SOPop 1]`, `r with ps_stack := stack_pop 1 r.ps_stack`] mp_tac) >>
  simp[]
QED

Theorem popmany_plan_cleanup_update:
  !xs ps h g b.
    popmany_plan xs (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (popmany_plan xs ps), SND (popmany_plan xs ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  Cases >> rpt gen_tac >> simp[popmany_plan_def, Excl "LET_THM"] >>
  IF_CASES_TAC >> simp[popmany_individual_cleanup_update, Excl "LET_THM"] >>
  IF_CASES_TAC >> simp[popmany_individual_cleanup_update, Excl "LET_THM"] >>
  Cases_on `do_swap (SUC (LENGTH t)) ps` >>
  simp[do_swap_cleanup_update]
QED

Theorem emit_one_input_cleanup_update:
  !opc next op ps h g b.
    emit_one_input opc next op (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (emit_one_input opc next op ps), SND (emit_one_input opc next op ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[emit_one_input_def, Excl "LET_THM"] >>
  irule (BETA_RULE (Q.ISPEC `(\s:plan_state. s with
    <|ps_cleanup_height := h; ps_cleanup_growth := g;
      ps_cleanup_promised := b|>)` pair_bind_transport)) >>
  reverse conj_tac >- (IF_CASES_TAC >> simp[do_restore_cleanup_update]) >>
  rpt gen_tac >> Cases_on `op` >> simp[Excl "LET_THM"] >>
  rpt (IF_CASES_TAC >> simp[Excl "LET_THM"]) >>
  Cases_on `stack_get_depth (Var s) t.ps_stack` >> simp[Excl "LET_THM"] >>
  Cases_on `do_dup x t` >> simp[do_dup_cleanup_update]
QED

Theorem emit_input_plan_cleanup_update:
  !xs opc next ps h g b.
    emit_input_plan opc xs next (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (emit_input_plan opc xs next ps), SND (emit_input_plan opc xs next ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  Induct >> rpt gen_tac >> simp[emit_input_plan_def, Excl "LET_THM"] >>
  Cases_on `emit_one_input opc (operand_vars xs ++ next) h ps` >>
  simp[emit_one_input_cleanup_update, Excl "LET_THM"] >>
  Cases_on `emit_input_plan opc xs next r` >> simp[]
QED

Theorem optimistic_swap_plan_cleanup_update:
  !dfg inst next term ps h g b.
    optimistic_swap_plan dfg inst next term (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (optimistic_swap_plan dfg inst next term ps),
     SND (optimistic_swap_plan dfg inst next term ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST next)) ps.ps_stack` >>
  simp[do_swap_cleanup_update]
QED

Theorem generate_offset_plan_cleanup_update:
  !inst ps h g b.
    generate_offset_plan inst (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (generate_offset_plan inst ps), SND (generate_offset_plan inst ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> simp[generate_offset_plan_def] >>
  Cases_on `EL 1 inst.inst_operands` >> simp[]
QED

Theorem generate_emit_ops_cleanup_update:
  !inst topics ps h g b.
    generate_emit_ops inst topics (ps with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>) =
    (FST (generate_emit_ops inst topics ps), SND (generate_emit_ops inst topics ps) with
      <|ps_cleanup_height := h; ps_cleanup_growth := g; ps_cleanup_promised := b|>)
Proof
  rpt gen_tac >> Cases_on `venom_to_evm_name inst.inst_opcode` >>
  simp[generate_emit_ops_def, fresh_label_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED
