(*
 * One instruction's step preserves the slot alias invariant of the block
 * induction (fnAliasInv): every operand on the planner's stack or in its
 * spill map has the value of its ASSIGN-chain root (normalize_operand),
 * read through the frame view.  The block body (fnBlockBody) carries it
 * from instruction to instruction; lineage_alias_successor carries it
 * across a whole block from the block's entry.
 *
 * TOP-LEVEL:
 *   alias_step_preserve - an instruction whose step is OK keeps the
 *                         invariant from its planner state to the next
 *)

Theory fnAliasStep
Ancestors
  fnAliasInv reorderSim frameRel codegenRel unitShapeDefs stackPlanGen
  stackPlanOps stackPlanTypes venomExecSemantics venomState livenessDefs
  dfgDefs cfgDefs deepResidualBudget fnFrameStepsRevertForward frameViewFacts
  venomExecProps venomInstProps planWf stackModel foldlSim
  list rich_list finite_map pred_set

(* ===== Slot provenance: the planner manufactures no operand ===== *)

Theorem restore_spilled_plan_inventory_subset:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[do_restore_inventory_subset]
QED

(* A restore moves its operand from the spill map to the stack. *)
Theorem do_restore_inventory_count[local]:
  !op ps ops ps'.
    do_restore op ps = (ops,ps') ==>
    (!x. LIST_ELEM_COUNT x ps'.ps_stack +
           (if x IN FDOM ps'.ps_spilled then 1 else 0) =
         LIST_ELEM_COUNT x ps.ps_stack +
           (if x IN FDOM ps.ps_spilled then 1 else 0)) /\
    op NOTIN FDOM ps'.ps_spilled /\
    FDOM ps'.ps_spilled SUBSET FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
  >- (strip_tac >> gvs[FLOOKUP_DEF]) >>
  strip_tac >> gvs[stack_push_def, SNOC_APPEND, LIST_ELEM_COUNT_DEF,
                   FILTER_APPEND, FLOOKUP_DEF, SUBSET_DEF] >>
  rw[] >> gvs[]
QED

Theorem restore_spilled_plan_inventory_count[local]:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') ==>
    (!x. LIST_ELEM_COUNT x ps'.ps_stack +
           (if x IN FDOM ps'.ps_spilled then 1 else 0) =
         LIST_ELEM_COUNT x ps.ps_stack +
           (if x IN FDOM ps.ps_spilled then 1 else 0)) /\
    (!x. MEM x targets ==> x NOTIN FDOM ps'.ps_spilled) /\
    FDOM ps'.ps_spilled SUBSET FDOM ps.ps_spilled
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule do_restore_inventory_count >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rpt conj_tac
  >- (gen_tac >>
      qpat_x_assum `!x. LIST_ELEM_COUNT x ps1.ps_stack + _ = _`
        (qspec_then `x` (SUBST1_TAC o SYM)) >>
      qpat_x_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
        (qspec_then `x` ACCEPT_TAC))
  >- (rpt strip_tac >> gvs[SUBSET_DEF] >> metis_tac[])
  >> metis_tac[SUBSET_TRANS]
QED

(* The join reorder's target stack fits on the stack once its spilled
   operands are restored. *)
Theorem restore_spilled_plan_length_floor:
  !targets ps ops ps'.
    restore_spilled_plan targets ps = (ops,ps') /\
    pending_inventory_wf targets ps ==>
    LENGTH targets <= LENGTH ps'.ps_stack
Proof
  rpt strip_tac >> drule restore_spilled_plan_inventory_count >> strip_tac >>
  irule list_elem_count_dom_length >> gen_tac >>
  Cases_on `MEM x targets`
  >- (`LIST_ELEM_COUNT x targets <=
       LIST_ELEM_COUNT x ps.ps_stack +
         (if x IN FDOM ps.ps_spilled then 1 else 0)` by
        fs[pending_inventory_wf_def] >>
      `x NOTIN FDOM ps'.ps_spilled` by metis_tac[] >>
      qpat_x_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
        (qspec_then `x` mp_tac) >> simp[]) >>
  `LIST_ELEM_COUNT x targets = 0` by
    (CCONTR_TAC >>
     `LIST_ELEM_COUNT x targets > 0` by decide_tac >>
     metis_tac[LIST_ELEM_COUNT_MEM]) >>
  simp[]
QED

Theorem reorder_restore_length_mono[local]:
  !op f n ps ops ps'.
    (case stack_get_unfixed_depth op f n ps.ps_stack of
       SOME _ => ([],ps)
     | NONE => case FLOOKUP ps.ps_spilled op of
                 SOME _ => do_restore op ps | NONE => ([],ps)) = (ops,ps') ==>
    LENGTH ps.ps_stack <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `do_restore _ _ = _` mp_tac >>
  simp[do_restore_def] >> strip_tac >> gvs[stack_push_def]
QED

(* reorder_one keeps the target window on the stack, with no bound on the
   number of targets. *)
Theorem reorder_one_length_floor:
  !dfg tops idx op ps ops ps'.
    idx < LENGTH tops /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_one dfg tops idx op ps = (ops,ps') ==>
    LENGTH tops <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> gvs[] >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    (drule reorder_restore_length_mono >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps1.ps_stack = SOME dist` >>
  pairarg_tac >> simp[] >>
  `LENGTH tops <= LENGTH ps2.ps_stack` by
    (Cases_on `dist > 16` >> gvs[] >>
     drule reduce_depth_plan_target_len_floor >> simp[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH tops - (idx + 1)) (LENGTH tops) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack` by metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH tops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH tops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH tops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[stack_poke_def]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >>
     asm_simp_tac (srw_ss()) []) >>
  strip_tac >> gvs[] >>
  `LENGTH tops - (idx + 1) < LENGTH ps3.ps_stack` by decide_tac >>
  qspecl_then [`LENGTH tops - (idx + 1)`, `ps3`] mp_tac do_swap_length >>
  asm_simp_tac (srw_ss()) []
QED

Theorem plan_steps_reorder_inventory_subset_nb[local]:
  !items dfg tops ps ops ps'.
    EVERY (\(idx,op). idx < LENGTH tops) items /\
    LENGTH tops <= LENGTH ps.ps_stack /\
    plan_steps (\(idx,op) ps. reorder_one dfg tops idx op ps) items ps =
      (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Induct >> simp[plan_steps_def] >> rpt gen_tac >>
  Cases_on `h` >> rename1 `(idx,op)` >> simp[] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg tops idx op ps = (step_ops,ps1)` >>
  `LENGTH tops <= LENGTH ps1.ps_stack` by
    metis_tac[reorder_one_length_floor] >>
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled` by
    metis_tac[reorder_one_inventory_subset_nb] >>
  rpt strip_tac >>
  `MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled` by
    (first_x_assum (qspecl_then [`dfg`, `tops`, `ps1`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  metis_tac[]
QED

(* reorder_plan manufactures no operand, with no bound on the number of
   targets. *)
Theorem reorder_plan_inventory_subset_nb:
  !dfg tops ps ops ps'.
    LENGTH tops <= LENGTH ps.ps_stack /\
    reorder_plan dfg tops ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,op). idx < LENGTH tops) (MAPi (\i op. (i,op)) tops)` by
    (simp[EVERY_MEM, pairTheory.FORALL_PROD, indexedListsTheory.MEM_MAPi] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `reorder_plan _ _ _ = _`
    (assume_tac o REWRITE_RULE [reorder_plan_eq_plan_steps]) >>
  metis_tac[plan_steps_reorder_inventory_subset_nb]
QED

Theorem foldl_plan_inventory_subset[local]:
  !(f : 'a # plan_state -> 'b -> 'a # plan_state) items acc.
    (!acc x at.
       MEM at (SND (f acc x)).ps_stack \/ at IN FDOM (SND (f acc x)).ps_spilled ==>
       MEM at (SND acc).ps_stack \/ at IN FDOM (SND acc).ps_spilled) ==>
    !at. MEM at (SND (FOLDL f acc items)).ps_stack \/
         at IN FDOM (SND (FOLDL f acc items)).ps_spilled ==>
         MEM at (SND acc).ps_stack \/ at IN FDOM (SND acc).ps_spilled
Proof
  ntac 2 gen_tac >> Induct_on `items` >> simp[] >> metis_tac[]
QED

Theorem popmany_individual_inventory_subset:
  !to_pop ps ops ps'.
    popmany_individual to_pop ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `FOLDL f acc0 sorted` >>
  `ps' = SND (FOLDL f acc0 sorted) /\ ps = SND acc0` by
    gvs[Abbr `acc0`] >>
  pop_assum SUBST1_TAC >> pop_assum SUBST1_TAC >>
  match_mp_tac foldl_plan_inventory_subset >>
  simp[Abbr `f`, pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  Cases_on `stack_get_depth x p_2.ps_stack` >> simp[] >>
  rename1 `stack_get_depth x p_2.ps_stack = SOME dist` >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `dist = 0` >> simp[]
  >- (simp[stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  pairarg_tac >> simp[stack_pop_def] >> strip_tac >>
  `MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled` by
    metis_tac[MEM_TAKE] >>
  metis_tac[do_swap_inventory_subset]
QED

Theorem popmany_plan_inventory_subset:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  Cases
  >- (simp[popmany_plan_def] >> rpt strip_tac >> gvs[]) >>
  simp[popmany_plan_def] >> rpt gen_tac >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_inventory_subset] >>
  reverse IF_CASES_TAC
  >- metis_tac[popmany_individual_inventory_subset] >>
  qmatch_asmsub_abbrev_tac `is_contiguous_top depths` >>
  `!v. IS_SOME (stack_get_depth v ps.ps_stack) ==>
       THE (stack_get_depth v ps.ps_stack) < LENGTH ps.ps_stack` by
    (rpt strip_tac >> Cases_on `stack_get_depth v ps.ps_stack` >> gvs[] >>
     drule stack_get_depth_props >> simp[]) >>
  `!d. MEM d depths ==> d < LENGTH ps.ps_stack` by
    (simp[Abbr `depths`, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     gvs[EVERY_MEM, MEM_MAP, PULL_EXISTS] >> metis_tac[]) >>
  `MEM (SUC (LENGTH t)) depths` by
    (`LENGTH depths = SUC (LENGTH t)` by simp[Abbr `depths`] >>
     `MEM (SUC (LENGTH t)) (QSORT (\a b. a <= b) depths)` by
       gvs[is_contiguous_top_def, LET_THM, MEM_GENLIST] >>
     metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]) >>
  `SUC (LENGTH t) < LENGTH ps.ps_stack` by metis_tac[] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[stack_pop_def] >>
  rpt strip_tac >>
  `MEM at ps''.ps_stack \/ at IN FDOM ps''.ps_spilled` by
    metis_tac[MEM_TAKE] >>
  metis_tac[do_swap_inventory_subset]
QED

Theorem optimistic_swap_plan_inventory_subset:
  !dfg inst nl nt ps ops ps'.
    optimistic_swap_plan dfg inst nl nt ps = (ops,ps') ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
         MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  strip_tac >> gen_tac >> disch_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  drule stack_get_depth_props >> strip_tac >>
  metis_tac[do_swap_inventory_subset]
QED

Theorem release_dead_spills_inventory_subset:
  !nl ps at.
    MEM at (release_dead_spills nl ps).ps_stack \/
    at IN FDOM (release_dead_spills nl ps).ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
Proof
  `!(f : plan_state -> operand # num -> plan_state) l ps.
     (!ps x. (f ps x).ps_stack = ps.ps_stack /\
             FDOM (f ps x).ps_spilled SUBSET FDOM ps.ps_spilled) ==>
     (FOLDL f ps l).ps_stack = ps.ps_stack /\
     FDOM (FOLDL f ps l).ps_spilled SUBSET FDOM ps.ps_spilled` by
    (ntac 2 gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
     metis_tac[SUBSET_TRANS]) >>
  rpt gen_tac >> simp[release_dead_spills_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL f ps dead` >>
  `(FOLDL f ps dead).ps_stack = ps.ps_stack /\
   FDOM (FOLDL f ps dead).ps_spilled SUBSET FDOM ps.ps_spilled` by
    (first_x_assum irule >>
     simp[Abbr `f`, pairTheory.FORALL_PROD, SUBSET_DEF]) >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem generate_emit_ops_slots:
  !inst ltc ps ops ps'.
    generate_emit_ops inst ltc ps = (ops, ps') ==>
    ps'.ps_stack = ps.ps_stack /\ ps'.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode = JNZ` >> gvs[]
  >- (BasicProvers.every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = JMP` >> gvs[]
  >- (BasicProvers.every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = DJMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[]
  >- (Cases_on `HD inst.inst_operands` >> gvs[] >>
      pairarg_tac >> gvs[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = RET` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE` >> gvs[]
  >- (pairarg_tac >> gvs[fresh_label_def]) >>
  Cases_on `inst.inst_opcode = LOG` >> gvs[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = BUMP` >> gvs[]
QED

Theorem foldl_push_outputs_inventory[local]:
  !outs ps at.
    MEM at (FOLDL (\ps' out. ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
              ps outs).ps_stack \/
    at IN FDOM (FOLDL (\ps' out. ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
              ps outs).ps_spilled ==>
    MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
    ?out. MEM out outs /\ at = Var out
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then
    [`ps with ps_stack := stack_push (Var h) ps.ps_stack`, `at`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  simp[stack_push_def, MEM_SNOC] >> metis_tac[]
QED

(* Every slot a regular instruction's plan leaves is a slot of its input
   state, one of its stack operands, or one of its outputs. *)
Theorem generate_regular_inst_plan_inventory:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      (ops,ps') /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!target_ops. inst.inst_opcode = JMP /\
       join_target_ops liveness fn bbl inst = SOME target_ops ==>
       pending_inventory_wf target_ops ps) ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
      MEM at (compute_operands inst) \/
      ?out. MEM out inst.inst_outputs /\ at = Var out
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  (* input emission *)
  `!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
        MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
        MEM at (compute_operands inst)` by
    metis_tac[emit_input_plan_inventory_subset] >>
  (* join reorder *)
  `(!at. MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled ==>
         MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled) /\
   LENGTH (compute_operands inst) <= LENGTH ps2.ps_stack` by
    (qpat_x_assum `(if _ then _ else _) = (join_ops,ps2)` mp_tac >>
     IF_CASES_TAC
     >- (BasicProvers.TOP_CASE_TAC
         >- (simp[] >> strip_tac >> gvs[] >>
             metis_tac[available_input_plan_length]) >>
         rename1 `join_target_ops _ _ _ _ = SOME target_ops` >>
         rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
         `pending_inventory_wf target_ops ps` by metis_tac[] >>
         `compute_operands inst = []` by
           (qpat_x_assum `join_target_ops _ _ _ _ = _` mp_tac >>
            simp[join_target_ops_def, AllCaseEqs()] >> strip_tac >>
            gvs[compute_operands_def, asmIRTheory.get_non_label_operands_def]) >>
         gvs[] >>
         rename1 `restore_spilled_plan target_ops ps = (restore_ops,ps1')` >>
         `LENGTH target_ops <= LENGTH ps1'.ps_stack` by
           metis_tac[restore_spilled_plan_length_floor] >>
         metis_tac[reorder_plan_inventory_subset_nb,
                   restore_spilled_plan_inventory_subset]) >>
     simp[] >> strip_tac >> gvs[] >>
     metis_tac[available_input_plan_length]) >>
  (* operand reorder, possibly commuted *)
  `!l rops rps. LENGTH l = LENGTH (compute_operands inst) /\
     reorder_plan dfg l ps2 = (rops,rps) ==>
     !at. MEM at rps.ps_stack \/ at IN FDOM rps.ps_spilled ==>
          MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (rpt gen_tac >> strip_tac >>
     `LENGTH l <= LENGTH ps2.ps_stack` by decide_tac >>
     metis_tac[reorder_plan_inventory_subset_nb]) >>
  `!at. MEM at ps4.ps_stack \/ at IN FDOM ps4.ps_spilled ==>
        MEM at ps2.ps_stack \/ at IN FDOM ps2.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (reorder_ops,ps4)` mp_tac >>
     IF_CASES_TAC
     >- (IF_CASES_TAC >> strip_tac >> gvs[]
         >- metis_tac[] >>
         `LENGTH (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
            [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
             EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) =
          LENGTH (compute_operands inst)` by
           (fs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> rw[] >> fs[]) >>
         metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  (* pop operands, push outputs, emit *)
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc ps6 = (emit_ops,ps7)` >>
  `!at. MEM at ps7.ps_stack \/ at IN FDOM ps7.ps_spilled ==>
        MEM at ps4.ps_stack \/ at IN FDOM ps4.ps_spilled \/
        ?out. MEM out inst.inst_outputs /\ at = Var out` by
    (drule generate_emit_ops_slots >> strip_tac >> simp[] >>
     rpt strip_tac >>
     qspecl_then [`inst.inst_outputs`,
       `ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack`,
       `at`] mp_tac foldl_push_outputs_inventory >>
     (impl_tac >- gvs[Abbr `ps6`]) >>
     simp[stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  (* post-processing *)
  IF_CASES_TAC
  >- (strip_tac >> gvs[] >> rpt strip_tac >>
      metis_tac[release_dead_spills_inventory_subset]) >>
  `!at. MEM at ps8.ps_stack \/ at IN FDOM ps8.ps_spilled ==>
        MEM at ps7.ps_stack \/ at IN FDOM ps7.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >> strip_tac >> gvs[] >>
     metis_tac[popmany_plan_inventory_subset]) >>
  `!at. MEM at ps9.ps_stack \/ at IN FDOM ps9.ps_spilled ==>
        MEM at ps8.ps_stack \/ at IN FDOM ps8.ps_spilled` by
    (qpat_x_assum `(if _ then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_inventory_subset]) >>
  strip_tac >> gvs[] >> rpt strip_tac >>
  metis_tac[release_dead_spills_inventory_subset]
QED

Theorem generate_inst_plan_inventory:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      SOME (ops,ps') /\
    inst.inst_opcode <> PHI /\
    (inst.inst_opcode = OFFSET ==> ?out. inst.inst_outputs = [out]) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!target_ops. inst.inst_opcode = JMP /\
       join_target_ops liveness fn bbl inst = SOME target_ops ==>
       pending_inventory_wf target_ops ps) ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
      ~is_var_operand at \/
      ?out. MEM out inst.inst_outputs /\ at = Var out
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (`?out. inst.inst_outputs = [out]` by metis_tac[] >>
      gvs[generate_inst_plan_def, generate_offset_plan_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[stack_push_def, MEM_SNOC]) >>
  Cases_on `is_param_opcode inst.inst_opcode`
  >- (gvs[generate_inst_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (gvs[generate_inst_plan_def, AllCaseEqs()] >> metis_tac[]) >>
  `generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
     (ops,ps')` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM, AllCaseEqs()]) >>
  qspecl_then [`liveness`,`dfg`,`cfg`,`fn`,`inst`,`nl`,`ih`,`nit`,`bbl`,
               `ps`,`ops`,`ps'`] mp_tac generate_regular_inst_plan_inventory >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!at. _ ==> _ \/ _ \/ MEM at (compute_operands inst) \/ _`
    (qspec_then `at` mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >> simp[] >>
  Cases_on `is_var_operand at` >> simp[] >> metis_tac[]
QED

(* ===== Values: an OK step changes only its outputs ===== *)

Theorem step_inst_ok_non_output_lookup:
  !fuel ctx inst vs vs1 v.
    step_inst fuel ctx inst vs = OK vs1 /\ ~MEM v inst.inst_outputs ==>
    FLOOKUP vs1.vs_vars v = FLOOKUP vs.vs_vars v
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all venomExecPropsTheory.step_terminator_preserves_vars >>
      simp[lookup_var_def]) >>
  drule_all venomInstPropsTheory.step_preserves_non_output_vars >>
  simp[lookup_var_def]
QED

Theorem frame_view_non_output_val:
  !fuel ctx inst vs vs1 fn ra lo op.
    step_inst fuel ctx inst vs = OK vs1 /\
    (!v. op = Var v ==> ~MEM v inst.inst_outputs) ==>
    operand_val (frame_view fn ra vs1) lo op =
    operand_val (frame_view fn ra vs) lo op
Proof
  rpt strip_tac >> Cases_on `op` >> simp[operand_val_def, frame_view_vars_lookup] >>
  rename1 `FLOOKUP vs1.vs_vars x` >>
  `FLOOKUP vs1.vs_vars x = FLOOKUP vs.vs_vars x` by
    (irule step_inst_ok_non_output_lookup >> metis_tac[]) >>
  simp[]
QED

(* Used at each instruction of the block body whose step is OK: every
   non-terminator (INVOKE included), and a JMP or JNZ, after which ps' is
   the state the successor's lineage entry inherits its stack and spill
   map from.  Its static premises are fnBlockPlanStatic's
   block_plan_state_static conclusions.  The label premise is needed at
   vs only: operand_val reads labels from lo, but an ASSIGN of a label
   gives its output the value vs_labels has.

   Why it should hold: a step that is OK changes no variable but inst's
   outputs (step_inst_base; INVOKE binds its outputs into the caller's
   state, merge_callee_state).  By the freshness premise, no slot of ps
   is an output or has one as its root, so each slot of ps keeps both
   values.  Each slot of ps' is a slot of ps (moved, duplicated, restored
   or spilled), a literal or label (its own root, as is
   dead_stack_marker), or an output of inst.  The emitted operands are
   owned (ownership premise), and a JMP's join reorder may relabel an
   equivalent slot as a target variable, which pending_inventory_wf keeps
   to variables the state holds.  An output's root is itself unless inst
   is an ASSIGN (dfg_build_function and SSA make inst its dfg_defs
   entry); an ASSIGN's output takes its operand's value: an owned
   variable's, which is its root's by the invariant at vs; a literal; or
   a label's, which is lo's by the label premise.  Return-PC variables are
   copied only into return-PC variables (retpc_shape_ok), so the frame
   view reads ra on both sides of such an ASSIGN. *)
Theorem alias_step_preserve:
  !fuel ctx lo fn ra liveness dfg cfg inst next_live is_halting next_is_term
   bb_label ps ops ps' vs vs1.
    dfg = dfg_build_function fn /\ codegen_ready_fn fn /\ retpc_shape_ok fn /\
    MEM inst (fn_insts fn) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v inst.inst_outputs) /\
    (inst.inst_opcode = JMP ==>
     !target target_bb target_stack.
       inst.inst_operands = [Label target] /\
       lookup_block target fn.fn_blocks = SOME target_bb /\
       target_stack =
         MAP Var (input_vars_from bb_label target_bb.bb_instructions
                    (live_vars_at liveness target 0)) ==>
       pending_inventory_wf target_stack ps) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    generate_inst_plan liveness dfg cfg fn inst next_live is_halting
      next_is_term bb_label ps = SOME (ops, ps') /\
    step_inst fuel ctx inst vs = OK vs1
    ==>
    !at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
      operand_val (frame_view fn ra vs1) lo at =
      operand_val (frame_view fn ra vs1) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[step_inst_non_invoke, Once step_inst_base_def]) >>
  `inst.inst_opcode = OFFSET ==> ?out. inst.inst_outputs = [out]` by
    (strip_tac >>
     qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
     gvs[step_inst_non_invoke, Once step_inst_base_def, exec_pure2_def,
         AllCaseEqs()] >> strip_tac >> simp[]) >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. MEM op (compute_operands inst) /\ _ ==> IS_SOME _ \/ _`
       (qspec_then `op` mp_tac) >>
     impl_tac >- metis_tac[] >>
     Cases_on `stack_get_depth op ps.ps_stack` >> simp[FLOOKUP_DEF]
     >- (IF_CASES_TAC >> simp[]) >>
     drule stack_get_depth_props >> metis_tac[stack_peek_mem]) >>
  `!target_ops. inst.inst_opcode = JMP /\
     join_target_ops liveness fn bb_label inst = SOME target_ops ==>
     pending_inventory_wf target_ops ps` by
    (rpt strip_tac >> gvs[join_target_ops_def, AllCaseEqs()] >>
     metis_tac[]) >>
  `!at. MEM at ps'.ps_stack \/ at IN FDOM ps'.ps_spilled ==>
     MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
     ~is_var_operand at \/
     ?out. MEM out inst.inst_outputs /\ at = Var out` by
    (qspecl_then [`liveness`,`dfg_build_function fn`,`cfg`,`fn`,`inst`,
                  `next_live`,`is_halting`,`next_is_term`,`bb_label`,`ps`,
                  `ops`,`ps'`] mp_tac generate_inst_plan_inventory >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!at. MEM at ps'.ps_stack \/ _ ==> _ \/ _ \/ ~is_var_operand at \/ _`
    (qspec_then `at` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
  >~ [`~is_var_operand at`]
  >- (Cases_on `at` >> gvs[is_var_operand_def, normalize_operand_def])
  >~ [`MEM out inst.inst_outputs`]
  >- (qpat_x_assum `MEM _ ps'.ps_stack \/ _` kall_tac >>
      `dfg_get_def (dfg_build_function fn) out = SOME inst` by
        metis_tac[dfg_build_function_ssa_def] >>
      Cases_on `inst.inst_opcode = ASSIGN`
      >- (`?op1 out1 v. inst.inst_operands = [op1] /\
            inst.inst_outputs = [out1] /\ eval_operand op1 vs = SOME v /\
            vs1 = update_var out1 v vs` by
            (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
             qpat_x_assum `inst.inst_opcode = ASSIGN`
               (fn th => simp[th, step_inst_non_invoke,
                              Once step_inst_base_def]) >>
             simp[AllCaseEqs()] >> metis_tac[]) >>
          gvs[] >>
          `normalize_operand (dfg_build_function fn) [] (Var out) = normalize_operand (dfg_build_function fn) [] op1` by
            metis_tac[normalize_operand_codegen_assign] >>
          simp[] >>
          Cases_on `op1`
          >- (`~retpc_var fn out` by
                (irule assign_nonvar_output_not_retpc >> simp[] >>
                 qexists_tac `inst` >> simp[]) >>
              gvs[eval_operand_def, normalize_operand_def, operand_val_def,
                  frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE])
          >- (rename1 `inst.inst_operands = [Var y]` >>
              `MEM (Var y) (compute_operands inst)` by
                gvs[compute_operands_def] >>
              `MEM (Var y) ps.ps_stack \/ Var y IN FDOM ps.ps_spilled` by
                (qpat_x_assum
                   `!op. MEM op (compute_operands inst) /\ _ ==> MEM op _ \/ _`
                   irule >> simp[is_var_operand_def]) >>
              `retpc_var fn out <=> retpc_var fn y` by
                (irule assign_output_retpc >> simp[] >>
                 qexists_tac `inst` >> simp[]) >>
              `operand_val (frame_view fn ra (update_var out v vs)) lo (Var out) =
               SOME (if retpc_var fn y then ra else v)` by
                (simp[operand_val_def, frame_view_vars_lookup, update_var_def,
                      FLOOKUP_UPDATE] >> metis_tac[]) >>
              `operand_val (frame_view fn ra vs) lo (Var y) =
               SOME (if retpc_var fn y then ra else v)` by
                (qpat_x_assum `eval_operand (Var y) vs = _` mp_tac >>
                 simp_tac bool_ss [eval_operand_def, lookup_var_def,
                   operand_val_def, frame_view_vars_lookup] >>
                 strip_tac >>
                 asm_simp_tac bool_ss [optionTheory.OPTION_MAP_DEF]) >>
              `operand_val (frame_view fn ra vs) lo (Var y) =
               operand_val (frame_view fn ra vs) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y))` by metis_tac[] >>
              `operand_val (frame_view fn ra (update_var out v vs)) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y)) =
               operand_val (frame_view fn ra vs) lo
                 (normalize_operand (dfg_build_function fn) [] (Var y))` by
                (irule frame_view_non_output_val >>
                 qexistsl_tac [`ctx`,`fuel`,`inst`] >>
                 conj_tac >- (rpt strip_tac >>
                   qpat_x_assum `!op. _ \/ _` (qspec_then `Var y` mp_tac) >>
                   gvs[]) >>
                 first_assum ACCEPT_TAC) >>
              metis_tac[])
          >> `~retpc_var fn out` by
               (irule assign_nonvar_output_not_retpc >> simp[] >>
                qexists_tac `inst` >> simp[]) >>
             gvs[eval_operand_def, normalize_operand_def, operand_val_def,
                 frame_view_vars_lookup, update_var_def, FLOOKUP_UPDATE]) >>
      `normalize_operand (dfg_build_function fn) [] (Var out) = Var out` by
        (simp[Once normalize_operand_def] >> gvs[dfg_get_def_def]) >>
      simp[]) >>
  `operand_val (frame_view fn ra vs) lo at =
   operand_val (frame_view fn ra vs) lo (normalize_operand (dfg_build_function fn) [] at)` by
    metis_tac[] >>
  `operand_val (frame_view fn ra vs1) lo at =
   operand_val (frame_view fn ra vs) lo at` by
    (irule frame_view_non_output_val >>
     qexistsl_tac [`ctx`,`fuel`,`inst`] >>
     conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `operand_val (frame_view fn ra vs1) lo (normalize_operand (dfg_build_function fn) [] at) =
   operand_val (frame_view fn ra vs) lo (normalize_operand (dfg_build_function fn) [] at)` by
    (irule frame_view_non_output_val >>
     qexistsl_tac [`ctx`,`fuel`,`inst`] >>
     conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
