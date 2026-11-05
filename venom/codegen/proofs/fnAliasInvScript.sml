(*
 * The cross-block DFG alias invariant of the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation.
 *
 * gen_fn_frame_simulation assumes that every operand on the planner's
 * stack or in its spill map has the value of its ASSIGN-chain root
 * (normalize_operand), read through the frame view.  The planner's
 * alias-only reorder steps rely on it.  The induction must re-establish
 * it at the successor block, whose lineage state carries the stack and
 * spill map the current block's code leaves (fnPlanLineage).
 *
 * TOP-LEVEL:
 *   lineage_alias_successor — CHEATED: one block preserves the invariant
 *)

Theory fnAliasInv
Ancestors
  fnPlanLineage frameRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  venomExecSemantics venomState livenessDefs dfgDefs cfgDefs
  fnAliasInvOrdering fnAliasInvAvailability dfgAnalysisProps allocaRemapSSA
  venomInst venomInstProps venomWf venomExecProps list rich_list stackModel
  stackPlanOps reorderSim sorting genericInputReady cleanOpsSim

Theorem alias_emit_reorder_consumed_window:
  emit_input_plan opc inputs nl ps = (iops,prepared) /\
  (!op. MEM op inputs /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  PERM inputs selected /\ LENGTH inputs <= 16 /\
  reorder_plan dfg selected prepared = (rops,arranged) ==>
  LENGTH selected <= LENGTH prepared.ps_stack /\
  arranged.ps_stack = stack_pop (LENGTH selected) arranged.ps_stack ++ selected
Proof
  `!xs : operand list. !ys.
     (!x. LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x ys) ==>
     LENGTH xs <= LENGTH ys` by
    (Induct >> simp[] >> rpt gen_tac >> strip_tac >>
     `MEM h ys` by
       (simp[GSYM LIST_ELEM_COUNT_MEM] >>
        first_x_assum (qspec_then `h` mp_tac) >>
        simp[LIST_ELEM_COUNT_THM]) >>
     qpat_x_assum `MEM h ys` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[] >>
     first_x_assum (qspec_then `l1 ++ l2` mp_tac) >>
     impl_tac >-
       (gen_tac >> first_x_assum (qspec_then `x` mp_tac) >>
        simp[elem_count_append, LIST_ELEM_COUNT_THM] >>
        Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM] ) >>
     simp[]) >>
  rpt strip_tac >>
  drule_all emit_input_plan_materialised >> strip_tac >>
  drule perm_operand_counts >> strip_tac >>
  `LENGTH selected = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `!x. LIST_ELEM_COUNT x selected <= LIST_ELEM_COUNT x prepared.ps_stack` by
    metis_tac[] >>
  `LENGTH selected <= LENGTH prepared.ps_stack` by metis_tac[] >>
  match_mp_tac fixed_suffix_decompose >> conj_tac
  >- (irule reorder_plan_materialised_length_floor >>
      simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]) >>
  rpt strip_tac >> irule reorder_plan_materialised_order >>
  simp[] >> qexistsl [`dfg`, `rops`, `prepared`] >> simp[]
QED

Theorem normalize_operand_non_assign_output:
  !fn inst x visited.
    ssa_form fn /\ MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
    inst.inst_opcode <> ASSIGN ==>
    normalize_operand (dfg_build_function fn) visited (Var x) = Var x
Proof
  rpt strip_tac >> Cases_on `MEM x visited` >> simp[Once normalize_operand_def] >>
  Cases_on `dfg_get_def (dfg_build_function fn) x` >>
  gvs[dfg_get_def_def] >>
  rename1 `FLOOKUP (dfg_build_function fn).dfg_defs x = SOME def` >>
  `dfg_get_def (dfg_build_function fn) x = SOME def` by simp[dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `def = inst` by
    (irule ssa_unique_output >> conj_tac >- (qexists_tac `fn` >> simp[]) >>
     qexists_tac `x` >> simp[]) >>
  gvs[] >> simp[Once normalize_operand_def]
QED

(* Actual single steps followed by normalize_operand, including literal roots. *)
Definition alias_assign_step_def:
  alias_assign_step dfg at src <=>
    ?v inst. at = Var v /\ FLOOKUP dfg.dfg_defs v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [src]
End

Theorem alias_assign_source_available:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  alias_assign_step (dfg_build_function fn) (Var x) (Var y) /\
  alias_path_available fn l i x ==>
  alias_path_available fn l i y
Proof
  strip_tac >>
  `?assign. dfg_get_def (dfg_build_function fn) x = SOME assign /\
      assign.inst_opcode = ASSIGN /\ assign.inst_operands = [Var y]` by
    gvs[alias_assign_step_def, dfg_get_def_def] >>
  drule dfg_build_function_correct >> strip_tac >>
  `!bb j. MEM bb fn.fn_blocks /\ j < LENGTH bb.bb_instructions /\
       MEM x (inst_defs (EL j bb.bb_instructions)) ==>
       alias_path_available fn bb.bb_label j y` by
    (rpt strip_tac >>
     `EL j bb.bb_instructions = assign` by
       (irule ssa_unique_output >> conj_tac
        >- (qexists_tac `fn` >>
            gvs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
        qexists_tac `x` >> gvs[inst_defs_def]) >>
     irule alias_ordinary_use_available >>
     simp[inst_uses_def, operand_vars_def, operand_var_def]) >>
  rewrite_tac[alias_path_available_def] >> rpt strip_tac >>
  qpat_x_assum `alias_path_available fn l i x` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac
  >- (`?j. j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = inst` by metis_tac[MEM_EL] >>
      `alias_path_available fn bb.bb_label j y` by
        metis_tac[lookup_block_MEM] >>
      `!p n. is_fn_path fn p ==> is_fn_path fn (TAKE n p)` by
        (Induct >- simp[is_fn_path_def] >>
         qx_gen_tac `head` >> Cases >- simp[is_fn_path_def] >>
         Cases_on `p` >> simp[is_fn_path_def] >>
         Cases_on `n'` >> simp[is_fn_path_def] >> strip_tac >>
         qpat_x_assum `!n. is_fn_path fn (h::t) ==> _`
           (qspec_then `SUC n` mp_tac) >> simp[]) >>
      qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
      rewrite_tac[alias_path_available_def] >>
      disch_then (qspec_then `TAKE (SUC k) path` mp_tac) >>
      impl_tac >- (simp[LENGTH_TAKE, HD_TAKE, LAST_EL, EL_TAKE] >>
                    metis_tac[lookup_block_label]) >>
      simp[LENGTH_TAKE, EL_TAKE] >> strip_tac >> disj1_tac
      >- (gvs[EL_TAKE] >> qexistsl_tac [`k'`,`bb'`,`inst'`] >> simp[] >> decide_tac) >>
      `bb.bb_label = EL k path` by metis_tac[lookup_block_label] >>
      gvs[] >> qexistsl_tac [`k`,`bb`,`EL j' bb.bb_instructions`] >>
      simp[EL_MEM]) >>
  `alias_path_available fn bb.bb_label j y` by
    metis_tac[lookup_block_MEM] >>
  qpat_x_assum `alias_path_available fn bb.bb_label j y` mp_tac >>
  rewrite_tac[alias_path_available_def] >>
  disch_then (qspec_then `path` mp_tac) >>
  impl_tac >- metis_tac[lookup_block_label] >>
  strip_tac >- metis_tac[] >>
  `bb.bb_label = l` by metis_tac[lookup_block_label] >> gvs[] >>
  disj2_tac >> qexists_tac `j'` >> simp[]
QED

Theorem normalize_operand_assign_chain:
  !dfg visited at.
    normalize_operand dfg visited at <> at ==>
    TC (alias_assign_step dfg) at (normalize_operand dfg visited at)
Proof
  recInduct normalize_operand_ind >>
  rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP dfg.dfg_defs v` >> gvs[] >>
  rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  rename1 `inst.inst_operands = src::rest` >>
  Cases_on `rest` >> gvs[] >>
  gvs[Once normalize_operand_def] >>
  `alias_assign_step dfg (Var v) src` by
    (simp[alias_assign_step_def] >> metis_tac[]) >>
  Cases_on `normalize_operand dfg (v::visited) src = src`
  >- metis_tac[relationTheory.TC_SUBSET] >>
  metis_tac[relationTheory.TC_RULES]
QED

Theorem alias_normalize_available:
  !dfg visited at.
    dfg = dfg_build_function fn /\ wf_function fn /\ ssa_form fn /\
    def_dominates_uses fn /\
    (!v. at = Var v ==> alias_path_available fn l i v) /\
    normalize_operand dfg visited at = Var r ==>
    alias_path_available fn l i r
Proof
  recInduct normalize_operand_ind >> rpt strip_tac >>
  gvs[Once normalize_operand_def, AllCaseEqs()] >>
  first_x_assum irule >> rpt strip_tac >> gvs[] >>
  irule alias_assign_source_available >>
  simp[alias_assign_step_def] >> metis_tac[]
QED

Theorem alias_live_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  MEM x (live_vars_at (liveness_analyze fn) l i) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l i x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

Theorem alias_live_after_root_not_defined:
  wf_function fn /\ ssa_form fn /\ def_dominates_uses fn /\
  fn_reachable fn l /\ lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  LENGTH (collect_phis bb.bb_instructions) <= SUC i /\
  MEM x (live_vars_at (liveness_analyze fn) l (SUC i)) /\
  ~MEM x (inst_defs (EL i bb.bb_instructions)) /\
  normalize_operand (dfg_build_function fn) [] (Var x) = Var r ==>
  ~MEM r (inst_defs (EL i bb.bb_instructions))
Proof
  strip_tac >>
  `alias_path_available fn l (SUC i) x` by
    metis_tac[alias_live_available_after_phis] >>
  `alias_path_available fn l i x` by
    metis_tac[alias_available_nondef_backward] >>
  `alias_path_available fn l i r` by
    (irule alias_normalize_available >> simp[] >>
     qexistsl_tac [`Var x`,`[]`] >> simp[]) >>
  metis_tac[alias_definition_not_available]
QED

(* Inventory boundaries do not depend on cleanup metadata or allocator fields. *)
Theorem alias_stack_find_singleton:
  !xs p v. FILTER p xs = [v] ==>
    ?d. stack_find p xs = SOME d /\ d < LENGTH xs /\ EL d xs = v /\
        (!j. j < LENGTH xs /\ p (EL j xs) ==> j = d)
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `p h` >> simp[stack_find_def]
  >- (strip_tac >> gvs[] >>
      rpt strip_tac >> Cases_on `j` >> gvs[] >>
      gvs[FILTER_EQ_NIL, EVERY_EL]) >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `SUC d` >> simp[arithmeticTheory.ADD1, EL_CONS] >>
  rpt strip_tac >> Cases_on `j` >> gvs[] >> metis_tac[]
QED

Theorem alias_phi_singleton_poke:
  FILTER (\at. MEM at inputs) stk = [v] /\ ~MEM ret inputs ==>
  ?d. stack_get_phi_depth inputs stk = SOME d /\
      stack_peek d stk = v /\
      (!at. MEM at inputs ==> ~MEM at (stack_poke d ret stk))
Proof
  strip_tac >>
  `FILTER (\at. MEM at inputs) (REVERSE stk) = [v]` by
    simp[FILTER_REVERSE] >>
  drule alias_stack_find_singleton >> strip_tac >>
  qexists_tac `d` >> simp[stack_get_phi_depth_def] >> conj_tac
  >- (gvs[LENGTH_REVERSE] >>
      qspecl_then [`d`,`stk`] mp_tac EL_REVERSE >> simp[stack_peek_def, arithmeticTheory.PRE_SUB1]) >>
  rpt strip_tac >>
  `?j. j < LENGTH (stack_poke d ret stk) /\
       EL j (stack_poke d ret stk) = at` by metis_tac[MEM_EL] >>
  gvs[stack_poke_def, LENGTH_LUPDATE, EL_LUPDATE] >>
  Cases_on `j = LENGTH stk - 1 - d` >> gvs[] >>
  `LENGTH stk - 1 - j = d` by
    (first_x_assum irule >>
     simp[EL_REVERSE, GSYM arithmeticTheory.ADD1]) >>
  decide_tac
QED

Definition plan_holds_def:
  plan_holds ps at <=> MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled
End

Definition alias_var_mass_def:
  alias_var_mass x ps =
    LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0)
End

Definition alias_var_budget_def:
  alias_var_budget pending ps <=>
    !x. alias_var_mass x ps <= SUC (LIST_ELEM_COUNT (Var x) pending)
End

Theorem alias_var_mass_fields:
  ps.ps_stack = qs.ps_stack /\ FDOM ps.ps_spilled = FDOM qs.ps_spilled ==>
  alias_var_mass x ps = alias_var_mass x qs
Proof
  simp[alias_var_mass_def]
QED

Theorem alias_var_budget_empty:
  alias_var_budget [] ps <=>
  !x. LIST_ELEM_COUNT (Var x) ps.ps_stack +
    (if Var x IN FDOM ps.ps_spilled then 1 else 0) <= 1
Proof
  simp[alias_var_budget_def, alias_var_mass_def, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_push:
  alias_var_mass x (ps with ps_stack := stack_push op ps.ps_stack) =
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  simp[alias_var_mass_def, stack_push_def, SNOC_APPEND, elem_count_append,
       LIST_ELEM_COUNT_THM] >>
  Cases_on `op = Var x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_restore:
  alias_var_mass x (SND (do_restore op ps)) = alias_var_mass x ps
Proof
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  simp[do_restore_def, alias_var_mass_def, stack_push_def,
       SNOC_APPEND, elem_count_append, LIST_ELEM_COUNT_THM, finite_mapTheory.FDOM_DOMSUB] >>
  Cases_on `op = Var x` >>
  gvs[finite_mapTheory.flookup_thm, LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_spill_tos:
  !ps x. ps.ps_stack <> [] ==>
  alias_var_mass x (SND (do_spill_tos ps)) <= alias_var_mass x ps
Proof
  rpt gen_tac >> strip_tac >>
  `?a stk. ps.ps_stack = SNOC a stk` by metis_tac[SNOC_CASES] >>
  simp[do_spill_tos_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[] >>
  simp[stack_pop_def, stack_peek_def, SNOC_APPEND, TAKE_APPEND,
       EL_APPEND_EQN, elem_count_append, LIST_ELEM_COUNT_THM] >>
  Cases_on `a = Var x` >> simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_var_mass_spill:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_spill_at d ps)) <= alias_var_mass x ps
Proof
  strip_tac >> Cases_on `d = 0`
  >- (simp[do_spill_at_def] >> irule alias_var_mass_spill_tos >>
      strip_tac >> gvs[]) >>
  `LIST_ELEM_COUNT (Var x) (stack_swap d ps.ps_stack) =
   LIST_ELEM_COUNT (Var x) ps.ps_stack` by
    (mp_tac (Q.SPECL [`ps.ps_stack`, `0`, `d`, `Var x`]
       doSwapSimTheory.stack_poke_exchange_multiplicity) >>
     simp[stack_poke_def, stack_peek_def, stack_swap_def]) >>
  `stack_swap d ps.ps_stack <> []` by
    (strip_tac >> gvs[stack_swap_def]) >>
  qspecl_then [`ps with ps_stack := stack_swap d ps.ps_stack`, `x`] mp_tac
    alias_var_mass_spill_tos >>
  simp[do_spill_at_def, alias_var_mass_def] >>
  pairarg_tac >> gvs[]
QED

Theorem alias_var_mass_dup:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_dup d ps)) = alias_var_mass x ps +
    (if stack_peek d ps.ps_stack = Var x then 1 else 0)
Proof
  strip_tac >>
  drule_then assume_tac doSwapSimTheory.do_dup_stack_exact >>
  Cases_on `d <= 15` >>
  simp[alias_var_mass_def, do_dup_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[alias_var_mass_def, stack_dup_def, elem_count_append] >>
  Cases_on `stack_peek d ps.ps_stack = Var x` >>
  simp[LIST_ELEM_COUNT_THM]
QED

Theorem alias_var_mass_swap:
  d < LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (do_swap d ps)) = alias_var_mass x ps
Proof
  strip_tac >> drule_then (qspec_then `Var x` assume_tac)
    doSwapSimTheory.do_swap_multiplicity >>
  simp[alias_var_mass_def, do_swap_spilled_unchanged]
QED

Theorem alias_var_mass_restore_spilled:
  !ops ps x.
  alias_var_mass x (SND (restore_spilled_plan ops ps)) = alias_var_mass x ps
Proof
  Induct >> simp[restore_spilled_plan_def] >> rpt gen_tac >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`ps1`, `x`] mp_tac) >>
  mp_tac (Q.INST [`op` |-> `h`] alias_var_mass_restore) >> gvs[]
QED

Theorem alias_var_mass_reduce_depth:
  !fuel targets op f n ps x.
  alias_var_mass x (SND (reduce_depth_plan fuel targets op f n ps)) <=
  alias_var_mass x ps
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x' n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_spill) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`, `x`] mp_tac) >>
  gvs[] >> decide_tac
QED

Theorem alias_reduce_depth_length_floor:
  !fuel targets op f n ps.
  n <= LENGTH ps.ps_stack ==>
  n <= LENGTH (SND (reduce_depth_plan fuel targets op f n ps)).ps_stack
Proof
  Induct >> simp[Once reduce_depth_plan_def] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_unfixed_depth op f n ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack targets x n` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  drule_then assume_tac stack_get_unfixed_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  drule_all_then strip_assume_tac planWfTheory.select_spill_candidate_bound >>
  drule_then assume_tac planWfTheory.select_spill_candidate_below_target >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack - 1` by
    (Cases_on `x' = 0` >>
     gvs[do_spill_at_def, do_spill_tos_def, LET_THM,
         stack_swap_def, stack_pop_def] >>
     rpt (pairarg_tac >> gvs[]) >> simp[LENGTH_LUPDATE, LENGTH_TAKE_EQ]) >>
  first_x_assum (qspecl_then [`targets`, `op`, `f`, `n`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_one_bounds:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack /\
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps1.ps_stack /\
   alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps.ps_stack` >> gvs[] >>
     Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
     mp_tac alias_var_mass_restore >>
     qspecl_then [`op`, `ps`] mp_tac planWfTheory.do_restore_length >> gvs[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps1.ps_stack` >> simp[] >>
  pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps2.ps_stack /\
   alias_var_mass x ps2 <= alias_var_mass x ps1` by
    (Cases_on `x' > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`]
       mp_tac alias_reduce_depth_length_floor >>
     qspecl_then [`LENGTH ps1.ps_stack`, `targets`, `op`,
       `LENGTH targets - (idx + 1)`, `LENGTH targets`, `ps1`, `x`]
       mp_tac alias_var_mass_reduce_depth >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (LENGTH targets - (idx + 1))
                   (LENGTH targets) ps2.ps_stack` >> simp[] >>
  suspend "exchange"
QED

Resume alias_reorder_one_bounds[exchange]:
  drule_then strip_assume_tac stack_get_unfixed_depth_props >>
  `LENGTH targets - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `x'' = LENGTH targets - (idx + 1)` >> simp[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH targets - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (qspecl_then [`ps2.ps_stack`, `x''`, `LENGTH targets - (idx + 1)`, `Var x`]
        mp_tac doSwapSimTheory.stack_poke_exchange_multiplicity >>
      simp[] >> strip_tac >>
      gvs[alias_var_mass_def, stack_poke_def, LENGTH_LUPDATE]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack /\
   alias_var_mass x ps3 = alias_var_mass x ps2` by
    (qspecl_then [`x''`, `ps2`] mp_tac planWfTheory.do_swap_length >>
     mp_tac (Q.INST [`d` |-> `x''`, `ps` |-> `ps2`] alias_var_mass_swap) >>
     gvs[]) >>
  qspecl_then [`LENGTH targets - (idx + 1)`, `ps3`]
    mp_tac planWfTheory.do_swap_length >>
  mp_tac (Q.INST [`d` |-> `LENGTH (targets : operand list) - (idx + 1)`, `ps` |-> `ps3`]
    alias_var_mass_swap) >> gvs[] >> decide_tac
QED

Finalise alias_reorder_one_bounds

Theorem alias_reorder_one_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_one dfg targets idx op ps)).ps_stack
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_var_mass_reorder_one:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_one dfg targets idx op ps)) <= alias_var_mass x ps
Proof
  metis_tac[alias_reorder_one_bounds]
QED

Theorem alias_reorder_fold_bounds:
  !steps ops ps.
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)).ps_stack /\
  alias_var_mass x (SND (FOLDL
    (\(ops, ps) (idx, op).
      (\(step_ops, ps'). (ops ++ step_ops, ps'))
        (reorder_one dfg targets idx op ps)) (ops, ps) steps)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> simp[] >> pairarg_tac >> simp[] >>
  `LENGTH targets <= LENGTH ps'.ps_stack /\
   alias_var_mass x ps' <= alias_var_mass x ps` by
    (mp_tac (Q.INST [`idx` |-> `h0`, `op` |-> `h1`] alias_reorder_one_bounds) >>
     gvs[]) >>
  first_x_assum (qspecl_then [`ops ++ step_ops`, `ps'`] mp_tac) >>
  simp[] >> decide_tac
QED

Theorem alias_reorder_plan_length_floor:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  LENGTH targets <= LENGTH (SND (reorder_plan dfg targets ps)).ps_stack
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_var_mass_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack ==>
  alias_var_mass x (SND (reorder_plan dfg targets ps)) <= alias_var_mass x ps
Proof
  strip_tac >> simp[reorder_plan_def] >>
  metis_tac[alias_reorder_fold_bounds]
QED

Theorem alias_var_budget_reorder_plan:
  LENGTH targets <= LENGTH ps.ps_stack /\ alias_var_budget pending ps ==>
  alias_var_budget pending (SND (reorder_plan dfg targets ps))
Proof
  rw[alias_var_budget_def] >>
  drule_then (qspecl_then [`x`, `dfg`] assume_tac)
    (GEN_ALL alias_var_mass_reorder_plan) >>
  first_x_assum (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_var_mass_pop:
  alias_var_mass x (ps with ps_stack := stack_pop n ps.ps_stack) +
  LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack) = alias_var_mass x ps
Proof
  `TAKE (LENGTH ps.ps_stack - n) ps.ps_stack ++ top_n n ps.ps_stack =
   ps.ps_stack` by
    (Cases_on `n <= LENGTH ps.ps_stack`
     >- simp[top_n_def, GSYM rich_listTheory.LASTN_def,
             rich_listTheory.LASTN_DROP, TAKE_DROP] >>
     `LENGTH ps.ps_stack <= n` by decide_tac >>
     simp[top_n_def, TAKE_LENGTH_TOO_LONG]) >>
  pop_assum (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
  simp[elem_count_append, alias_var_mass_def, stack_pop_def] >> decide_tac
QED

Theorem alias_var_budget_pop_window:
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n ps.ps_stack)) ==>
  alias_var_budget pending (ps with ps_stack := stack_pop n ps.ps_stack)
Proof
  rw[alias_var_budget_def] >>
  first_x_assum (qspec_then `x` assume_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >>
  mp_tac alias_var_mass_pop >> simp[elem_count_append] >> decide_tac
QED

Theorem alias_var_budget_reorder_pop:
  qs = SND (reorder_plan dfg targets ps) /\
  LENGTH targets <= LENGTH ps.ps_stack /\
  alias_var_budget (pending ++ consumed) ps /\
  (!x. LIST_ELEM_COUNT (Var x) consumed <=
       LIST_ELEM_COUNT (Var x) (top_n n qs.ps_stack)) ==>
  alias_var_budget pending (qs with ps_stack := stack_pop n qs.ps_stack)
Proof
  strip_tac >> irule alias_var_budget_pop_window >>
  qexists_tac `consumed` >> simp[] >>
  metis_tac[alias_var_budget_reorder_plan]
QED

Theorem alias_var_mass_emit_one:
  !opc live op ps x.
  alias_var_mass x (SND (emit_one_input opc live op ps)) <=
  alias_var_mass x ps + (if op = Var x then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[emit_one_input_def, is_var_operand_def, alias_var_mass_push]
  >~ [`SOPushLabel l`] >-
    (Cases_on `opc = INVOKE` >> simp[alias_var_mass_push]) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var s))` >>
     gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  drule_then (qspec_then `x` mp_tac) (GEN_ALL alias_var_mass_dup) >>
  gvs[]
QED

Theorem alias_var_mass_emit_inputs:
  !inputs opc live ps x.
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  gvs[] >> Cases_on `h = Var x` >> simp[LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem alias_var_mass_emit_inputs_dead:
  !inputs opc live ps x. ~MEM x live ==>
  alias_var_mass x (SND (emit_input_plan opc inputs live ps)) +
    (if MEM (Var x) inputs then 1 else 0) <=
  alias_var_mass x ps + LIST_ELEM_COUNT (Var x) inputs
Proof
  `!ops v. MEM v (dfgDefs$operand_vars ops) <=> MEM (Var v) ops` by
    (Induct >> simp[dfgDefsTheory.operand_vars_def] >>
     rpt gen_tac >> Cases_on `h` >>
     simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def]) >>
  Induct >> simp[emit_input_plan_def, LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> strip_tac >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  first_x_assum (qspecl_then [`opc`, `live`, `ps1`, `x`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `h = Var x`
  >- (gvs[] >> Cases_on `MEM (Var x) inputs`
      >- (qspecl_then [`opc`, `operand_vars inputs ++ live`, `Var x`, `ps`, `x`]
            mp_tac alias_var_mass_emit_one >>
          gvs[LIST_ELEM_COUNT_THM] >> decide_tac) >>
      `~MEM x (operand_vars inputs ++ live)` by
        simp[passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
      simp[emit_one_input_def, is_var_operand_def] >>
      pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      `alias_var_mass x ps1 = alias_var_mass x ps` by
        (Cases_on `IS_SOME (FLOOKUP ps.ps_spilled (Var x))` >>
         gvs[] >> metis_tac[alias_var_mass_restore, pairTheory.SND]) >>
      simp[LIST_ELEM_COUNT_THM] >> decide_tac) >>
  qspecl_then [`opc`, `operand_vars inputs ++ live`, `h`, `ps`, `x`]
    mp_tac alias_var_mass_emit_one >>
  simp[LIST_ELEM_COUNT_THM] >>
  Cases_on `MEM (Var x) inputs` >> gvs[] >> decide_tac
QED

Theorem alias_emit_reorder_pop_var_support:
  alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs_dead >> simp[] >> strip_tac >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  `0 < alias_var_mass x
     (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)` by
    (gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
     decide_tac) >>
  Cases_on `MEM (Var x) inputs`
  >- (gvs[] >> decide_tac) >>
  `~plan_holds ps (Var x)` by metis_tac[] >>
  `alias_var_mass x ps = 0` by
    gvs[plan_holds_def, alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_emit_reorder_pop_support:
  alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) inputs) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  emit_input_plan opc inputs live ps = (iops,mid) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  !x. plan_holds (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack)
         (Var x) ==> MEM x live
Proof
  simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  irule alias_emit_reorder_pop_var_support >> metis_tac[]
QED

Theorem alias_var_budget_emit_inputs:
  alias_var_budget pending ps ==>
  alias_var_budget (pending ++ inputs) (SND (emit_input_plan opc inputs live ps))
Proof
  simp[alias_var_budget_def, elem_count_append] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> decide_tac
QED

Theorem alias_popmany_singleton_inventory:
  plan_holds (SND (popmany_plan [v] ps)) at ==> plan_holds ps at
Proof
  Cases_on `stack_get_depth v ps.ps_stack` >>
  simp[popmany_plan_def, is_contiguous_top_def, popmany_individual_def,
       QSORT_DEF, PARTITION_DEF, PART_DEF] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `x = 0`
  >- (gvs[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]) >>
  Cases_on `x = 1` >> gvs[] >> pairarg_tac >> simp[] >>
  `!a. MEM a ps'.ps_stack \/ a IN FDOM ps'.ps_spilled ==>
       MEM a ps.ps_stack \/ a IN FDOM ps.ps_spilled` by
    metis_tac[do_swap_inventory_subset] >>
  simp[plan_holds_def, stack_pop_def] >> metis_tac[MEM_TAKE]
QED

Theorem alias_phi_singleton_consumed:
  inputs = FILTER is_var_operand inst.inst_operands /\
  ret = Var (HD inst.inst_outputs) /\
  FILTER (\at. MEM at inputs) ps.ps_stack = [Var v] /\
  MEM (Var v) inputs /\ ~MEM v next_liveness /\ ~MEM ret inputs /\
  (!at. MEM at inputs ==> at NOTIN FDOM ps.ps_spilled) ==>
  !at. MEM at inputs ==>
    ~plan_holds (SND (generate_phi_plan inst next_liveness is_halting ps)) at
Proof
  strip_tac >>
  `?d. stack_get_phi_depth inputs ps.ps_stack = SOME d /\
       stack_peek d ps.ps_stack = Var v /\
       (!at. MEM at inputs ==> ~MEM at (stack_poke d ret ps.ps_stack))` by
    metis_tac[alias_phi_singleton_poke] >>
  `!at. MEM at inputs ==>
      ~plan_holds (ps with ps_stack := stack_poke d ret ps.ps_stack) at` by
    (simp[plan_holds_def] >> metis_tac[]) >>
  gvs[] >> simp[generate_phi_plan_def, operand_to_string_def] >>
  IF_CASES_TAC
  >- (pairarg_tac >> simp[] >> rpt strip_tac >>
      metis_tac[alias_popmany_singleton_inventory, pairTheory.SND]) >>
  simp[]
QED
(* Generic projection for spill release; unlike the specialized stack
   theorem in fnFrameBoundaryGenRet this also describes arbitrary deletion
   batches, without importing the frame-simulation dependency chain. *)
Theorem alias_release_fold_fields:
  !xs ps.
    (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_stack = ps.ps_stack /\
    (!at. at IN FDOM (FOLDL (\ps' (op,off).
       ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                   ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps xs).ps_spilled <=>
      at IN FDOM ps.ps_spilled /\ ~MEM at (MAP FST xs))
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >>
  metis_tac[]
QED

Theorem alias_release_dead_spills_domain:
  at IN FDOM (release_dead_spills live ps).ps_spilled <=>
    at IN FDOM ps.ps_spilled /\ (?v. at = Var v /\ MEM v live)
Proof
  Cases_on `at` >>
  simp[release_dead_spills_def, alias_release_fold_fields, MEM_MAP, MEM_FILTER,
       pairTheory.FORALL_PROD, alistTheory.MEM_pair_fmap_to_alist_FLOOKUP] >>
  metis_tac[finite_mapTheory.flookup_thm]
QED

Theorem alias_var_mass_release_dead_spills:
  alias_var_mass x (release_dead_spills live ps) <= alias_var_mass x ps
Proof
  `(release_dead_spills live ps).ps_stack = ps.ps_stack` by
    simp[release_dead_spills_def, alias_release_fold_fields] >>
  simp[alias_var_mass_def, alias_release_dead_spills_domain] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[] >>
  Cases_on `MEM x live` >> simp[]
QED

Theorem alias_emit_ops_inventory:
  (SND (generate_emit_ops inst topics ps)).ps_stack = ps.ps_stack /\
  (SND (generate_emit_ops inst topics ps)).ps_spilled = ps.ps_spilled
Proof
  rw[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  gvs[asmIRTheory.venom_to_evm_name_def, fresh_label_def]
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`FILTER is_label_operand inst.inst_operands`] >- suspend "jnz"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >~ [`HD inst.inst_operands`] >- suspend "invoke"
  >> suspend "jmp"
QED

Resume alias_emit_ops_inventory[jnz]:
  markerLib.RESUME_TAC >>
  Cases_on `FILTER is_label_operand inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >>
  Cases_on `t` >> simp[] >> rename1 `h::t` >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Resume alias_emit_ops_inventory[invoke]:
  markerLib.RESUME_TAC >>
  Cases_on `HD inst.inst_operands` >> simp[]
QED

Resume alias_emit_ops_inventory[jmp]:
  markerLib.RESUME_TAC >>
  Cases_on `inst.inst_operands` >> simp[] >>
  rename1 `h::t` >> Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Finalise alias_emit_ops_inventory

Theorem alias_var_mass_emit_ops:
  alias_var_mass x (SND (generate_emit_ops inst topics ps)) = alias_var_mass x ps
Proof
  simp[alias_var_mass_def, alias_emit_ops_inventory]
QED

Theorem alias_var_mass_pop_foldl_body:
  alias_var_mass x (SND (pop_foldl_body (ops,ps) v)) <= alias_var_mass x ps
Proof
  simp[pop_foldl_body_def] >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[]
  >- (mp_tac (Q.INST [`n` |-> `1`] alias_var_mass_pop) >> decide_tac) >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps1 = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `1`, `ps` |-> `ps1`] alias_var_mass_pop) >>
  decide_tac
QED

Theorem alias_var_mass_pop_fold:
  !xs ops ps.
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) <= alias_var_mass x ps
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_var_mass_pop_foldl_body) >>
  simp[] >> decide_tac
QED

Theorem alias_var_mass_popmany_individual:
  alias_var_mass x (SND (popmany_individual to_pop ps)) <= alias_var_mass x ps
Proof
  simp[popmany_individual_eq_foldl, alias_var_mass_pop_fold]
QED

Theorem alias_var_mass_popmany:
  alias_var_mass x (SND (popmany_plan to_pop ps)) <= alias_var_mass x ps
Proof
  Cases_on `to_pop` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  IF_CASES_TAC >> simp[alias_var_mass_popmany_individual] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  fs[] >>
  pairarg_tac >> simp[] >>
  `alias_var_mass x ps' = alias_var_mass x ps` by
    metis_tac[alias_var_mass_swap, pairTheory.SND] >>
  mp_tac (Q.INST [`n` |-> `SUC (LENGTH (t:operand list))`, `ps` |-> `ps'`] alias_var_mass_pop) >>
  decide_tac
QED

Theorem alias_unique_take_absent:
  LIST_ELEM_COUNT at stk <= 1 /\ i < LENGTH stk /\ k <= i /\ EL i stk = at ==>
  ~MEM at (TAKE k stk)
Proof
  strip_tac >>
  `MEM at (DROP k stk)` by
    (simp[MEM_EL] >> qexists_tac `i - k` >>
     simp[EL_DROP] >> `k + (i - k) = i` by decide_tac >> simp[]) >>
  `LIST_ELEM_COUNT at (TAKE k stk) + LIST_ELEM_COUNT at (DROP k stk) <= 1` by
    metis_tac[TAKE_DROP, elem_count_append] >>
  fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem alias_pop_foldl_body_deletes:
  LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (pop_foldl_body (ops,ps) at)).ps_stack
Proof
  strip_tac >> Cases_on `stack_get_depth at ps.ps_stack`
  >- (simp[pop_foldl_body_def] >>
      fs[stack_get_depth_NONE] >> strip_tac >> fs[MEM_EL] >>
      first_x_assum (qspec_then `LENGTH ps.ps_stack - 1 - n` mp_tac) >>
      simp[stack_peek_def] >>
      `LENGTH ps.ps_stack - 1 - (LENGTH ps.ps_stack - 1 - n) = n` by decide_tac >>
      simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
  >- (simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
      qexists_tac `LENGTH ps.ps_stack - 1` >>
      gvs[stack_peek_def]) >>
  pairarg_tac >> simp[] >>
  `ps1.ps_stack = stack_swap x ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_stack_result, pairTheory.SND] >>
  `LIST_ELEM_COUNT at ps1.ps_stack <= 1` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  gvs[] >> simp[stack_pop_def] >> irule alias_unique_take_absent >> simp[] >>
  qexists_tac `LENGTH ps.ps_stack - 1` >>
  simp[] >> simp[stack_swap_def, EL_LUPDATE, stack_peek_def] >>
  gvs[stack_peek_def]
QED

Theorem alias_pop_foldl_body_count:
  LIST_ELEM_COUNT at (SND (pop_foldl_body (ops,ps) v)).ps_stack <=
  LIST_ELEM_COUNT at ps.ps_stack
Proof
  `!stk:operand list. !n. LIST_ELEM_COUNT at (stack_pop n stk) <= LIST_ELEM_COUNT at stk` by
    (simp[stack_pop_def] >> rpt gen_tac >>
     `LIST_ELEM_COUNT at (TAKE (LENGTH stk - n) stk) +
      LIST_ELEM_COUNT at (DROP (LENGTH stk - n) stk) = LIST_ELEM_COUNT at stk` by
       metis_tac[elem_count_append, TAKE_DROP] >> decide_tac) >>
  Cases_on `stack_get_depth v ps.ps_stack` >> simp[pop_foldl_body_def] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[] >>
  `LIST_ELEM_COUNT at ps1.ps_stack = LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[doSwapSimTheory.do_swap_multiplicity, pairTheory.SND] >>
  metis_tac[]
QED

Theorem alias_pop_fold_count:
  !xs ops ps. LIST_ELEM_COUNT at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack <=
    LIST_ELEM_COUNT at ps.ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  first_x_assum (qspecl_then [`q`, `r`] mp_tac) >>
  mp_tac (Q.INST [`v` |-> `h`] alias_pop_foldl_body_count) >> simp[] >> decide_tac
QED

Theorem alias_pop_fold_deletes:
  !xs ops ps. MEM at xs /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
    ~MEM at (SND (FOLDL pop_foldl_body (ops,ps) xs)).ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  `LIST_ELEM_COUNT at r.ps_stack <= LIST_ELEM_COUNT at ps.ps_stack` by
    metis_tac[alias_pop_foldl_body_count, pairTheory.SND] >>
  Cases_on `at = h`
  >- (`~MEM at r.ps_stack` by metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_pop_fold_count) >>
      gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_individual_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_individual to_pop ps)).ps_stack
Proof
  simp[popmany_individual_eq_foldl] >> strip_tac >>
  irule alias_pop_fold_deletes >> simp[QSORT_MEM]
QED

Theorem alias_popmany_contiguous_depth:
  MEM at to_pop /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) to_pop) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) to_pop)) ==>
  ?d. stack_get_depth at stk = SOME d /\ 1 <= d /\ d <= LENGTH to_pop
Proof
  strip_tac >>
  `IS_SOME (stack_get_depth at stk)` by (fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  Cases_on `stack_get_depth at stk` >> fs[] >>
  `MEM x (MAP THE (MAP (\v. stack_get_depth v stk) to_pop))` by
    (simp[MEM_MAP] >> qexists_tac `SOME x` >> simp[] >>
     qexists_tac `at` >> simp[]) >>
  fs[is_contiguous_top_def] >>
  `MEM x (GENLIST SUC (LENGTH to_pop))` by metis_tac[QSORT_MEM] >>
  fs[MEM_GENLIST] >> decide_tac
QED

Theorem alias_popmany_plan_deletes:
  MEM at to_pop /\ LIST_ELEM_COUNT at ps.ps_stack <= 1 ==>
  ~MEM at (SND (popmany_plan to_pop ps)).ps_stack
Proof
  disch_tac >> Cases_on `to_pop` >- fs[] >>
  `MEM at (h::t) /\ LIST_ELEM_COUNT at ps.ps_stack <= 1` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  reverse IF_CASES_TAC
  >- metis_tac[alias_popmany_individual_deletes] >>
  `LENGTH (h::t) < LENGTH ps.ps_stack` by
    (irule contiguous_top_stack_bound >> simp[]) >>
  `?d. stack_get_depth at ps.ps_stack = SOME d /\ 1 <= d /\ d <= LENGTH (h::t)` by
    (irule alias_popmany_contiguous_depth >> simp[]) >>
  drule_then strip_assume_tac stack_get_depth_props >>
  pairarg_tac >> simp[] >>
  `ps'.ps_stack = stack_swap (SUC (LENGTH t)) ps.ps_stack` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`] doSwapSimTheory.do_swap_stack_result) >>
     fs[]) >>
  `LIST_ELEM_COUNT at ps'.ps_stack <= 1` by
    (mp_tac (Q.SPECL [`SUC (LENGTH (t:operand list))`, `ps`]
       doSwapSimTheory.do_swap_multiplicity) >> simp[] >>
     impl_tac >- fs[] >> disch_then (qspec_then `at` mp_tac) >> simp[]) >>
  suspend "positions"
QED

Resume alias_popmany_plan_deletes[positions]:
  markerLib.RESUME_TAC >>
  simp[stack_pop_def] >> irule alias_unique_take_absent >>
  conj_tac >- gvs[] >>
  qexists_tac `if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
              else LENGTH ps.ps_stack - 1 - d` >>
  simp[] >>
  `LENGTH ps'.ps_stack = LENGTH ps.ps_stack` by simp[] >>
  `EL (if d = SUC (LENGTH t) then LENGTH ps.ps_stack - 1
       else LENGTH ps.ps_stack - 1 - d) ps'.ps_stack = at` by
    (Cases_on `d = SUC (LENGTH t)` >>
     `LENGTH ps.ps_stack - 1 - SUC (LENGTH t) <> LENGTH ps.ps_stack - 1` by
       (fs[] >> decide_tac) >>
     simp[stack_swap_def, EL_LUPDATE] >>
     gvs[stack_peek_def] >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1` by decide_tac >>
     `LENGTH ps.ps_stack - 1 - d <> LENGTH ps.ps_stack - 1 - SUC (LENGTH t)` by
       (fs[] >> decide_tac) >> simp[]) >>
  gvs[] >> decide_tac
QED

Finalise alias_popmany_plan_deletes

Theorem alias_pop_fold_mass_zero:
  !xs ops ps. MEM (Var x) xs /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
    alias_var_mass x (SND (FOLDL pop_foldl_body (ops,ps) xs)) = 0
Proof
  Induct >> simp[] >> rpt gen_tac >> disch_tac >>
  Cases_on `pop_foldl_body (ops,ps) h` >> simp[] >>
  `alias_var_mass x ps <= 1 /\ Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  `alias_var_mass x r <= alias_var_mass x ps` by
    metis_tac[alias_var_mass_pop_foldl_body, pairTheory.SND] >>
  `Var x NOTIN FDOM r.ps_spilled` by
    (qpat_x_assum `pop_foldl_body _ _ = _` mp_tac >>
     Cases_on `stack_get_depth h ps.ps_stack`
     >- (simp[pop_foldl_body_def] >> strip_tac >> gvs[]) >>
     simp[pop_foldl_body_def] >> IF_CASES_TAC >> simp[]
     >- (strip_tac >> gvs[]) >>
     pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >>
     metis_tac[do_swap_spilled_unchanged, pairTheory.SND]) >>
  Cases_on `Var x = h`
  >- (`LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by
        fs[alias_var_mass_def] >>
      `~MEM (Var x) r.ps_stack` by
        metis_tac[alias_pop_foldl_body_deletes, pairTheory.SND] >>
      `alias_var_mass x r = 0` by
        (gvs[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]) >>
      mp_tac (Q.SPECL [`xs`, `q`, `r`] alias_var_mass_pop_fold) >> simp[]) >>
  first_x_assum irule >> gvs[] >> decide_tac
QED

Theorem alias_popmany_plan_mass_zero:
  MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
    Var x NOTIN FDOM ps.ps_spilled ==>
  alias_var_mass x (SND (popmany_plan to_pop ps)) = 0
Proof
  disch_tac >>
  `MEM (Var x) to_pop /\ alias_var_mass x ps <= 1 /\
   Var x NOTIN FDOM ps.ps_spilled` by metis_tac[] >>
  qpat_x_assum `MEM _ _ /\ _` kall_tac >>
  `LIST_ELEM_COUNT (Var x) ps.ps_stack <= 1` by fs[alias_var_mass_def] >>
  `~MEM (Var x) (SND (popmany_plan to_pop ps)).ps_stack` by
    metis_tac[alias_popmany_plan_deletes] >>
  Cases_on `to_pop` >- fs[] >>
  simp[Once popmany_plan_def] >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  reverse IF_CASES_TAC
  >- (simp[popmany_individual_eq_foldl] >> irule alias_pop_fold_mass_zero >>
      simp[QSORT_MEM]) >>
  pairarg_tac >> simp[] >>
  `ps'.ps_spilled = ps.ps_spilled` by
    metis_tac[do_swap_spilled_unchanged, pairTheory.SND] >>
  qpat_x_assum `~MEM _ (SND _).ps_stack` mp_tac >>
  simp[Once popmany_plan_def] >> simp[] >>
  simp[alias_var_mass_def, GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem alias_var_mass_optimistic_swap:
  alias_var_mass x (SND (optimistic_swap_plan dfg inst live next_term ps)) <=
  alias_var_mass x ps
Proof
  simp[optimistic_swap_plan_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  drule_then strip_assume_tac stack_get_depth_props >>
  simp[alias_var_mass_swap]
QED

Theorem alias_var_mass_outputs:
  !outs ps.
    alias_var_mass x (FOLDL (\ps' out.
      ps' with ps_stack := stack_push (Var out) ps'.ps_stack) ps outs) =
    alias_var_mass x ps + LIST_ELEM_COUNT x outs
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> simp[alias_var_mass_push] >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_DEF] >> decide_tac
QED

Theorem alias_var_mass_zero:
  alias_var_mass x ps = 0 <=> ~plan_holds ps (Var x)
Proof
  simp[alias_var_mass_def, plan_holds_def, GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var x IN FDOM ps.ps_spilled` >> simp[]
QED

Theorem alias_emit_reorder_pop_mass:
  emit_input_plan opc inputs live ps = (iops,mid) /\
  (!op. MEM op inputs /\ is_var_operand op ==> plan_holds ps op) /\
  PERM targets inputs /\ LENGTH inputs <= 16 /\
  reorder_plan dfg targets mid = (rops,qs) ==>
  alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) <=
  alias_var_mass x ps
Proof
  strip_tac >>
  `PERM inputs targets` by metis_tac[PERM_SYM] >>
  `!op. MEM op inputs /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    metis_tac[plan_holds_def] >>
  drule_all alias_emit_reorder_consumed_window >> strip_tac >>
  `LENGTH targets = LENGTH inputs` by metis_tac[PERM_LENGTH] >>
  `alias_var_mass x qs <= alias_var_mass x mid` by
    (mp_tac (Q.INST [`targets` |-> `targets`, `ps` |-> `mid`,
                    `dfg` |-> `dfg`, `x` |-> `x`] alias_var_mass_reorder_plan) >>
     simp[]) >>
  `alias_var_mass x qs =
   alias_var_mass x (qs with ps_stack := stack_pop (LENGTH inputs) qs.ps_stack) +
   LIST_ELEM_COUNT (Var x) inputs` by
    (drule perm_operand_counts >> strip_tac >>
     qpat_x_assum `qs.ps_stack = _`
       (mp_tac o AP_TERM ``LIST_ELEM_COUNT (Var x)``) >>
     simp[alias_var_mass_def, elem_count_append] >> decide_tac) >>
  qspecl_then [`inputs`, `opc`, `live`, `ps`, `x`] mp_tac
    alias_var_mass_emit_inputs >> simp[] >> decide_tac
QED

Theorem alias_regular_plan_stages:
  inst.inst_opcode <> JMP /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  ?iops mid targets rops reordered topics eops emitted pops post.
    emit_input_plan inst.inst_opcode (compute_operands inst) live ps = (iops,mid) /\
    PERM targets (compute_operands inst) /\
    reorder_plan dfg targets mid = (rops,reordered) /\
    generate_emit_ops inst topics
      (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
        (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
        inst.inst_outputs) = (eops,emitted) /\
    (if inst.inst_outputs <> [] /\ (~is_halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)) emitted
     else ([],emitted)) = (pops,post) /\
    (!x. alias_var_mass x qs <= alias_var_mass x post)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics` >>
  pairarg_tac >> simp[] >>
  `?targets. PERM targets (compute_operands inst) /\
     reorder_plan dfg targets ps1 = (reorder_ops,ps4)` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[]
     >- (pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
         IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]
         >- metis_tac[PERM_REFL] >>
         `2 <= LENGTH (compute_operands inst)` by decide_tac >>
         drule last_two_reorder_perm >> metis_tac[PERM_SYM]) >>
     metis_tac[PERM_REFL]) >>
  qpat_x_assum `(if _ then _ else _) = _` kall_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >> gvs[] >>
      qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`] >>
      simp[] >> gen_tac >>
      mp_tac (Q.INST [`ps` |-> `ps7`] alias_var_mass_release_dead_spills) >> simp[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `!x. alias_var_mass x ps9 <= alias_var_mass x ps8` by
    (gen_tac >> qpat_x_assum `(if _ then _ else _) = (_,ps9)` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_optimistic_swap, pairTheory.SND]) >>
  strip_tac >> gvs[] >>
  qexistsl_tac [`targets`, `reorder_ops`, `ps4`, `topics`, `emit_ops`, `ps7`, `pop_ops`, `ps8`] >>
  simp[] >> gen_tac >>
  mp_tac (Q.INST [`ps` |-> `ps9`] alias_var_mass_release_dead_spills) >>
  first_x_assum (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_regular_plan_var_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `plan_holds (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
     (Var x) ==> MEM x live` by
    (strip_tac >> drule_all alias_emit_reorder_pop_var_support >> simp[]) >>
  strip_tac >> spose_not_then assume_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    metis_tac[alias_var_mass_zero] >>
  `alias_var_mass x emitted = 0` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs] >>
     `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
       (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     mp_tac (Q.INST [`ps` |-> `emitted`, `to_pop` |-> `MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs)`] alias_var_mass_popmany) >>
     simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live \/ MEM x inst.inst_outputs
Proof
  rpt strip_tac >> irule alias_regular_plan_var_support >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> metis_tac[]
QED

Theorem alias_regular_plan_var_mass:
  inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs
Proof
  strip_tac >> drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack)
    <= alias_var_mass x ps` by
    (drule_all alias_emit_reorder_pop_mass >> simp[]) >>
  `alias_var_mass x emitted <= alias_var_mass x ps + LIST_ELEM_COUNT x inst.inst_outputs` by
    (qpat_x_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `alias_var_mass x post <= alias_var_mass x emitted` by
    (qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     IF_CASES_TAC >> simp[] >> strip_tac >> gvs[] >>
     metis_tac[alias_var_mass_popmany, pairTheory.SND]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >> decide_tac
QED

Theorem alias_regular_plan_var_budget:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_mass x qs <= 1
Proof
  strip_tac >> drule_all alias_regular_plan_var_mass >>
  disch_then (qspec_then `x` mp_tac) >>
  Cases_on `MEM x inst.inst_outputs`
  >- (`alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >> simp[]) >>
  `LIST_ELEM_COUNT x inst.inst_outputs = 0` by
    (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >> simp[]
QED

Theorem alias_distinct_output_count:
  !xs:string list. !x. ALL_DISTINCT xs ==> LIST_ELEM_COUNT x xs <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (fs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem alias_regular_plan_budget:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  alias_var_budget [] qs
Proof
  strip_tac >> simp[alias_var_budget_def, LIST_ELEM_COUNT_THM] >> gen_tac >>
  irule alias_regular_plan_var_budget >>
  fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  metis_tac[alias_distinct_output_count]
QED

Theorem alias_regular_plan_var_live_support:
  inst.inst_opcode <> JMP /\ alias_var_mass x ps <= 1 /\
  (plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  LIST_ELEM_COUNT x inst.inst_outputs <= 1 /\
  (MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)) /\
  (~is_halting \/ LENGTH inst.inst_outputs > 1) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  strip_tac >> spose_not_then assume_tac >>
  `MEM x inst.inst_outputs` by
    (drule_all alias_regular_plan_var_support >> simp[]) >>
  `alias_var_mass x ps = 0` by metis_tac[alias_var_mass_zero] >>
  drule_all alias_regular_plan_stages >> strip_tac >>
  `alias_var_mass x (reordered with ps_stack := stack_pop (LENGTH (compute_operands inst)) reordered.ps_stack) = 0` by
    (drule_all alias_emit_reorder_pop_mass >>
     disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `alias_var_mass x residual = 0` >>
  `alias_var_mass x emitted <= 1` by
    (qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. alias_var_mass x (SND p)``) >>
     simp[alias_var_mass_emit_ops, alias_var_mass_outputs]) >>
  `Var x NOTIN FDOM emitted.ps_spilled` by
    (`!outs p. (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
       p outs).ps_spilled = p.ps_spilled` by (Induct >> simp[]) >>
     `Var x NOTIN FDOM residual.ps_spilled` by
       (qpat_x_assum `alias_var_mass x residual = 0` mp_tac >>
        simp[alias_var_mass_def] >> IF_CASES_TAC >> simp[]) >>
     qpat_assum `generate_emit_ops _ _ _ = _`
       (mp_tac o AP_TERM ``\p:stack_op list # plan_state. (SND p).ps_spilled``) >>
     simp[alias_emit_ops_inventory] >> metis_tac[]) >>
  `inst.inst_outputs <> []` by (strip_tac >> fs[]) >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[] >> strip_tac >>
  `alias_var_mass x post = 0` by
    (`MEM (Var x) (MAP Var (FILTER (\out. ~MEM out live) inst.inst_outputs))` by
       simp[MEM_MAP, MEM_FILTER] >>
     drule_all alias_popmany_plan_mass_zero >> simp[]) >>
  qpat_x_assum `!x. alias_var_mass x qs <= _` (qspec_then `x` mp_tac) >>
  `alias_var_mass x qs <> 0` by metis_tac[alias_var_mass_zero] >> decide_tac
QED

Theorem alias_regular_plan_live_support:
  inst.inst_opcode <> JMP /\ alias_var_budget [] ps /\
  (!x. plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==> plan_holds ps op) /\
  LENGTH (compute_operands inst) <= 16 /\
  ALL_DISTINCT inst.inst_outputs /\
  (!x. MEM x inst.inst_outputs ==>
    ~plan_holds ps (Var x) /\ ~MEM (Var x) (compute_operands inst)) /\
  (~is_halting \/ 1 < LENGTH inst.inst_outputs) /\
  generate_regular_inst_plan liveness dfg cfg fn inst live is_halting next_term lbl ps = (ops,qs) ==>
  !x. plan_holds qs (Var x) ==> MEM x live
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt strip_tac >>
  `alias_var_mass x ps <= 1` by fs[alias_var_budget_def, LIST_ELEM_COUNT_THM] >>
  `LIST_ELEM_COUNT x inst.inst_outputs <= 1` by metis_tac[alias_distinct_output_count] >>
  `MEM x inst.inst_outputs ==> ~plan_holds ps (Var x)` by simp[] >>
  `plan_holds ps (Var x) ==> MEM x live \/ MEM (Var x) (compute_operands inst)` by simp[] >>
  drule_all (SRULE [arithmeticTheory.GREATER_DEF] alias_regular_plan_var_live_support) >> simp[]
QED

Definition alias_probe_phis_def:
  alias_probe_phis =
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]]
End

Theorem alias_probe_phi_static_edges:
  phi_uses_disjoint alias_probe_phis /\
  input_vars_from "left" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["a"; "c"; "r"] /\
  input_vars_from "right" alias_probe_phis ["a"; "b"; "c"; "d"; "r"] = ["b"; "d"; "r"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_prefix_ownership:
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "r"; Var "c"] /\
  FILTER (\at. MEM at [Var "c"; Var "d"])
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_stack =
    [Var "c"] /\
  (SND (generate_phi_plan (EL 1 alias_probe_phis) ["q"; "r"] F
    (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
      ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))))).ps_stack =
    [Var "r"; Var "q"] /\
  (SND (generate_phi_plan (HD alias_probe_phis) ["c"; "d"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"; Var "c"]))).ps_spilled = FEMPTY
Proof
  EVAL_TAC
QED

(* Input disjointness alone supplies neither output freshness nor static
   edge choice. In loops SSA alone also permits an output on a backedge.
   A proposed freshness proof must additionally use phi_block_ready's
   dead-after-prefix condition and a liveness witness from the backedge;
   that proof remains an obligation, not a consequence of these fixtures. *)
Theorem alias_probe_phi_disjoint_not_fresh:
  phi_uses_disjoint
    [mk_inst 10 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["c"];
     mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]] /\
  MEM (Var "c") (FILTER is_var_operand
    (mk_inst 11 PHI [Label "left"; Var "c"; Label "right"; Var "d"] ["q"]).inst_operands)
Proof
  EVAL_TAC
QED

(* Proposed remaining-PHI preservation interface: disjoint selected input
   lists A,B, FILTER A stack = [Var a], FILTER B stack = [Var b], no
   incoming spill keys, a dead at this step, output not in A or B and not
   already held. After the step FILTER B stack = [Var b], no B spills,
   and no A held (the latter is alias_phi_singleton_consumed).
   Output freshness needs its own codegen_ready/SSA/liveness boundary.
   Poke preserves the B filter, but optional pop can move the B slot;
   preserve a FILTER singleton, not its absolute depth. The computation
   above exercises that movement with a carried residual r. *)


Theorem plan_holds_cleanup_update[simp]:
  plan_holds
    (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) at
  <=> plan_holds ps at
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_inventory_update[simp]:
  plan_holds (ps with <| ps_stack := stk; ps_spilled := spilled |>) at
  <=> MEM at stk \/ at IN FDOM spilled
Proof
  simp[plan_holds_def]
QED

Theorem plan_holds_init_cleanup[simp]:
  ~plan_holds (init_cleanup_plan_state ch growth spill_base lbl_ctr) at
Proof
  simp[plan_holds_def, init_cleanup_plan_state_def, init_plan_state_def]
QED

(* A successful PHI plan does not, by itself, establish demand coverage. *)
Theorem generate_phi_plan_absent_slot:
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack =
    NONE ==>
  generate_phi_plan inst next_liveness is_halting ps = ([], ps)
Proof
  simp[generate_phi_plan_def]
QED

(* OFFSET bypasses dead-output filtering. Such names must not be confused
   with nontrivial ASSIGN aliases by a static support invariant. *)
Theorem generate_offset_plan_holds_output:
  inst.inst_operands = [Lit n; Label lbl] /\ inst.inst_outputs = [out] ==>
  plan_holds (SND (generate_offset_plan inst ps)) (Var out)
Proof
  simp[generate_offset_plan_def, plan_holds_def, stackModelTheory.stack_push_def]
QED

(* Small computation fixture: an actual DFG, not an assumed equivalence. *)
Definition alias_probe_fn_def:
  alias_probe_fn = mk_raw_function "alias_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 ASSIGN [Var "r"] ["a"];
       mk_inst 2 STOP [] []] |>]
End

(* Demand diagnostics use analyzed liveness of this actual function. *)
Definition alias_demand_probe_fn_def:
  alias_demand_probe_fn = mk_raw_function "demand_probe"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [] ["r"];
       mk_inst 1 PARAM [] ["k"];
       mk_inst 2 ADD [Var "r"; Var "r"] ["z"];
       mk_inst 3 ADD [Var "z"; Var "k"] ["result"];
       mk_inst 4 STOP [] []] |>]
End

Theorem alias_demand_probe_entry_preparation:
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "r") /\
  ~plan_holds (init_cleanup_plan_state NONE [] 0 0) (Var "k") /\
  MEM "r" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 2) /\
  (!x. MEM x ["r"; "k"] ==>
    plan_holds (SND (prepare_params_plan (liveness_analyze alias_demand_probe_fn)
      alias_demand_probe_fn (init_cleanup_plan_state NONE [] 0 0))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

Theorem alias_demand_probe_regular_distinct_live:
  MEM "k" (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with ps_stack := [Var "k"; Var "r"]))) (Var x)) /\
  (!x. MEM x ["z"; "k"] ==>
    plan_holds (SND (generate_regular_inst_plan
      (liveness_analyze alias_demand_probe_fn) (dfg_build_function alias_demand_probe_fn)
      (cfg_analyze alias_demand_probe_fn) alias_demand_probe_fn
      (mk_inst 2 ADD [Var "r"; Var "r"] ["z"])
      (live_vars_at (liveness_analyze alias_demand_probe_fn) "entry" 3)
      T F "entry" ((init_plan_state 0) with <| ps_stack := [Var "r"];
        ps_spilled := FEMPTY |+ (Var "k",0) |>))) (Var x))
Proof
  EVAL_TAC >> simp[] >> metis_tac[]
QED

(* The published path predicate permits inter-block exits before the terminator.
   This witnesses only an interface limitation, not analyzed liveness. *)
Definition alias_path_probe_fn_def:
  alias_path_probe_fn = mk_raw_function "path_probe"
    [<| bb_label := "A"; bb_instructions :=
       [mk_inst 0 PARAM [] ["r"];
        mk_inst 1 ASSIGN [Var "r"] ["a"];
        mk_inst 2 JMP [Label "B"] []] |>;
     <| bb_label := "B"; bb_instructions :=
       [mk_inst 3 ADD [Var "a"; Lit 1w] ["b"];
        mk_inst 4 STOP [] []] |>]
End

Theorem alias_path_probe_early_exit:
  cfg_exec_path (cfg_analyze alias_path_probe_fn) [("A",0);("B",0)] /\
  used_before_defined alias_path_probe_fn.fn_blocks "a" [("A",0);("B",0)] /\
  normalize_operand (dfg_build_function alias_path_probe_fn) [] (Var "a") =
    Var "r" /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_path_probe_fn) "A" 0)
Proof
  EVAL_TAC >> qexists_tac `1` >> simp[] >> EVAL_TAC
QED

Theorem alias_probe_normalize:
  normalize_operand (dfg_build_function alias_probe_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_slots:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "p"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_phi_live_and_dead:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["a"; "p"] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "p"] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_regular_consumption:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ISZERO [Var "a"] ["z"])
    [] F F "entry" ((init_plan_state 0) with ps_stack := [Var "a"; Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

(* Boundary fixtures distinguish transient duplicates from retained ownership. *)
Theorem alias_probe_assign_ownership:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"; "z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["z"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_repeated_operands:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    [] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ADD [Var "a"; Var "a"] ["z"])
    ["a"] F T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem alias_probe_live_then_dead:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 5 ISZERO [Var "a"] ["q"])
    ["z"] F T "entry"
    (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
      ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
      ["a"; "z"] F T "entry"
      ((init_plan_state 0) with ps_stack := [Var "a"]))))).ps_stack = [Var "z"]
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem alias_probe_spill_restore_ownership:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_stack =
    [Var "a"; Var "a"] /\
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0)))).ps_spilled = FEMPTY /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_stack =
    (Var "a" :: REPLICATE 16 (Lit 0w)) ++ [Var "a"] /\
  (SND (emit_one_input ADD ["a"] (Var "a")
    ((init_plan_state 0) with ps_stack := Var "a" :: REPLICATE 16 (Lit 0w)))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

(* Candidate interface (not yet a reachable-state invariant):
   At ordinary boundaries each variable has at most one owner, either one
   stack occurrence or a spill key. Constants/markers may repeat freely.
   Inputs actually read must be covered. Emission needs the transient bound
     count x stack <= count x pending + 1
   and, for spilled x, count x stack <= count x pending; these are the
   occurrence clauses of reorderSim.residual_budget_wf. Its slot/allocator
   clauses are extra obligations, not consequences of coverage.
   emit_input_plan_pending_inventory gives a LOWER bound from coverage;
   emit_input_plan_inventory_accumulation is also a LOWER bound and cannot
   establish the desired upper bound. reorder_one_pending_inventory_wf
   preserves that lower bound only assuming residual_budget_wf and pending
   length <= 16. Thus none of these three is a uniqueness theorem.
   Missing transfer: covered demand + per-variable one-owner + fresh outputs
   + valid spill allocation must yield one-owner after reorder/pop/output,
   with dead nontrivial aliases absent except for untouched branch residuals.
   Support for those residuals is edge/cleanup dependent, not plain liveness.
   OFFSET introduces a fresh root even when dead; PARAM introduces no planner
   operand at dispatch. Halting may retain a dead single output. Restrict live
   support to nontrivial aliases at nonhalting boundaries, not all held names.
   These tests validate the local candidate only, not the lineage induction. *)
Theorem alias_probe_halting_retention:
  (SND (generate_regular_inst_plan ARB (dfg_build_function alias_probe_fn)
    ARB alias_probe_fn (mk_inst 4 ASSIGN [Var "a"] ["z"])
    [] T T "entry" ((init_plan_state 0) with ps_stack := [Var "a"]))).ps_stack =
    [Var "z"]
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_clean_def:
  alias_probe_clean inputs stk height promised =
    clean_stack_plan
      <| ds_inst := FEMPTY |++ [(("pred",0),["a"; "b"]); (("edge",0),inputs)];
         ds_boundary := FEMPTY |>
      (ARB with <| cfg_preds := FEMPTY |+ ("edge",["pred"]);
                   cfg_succs := FEMPTY |+ ("pred",["edge"; "other"]) |>)
      (mk_raw_function "clean_probe"
        [<| bb_label := "pred"; bb_instructions := [] |>])
      <| bb_label := "edge"; bb_instructions := [] |>
      ((init_plan_state 0) with <| ps_stack := stk;
        ps_cleanup_height := height; ps_cleanup_promised := promised |> )
End

Theorem alias_probe_clean_slots:
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; Var "b"] /\
  (SND (alias_probe_clean ["b"] [Var "a"; Var "b"] NONE F)).ps_stack =
    [Var "b"] /\
  (SND (alias_probe_clean ["a"; "b"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (alias_probe_clean [] [Var "a"; Var "b"] NONE T)).ps_stack =
    [dead_stack_marker; dead_stack_marker] /\
  (SND (alias_probe_clean ["a"] [Var "a"; Var "b"] NONE T)).ps_stack =
    [Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_jmp_residual:
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "b"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "b"]))).ps_stack =
    [Var "a"; Var "b"] /\
  (SND (reorder_plan (dfg_build_function alias_probe_fn) [Var "r"; Var "a"]
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "r"]))).ps_stack =
    [Var "r"; Var "a"]
Proof
  EVAL_TAC
QED

Theorem alias_probe_spilled_phi:
  (SND (generate_phi_plan
    (mk_inst 3 PHI [Label "left"; Var "a"; Label "right"; Var "b"] ["p"])
    ["p"] F ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))))
      .ps_spilled = FEMPTY |+ (Var "a",0) /\
  (release_dead_spills []
    ((init_plan_state 0) with ps_spilled := FEMPTY |+ (Var "a",0))).ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Definition alias_probe_loop_fn_def:
  alias_probe_loop_fn = mk_raw_function "loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 3 ASSIGN [Var "r"] ["a"];
          mk_inst 4 ISZERO [Var "a"] ["z"];
          mk_inst 5 JNZ [Var "z"; Label "header"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem alias_probe_loop_liveness:
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "header" 0) /\
  MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 1) /\
  ~MEM "a" (live_vars_at (liveness_analyze alias_probe_loop_fn) "body" 2) /\
  normalize_operand (dfg_build_function alias_probe_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

(* Without dominance, liveness alone admits a stale alias at a root write. *)
Definition alias_probe_bad_loop_fn_def:
  alias_probe_bad_loop_fn = mk_raw_function "bad_loop_probe"
    [<| bb_label := "entry"; bb_instructions :=
         [mk_inst 0 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
         [mk_inst 1 CALLDATASIZE [] ["r"];
          mk_inst 2 ISZERO [Var "a"] ["z"];
          mk_inst 3 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
         [mk_inst 4 ASSIGN [Var "r"] ["a"];
          mk_inst 5 JMP [Label "header"] []] |>]
End

Theorem alias_probe_bad_loop_liveness:
  MEM "a" (live_vars_at (liveness_analyze alias_probe_bad_loop_fn) "header" 0) /\
  normalize_operand (dfg_build_function alias_probe_bad_loop_fn) [] (Var "a") = Var "r"
Proof
  EVAL_TAC >> simp[]
QED

Theorem eval_one_phi_without_predecessor:
  s.vs_prev_bb = NONE ==> eval_one_phi s inst = NONE
Proof
  simp[eval_one_phi_def] >> Cases_on `inst.inst_outputs` >> simp[]
QED

(* Used at each jump of the block induction, for the successor's alias
   premise.  The invariant reads only ps_stack and ps_spilled, so the
   lineage entry state of the successor (its DFS state with ps_after's
   stack and spill map, lineage_entry) inherits it from ps_after.  The
   block's code is the one lineage_state_block_plan regenerates from the
   lineage state ps, with the cleanup fields it chooses.

   The ownership premise is the planner's static entry invariant: every
   variable live into the block along the edge taken is on the stack or
   spilled.  Without it a block could copy (ASSIGN) a variable the planner
   doesn't hold, whose value need not be its root's after a loop
   iteration, and push the copy.

   Why it should hold: a variable defined in the block by ASSIGN of an
   owned operand takes that operand's value, which is its root's; any
   other definition is its own root.  A root's value only changes when
   its definition runs again, and by SSA and def_dominates_uses a
   variable derived from it is then no longer live, so the planner has
   dropped it: popped, overwritten by a PHI poke, or left behind at the
   join reorder of a JMP (every loop header is a join).  An INVOKE
   changes only its own outputs among the caller's variables.  Return-PC
   variables all read ra in the frame view, and so do their roots. *)

(* Notes from a statement check (intuition, not a prescribed proof):
   - Where the planner drops names (stackPlanGen): an operand dead after
     its instruction is consumed rather than duplicated; dead outputs are
     popped at the end of generate_regular_inst_plan when the block does
     not halt (PHI outputs likewise); after a JNZ clean_stack_plan pops
     dead names or marks them dead_stack_marker; release_dead_spills
     drops dead spills after each regular instruction.  reorder_one's
     alias step only swaps the names of two slots.  So a name in ps_after
     is a name of ps (stack or spill map) or an output of bb.
   - A name z live out of bb, not defined in bb, whose root is defined in
     bb, is impossible: bb dominates z's definition (def_dominates_uses,
     transitively along the ASSIGN chain), and an entry path that meets
     bb only at its end, followed by liveness_sound's witness path, misses
     z's definition.  A bb entered around a loop is a join (entry block
     has no predecessors), entered only by JMP (block_entries_ready),
     whose reorder leaves only names live into it.
   - The ps premises tie ps to vs only through ownership and the alias
     premise; ps's names beyond those are bounded by a static invariant
     of lineage states (their names are live out of the lineage
     predecessor, and the vars live along that edge are all held), which
     also covers a run with vs_prev_bb = NONE at a non-entry block.  The
     entry block has no live-in variables.
   - dead_stack_marker is Label "", and Lit/Label operands are fixed by
     normalize_operand, so only Var operands matter.  PHI and INVOKE
     outputs are their own roots.  For return-PC variables, copy_phi_var
     and retpc_shape_ok keep every link of the chain a return-PC
     variable, so both sides read ra. *)
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
Proof
  cheat
QED
