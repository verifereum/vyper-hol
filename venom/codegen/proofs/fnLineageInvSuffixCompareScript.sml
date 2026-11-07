Theory fnLineageInvSuffixCompare
Ancestors fnLineageInvActualReplay fnLineageInvWeakSuffix fnPlanLineageInventory stackPlanGen list rich_list

Theorem analyzed_weak_suffix_common_core:
 !fn bb dfg cfg spillbase p j ps ts ops qs tops us m n core.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j+p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 lineage_core m core ps /\ lineage_core n core ts /\ EVERY is_var_operand core /\
 (ps with ps_stack := []) = (ts with ps_stack := []) /\
 (!x. MEM x [ps;ts] ==>
   residual_budget_wf spillbase [] (x with ps_stack := core) /\
   set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p))) /\
   (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)) ==>
     MEM (Var v) x.ps_stack \/ Var v IN FDOM x.ps_spilled) /\
   EVERY (\inst. EVERY (\v. ~MEM (Var v) x.ps_stack /\
     Var v NOTIN FDOM x.ps_spilled) inst.inst_outputs)
     (DROP (j+p) bb.bb_instructions)) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ts = SOME (tops,us)
 ==>
 ops = tops /\
 FILTER (\op. op <> dead_stack_marker) qs.ps_stack =
 FILTER (\op. op <> dead_stack_marker) us.ps_stack /\
 (qs with ps_stack := []) = (us with ps_stack := [])
Proof
 rpt gen_tac >> strip_tac >>
 `generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ps with ps_stack := REPLICATE n dead_stack_marker ++ ps.ps_stack) =
   SOME (ops,qs with ps_stack := REPLICATE n dead_stack_marker ++ qs.ps_stack)` by
  (irule (cj 4 analyzed_weak_suffix_replay) >> simp[] >>
   qexistsl_tac [`spillbase`,`m`,`core`] >> simp[] >> metis_tac[MEM]) >>
 `generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ts with ps_stack := REPLICATE m dead_stack_marker ++ ts.ps_stack) =
   SOME (tops,us with ps_stack := REPLICATE m dead_stack_marker ++ us.ps_stack)` by
  (irule (cj 4 analyzed_weak_suffix_replay) >> simp[] >>
   qexistsl_tac [`spillbase`,`n`,`core`] >> simp[] >> metis_tac[MEM]) >>
 ` (ps with ps_stack := REPLICATE n dead_stack_marker ++ ps.ps_stack) =
   (ts with ps_stack := REPLICATE m dead_stack_marker ++ ts.ps_stack)` by
  (fs[lineage_core_def, stackPlanTypesTheory.plan_state_component_equality] >>
   simp[APPEND_ASSOC, REPLICATE_APPEND, arithmeticTheory.ADD_COMM]) >>
 qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ (ps with ps_stack := _) = _` mp_tac >>
 simp[] >> strip_tac >>
 qpat_x_assum `(us with ps_stack := _) = _` mp_tac >>
 simp[stackPlanTypesTheory.plan_state_component_equality] >> strip_tac >>
 `FILTER (\op. op <> dead_stack_marker)
    (REPLICATE m dead_stack_marker ++ us.ps_stack) =
  FILTER (\op. op <> dead_stack_marker)
    (REPLICATE n dead_stack_marker ++ qs.ps_stack)` by simp[] >>
 `!k. FILTER (\op. op <> dead_stack_marker)
        (REPLICATE k dead_stack_marker) = []` by
   simp[FILTER_EQ_NIL, EVERY_REPLICATE] >>
 fs[FILTER_APPEND]
QED

Theorem analyzed_weak_suffix_common_core_cleanup:
 !fn bb dfg cfg spillbase p j ps ts ops qs tops us m n core.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j+p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 lineage_core m core ps /\ lineage_core n core ts /\ EVERY is_var_operand core /\
 (ps with <|ps_stack := []; ps_cleanup_height := NONE; ps_cleanup_promised := F|>) =
 (ts with <|ps_stack := []; ps_cleanup_height := NONE; ps_cleanup_promised := F|>) /\
 (!x. MEM x [ps;ts] ==>
   residual_budget_wf spillbase [] (x with ps_stack := core) /\
   set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p))) /\
   (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)) ==>
     MEM (Var v) x.ps_stack \/ Var v IN FDOM x.ps_spilled) /\
   EVERY (\inst. EVERY (\v. ~MEM (Var v) x.ps_stack /\
     Var v NOTIN FDOM x.ps_spilled) inst.inst_outputs)
     (DROP (j+p) bb.bb_instructions)) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ts = SOME (tops,us)
 ==>
 ops = tops /\
 FILTER (\op. op <> dead_stack_marker) qs.ps_stack =
 FILTER (\op. op <> dead_stack_marker) us.ps_stack /\
 (qs with <|ps_stack := []; ps_cleanup_height := NONE; ps_cleanup_promised := F|>) =
 (us with <|ps_stack := []; ps_cleanup_height := NONE; ps_cleanup_promised := F|>)
Proof
 rpt gen_tac >> strip_tac >>
 `generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ps with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>) =
   SOME (ops,qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>)` by
   simp[generate_block_insts_plan_cleanup_frame] >>
 `generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ts with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>) =
   SOME (tops,us with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>)` by
   simp[generate_block_insts_plan_cleanup_frame] >>
 drule_at (Pat `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`)
   analyzed_weak_suffix_common_core >>
 disch_then (qspec_then `spillbase` mp_tac) >>
 disch_then (qspec_then `ps with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>` mp_tac) >>
 disch_then (qspecl_then [`ops`, `qs with <|ps_cleanup_height := NONE; ps_cleanup_promised := F|>`, `n`, `m`, `core`] mp_tac) >>
 simp[lineage_core_def] >>
 impl_tac >-
  (qpat_assum `!x. MEM x [ps;ts] ==> _` (qspec_then `ps` assume_tac) >>
   qpat_assum `!x. MEM x [ps;ts] ==> _` (qspec_then `ts` assume_tac) >>
   qpat_x_assum `!x. MEM x [ps;ts] ==> _` kall_tac >>
   fs[MEM, lineage_core_def] >> rpt strip_tac >> gvs[] >>
   fs[reorderSimTheory.residual_budget_wf_def,
      planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
 metis_tac[]
QED
