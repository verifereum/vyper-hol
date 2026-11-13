Theory fnLineageInvWeakSuffix
Ancestors fnLineageInvWeakStep fnLineageInvControl fnLineageInvBoundary
  fnPlanLineageInventory stackPlanGen venomInst list rich_list pred_set finite_map

Theorem analyzed_weak_suffix_replay:
 !fn bb dfg cfg base p j ps ops qs r.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j+p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 (?m core. lineage_core m core ps /\ EVERY is_var_operand core /\
   residual_budget_wf base [] (ps with ps_stack := core) /\
   set core SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))) /\
 (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)) ==>
   MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
 EVERY (\inst. EVERY (\v. ~MEM (Var v) ps.ps_stack /\
   Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs) (DROP (j+p) bb.bb_instructions) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs)
 ==>
 (?n tail. lineage_core n tail qs /\ EVERY is_var_operand tail /\
   residual_budget_wf base [] (qs with ps_stack := tail) /\
   set tail SUBSET set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)))) /\
 (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)) ==>
   MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
 (j+p < LENGTH bb.bb_instructions /\
   (LAST bb.bb_instructions).inst_opcode <> NOP /\
   (LAST bb.bb_instructions).inst_opcode <> OFFSET ==>
   lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)))) qs) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions)
   (ps with ps_stack := REPLICATE r dead_stack_marker ++ ps.ps_stack) =
 SOME (ops,qs with ps_stack := REPLICATE r dead_stack_marker ++ qs.ps_stack)
Proof
 rpt gen_tac >>
 map_every qid_spec_tac [`ps`,`ops`,`qs`,`j`] >>
 measureInduct_on `LENGTH bb.bb_instructions - (j+p)` >>
 rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `j+p = LENGTH bb.bb_instructions`
 >- (gvs[DROP_LENGTH_TOO_LONG, generate_block_insts_plan_def] >> metis_tac[]) >>
 `j+p < LENGTH bb.bb_instructions` by decide_tac >>
 `DROP (j+p) bb.bb_instructions =
    EL (j+p) bb.bb_instructions :: DROP (SUC (j+p)) bb.bb_instructions` by
   simp[DROP_CONS_EL] >>
 `DROP (SUC (j+p)) bb.bb_instructions = [] ==>
    SUC (j+p) = LENGTH bb.bb_instructions` by
   (simp[DROP_EQ_NIL] >> decide_tac) >>
 qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 once_rewrite_tac[generate_block_insts_plan_def] >> asm_rewrite_tac[] >>
 simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
 ` (if LENGTH bb.bb_instructions <= SUC (j+p) then
      live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label (j+(p+1))) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))` by
   (IF_CASES_TAC >> simp[] >> AP_TERM_TAC >> decide_tac) >>
 gvs[] >>
 drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`) analyzed_weak_envelope_step >>
 disch_then (qspecl_then [`m`,`core`,`base'`] mp_tac) >>
 (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
 suspend "compose"
QED

Resume analyzed_weak_suffix_replay[compose]:
 Cases_on `SUC (j+p) = LENGTH bb.bb_instructions`
 >- suspend "last" >>
 qpat_x_assum `!y. LENGTH _ < _ ==> _` (qspec_then `SUC (j+p)` mp_tac) >>
 (impl_tac >- decide_tac) >>
 disch_then (qspecl_then [`j+1`,`p`] mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES] >>
 disch_then (qspecl_then [`qs`,`rest_ops`,`ps'`] mp_tac) >>
 `j+(p+1) = SUC (j+p)` by decide_tac >> asm_rewrite_tac[] >>
 (impl_tac >- (simp[] >> qexistsl_tac [`n`,`tail`] >> simp[])) >>
 strip_tac >>
 conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
 conj_tac >- (strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
 once_rewrite_tac[generate_block_insts_plan_def] >> asm_rewrite_tac[] >>
 `~(DROP (SUC (j+p)) bb.bb_instructions = [])` by (simp[DROP_EQ_NIL] >> decide_tac) >>
 simp[] >> asm_rewrite_tac[]
QED

Resume analyzed_weak_suffix_replay[last]:
 `bb.bb_instructions <> []` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
 `LAST bb.bb_instructions = EL (j+p) bb.bb_instructions` by
   (`j+p = PRE (LENGTH bb.bb_instructions)` by decide_tac >> simp[LAST_EL]) >>
 gvs[DROP_LENGTH_TOO_LONG, generate_block_insts_plan_def] >>
 qexistsl_tac [`n`,`tail`] >> simp[]
QED

Finalise analyzed_weak_suffix_replay
