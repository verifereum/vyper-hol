(*
 * Where region i's plan comes from and how it starts, for
 * fnEntryStep$fn_entry_block_step.
 *
 * TOP-LEVEL:
 *   region_fn_plan   - region i's plan is the function planner's output
 *                      for some label counter
 *   entry_block_plan - a function plan starts with the entry block's
 *                      label, parameter code and instructions' code
 *)

Theory fnEntryPlan
Ancestors
  fnBlockBody fnBlockPlanStatic fnPlanPrefix fnPlanLineage fnPlanPlaceFnRegion allocMono stackPlanGen
  stackPlanTypes fcgDefs livenessDefs dfgDefs cfgDefs venomInst venomWf
  list rich_list arithmetic

(* Helper: generate_context_regions_provenance with the region's name and
   spill end, which it records from the function and the planner's final
   state. *)
Theorem generate_context_regions_region_fields[local]:
  !fns acc out.
  generate_context_regions gen fns acc = SOME out ==>
  LENGTH out.cpa_regions = LENGTH acc.cpa_regions + LENGTH fns /\
  TAKE (LENGTH acc.cpa_regions) out.cpa_regions = acc.cpa_regions /\
  (!i. i < LENGTH fns ==>
    (EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_fn_name =
      (EL i fns).fn_name /\
    ?ctr ps. gen (EL i fns)
      (EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_spill_base ctr =
      SOME ((EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_plan, ps) /\
      ps.ps_alloc.sa_next_offset =
        (EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_spill_end)
Proof
  Induct_on `fns` >- simp[generate_context_regions_def] >>
  rpt gen_tac >>
  simp[Once generate_context_regions_def, AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_context_regions gen fns next` >>
  first_x_assum drule >> strip_tac >>
  gvs[Abbr `next`, LENGTH_SNOC] >>
  conj_tac >-
    (qpat_x_assum `TAKE (SUC _) _ = _`
       (mp_tac o Q.AP_TERM `TAKE (LENGTH acc.cpa_regions)`) >>
     simp[TAKE_TAKE, TAKE_SNOC, MIN_DEF]) >>
  Cases_on `i` >> simp[] >-
    (qpat_x_assum `TAKE (SUC _) _ = _` (mp_tac o Q.AP_TERM `EL (LENGTH acc.cpa_regions)`) >>
     simp[EL_TAKE, EL_LENGTH_SNOC] >> strip_tac >>
     qexistsl_tac [`acc.cpa_label_counter`, `ps`] >> simp[]) >>
  strip_tac >> first_x_assum drule >> simp[arithmeticTheory.ADD_CLAUSES]
QED

(* generate_context_plan runs the function planner on each function in
   order, with the region's spill base and the label counter the earlier
   regions left, and records the function's name and the planner's final
   spill offset in the region.  cp does not record the counter, so it is
   existential. *)
Theorem region_fn_plan:
  !ctx cp i fn r.
    generate_context_plan ctx = SOME cp /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r ==>
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    ?lbl_ctr ps_end.
      generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn)
        (dfg_build_function fn) (cfg_analyze fn)
        (cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name)
        (cleanup_growth_table ctx (fcg_analyze ctx)) fn
        r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
      ps_end.ps_alloc.sa_next_offset = r.sr_spill_end
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_context_plan _ = _` mp_tac >>
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >> strip_tac >>
  drule generate_context_regions_region_fields >> strip_tac >>
  gvs[finish_context_plan_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[generate_fn_plan_with_cleanup_def] >>
  simp[MEM_EL] >> metis_tac[]
QED

Theorem entry_plan_first_block[local]:
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn spill_base ctr =
    SOME (ops, pend) ==>
  fn.fn_blocks <> [] /\
  fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
  lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks =
    SOME (HD fn.fn_blocks) /\
  ?bops pa rest.
    generate_block_plan lv dfg cfg fn (HD fn.fn_blocks)
      (init_cleanup_plan_state ch growth spill_base ctr) = SOME (bops, pa) /\
    ops = bops ++ rest /\
    pa.ps_alloc.sa_next_offset <= pend.ps_alloc.sa_next_offset
Proof
  Cases_on `fn.fn_blocks` >-
    simp[generate_fn_plan_with_cleanup_analyzed_def, callLayoutDefsTheory.canonical_param_prefix_def] >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, fn_entry_label_def,
       entry_block_def] >>
  simp[Once generate_fn_plan_aux_def, lookup_block_def, FIND_thm] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule (cj 2 fn_plan_aux_alloc_mono) >> strip_tac >>
  drule (cj 1 fn_plan_aux_alloc_mono) >> strip_tac >>
  decide_tac
QED

Theorem entry_plan_param_boundary[local]:
  codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
  generate_block_plan lv dfg (cfg_analyze fn) fn (HD fn.fn_blocks) ps0 =
    SOME (bops, pa) ==>
  ?pops ps1 body.
    prepare_params_plan lv fn ps0 = (pops, ps1) /\
    bops = SOLabel (HD fn.fn_blocks).bb_label :: pops ++ body /\
    block_plan_state lv dfg (cfg_analyze fn) fn (HD fn.fn_blocks) ps0
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 /\
    generate_block_insts_plan lv dfg (cfg_analyze fn) fn
      (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
      (LENGTH (HD fn.fn_blocks).bb_instructions) 0
      (non_param_insts (HD fn.fn_blocks)) ps1 = SOME (body, pa) /\
    ps1.ps_alloc.sa_next_offset <= pa.ps_alloc.sa_next_offset
Proof
  `!insts i ps ops ps'.
     generate_block_insts_plan lv dfg (cfg_analyze fn) fn
       (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
       (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
       (LENGTH (HD fn.fn_blocks).bb_instructions) i insts ps = SOME (ops, ps') ==>
     ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset` by
    (Induct_on `insts` >> rpt gen_tac >>
     simp[Once generate_block_insts_plan_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     drule generate_inst_plan_next_offset >> strip_tac >>
     first_x_assum drule >> strip_tac >> decide_tac) >>
  strip_tac >>
  `cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []` by
    (qpat_x_assum `codegen_ready_fn _` mp_tac >>
     Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, block_entries_ready_def, entry_block_def,
         NULL_EQ]) >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[block_plan_state_def, generate_block_insts_prefix_def] >>
  metis_tac[]
QED

(* The DFS planner starts at the entry label from the initial state ps0,
   so the entry block is planned first, from ps0: the plan begins with the
   entry block's code, its label, its parameter code (prepare_params_plan)
   and its instructions' code.  The entry block has no predecessors
   (block_entries_ready), so there is no cleanup code, and the planner
   state after the parameters is the block_plan_state at the first
   non-parameter instruction.  The allocator only grows along the plan, so
   that state's next offset is at most the final one. *)
Theorem entry_block_plan:
  !liveness dfg ch growth fn spill_base lbl_ctr ops ps_end.
    codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg (cfg_analyze fn) ch
      growth fn spill_base lbl_ctr = SOME (ops, ps_end) ==>
    ?param_ops ps1 body_ops ps_after rest_ops.
      prepare_params_plan liveness fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
        (param_ops, ps1) /\
      generate_block_plan liveness dfg (cfg_analyze fn) fn (HD fn.fn_blocks)
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) =
        SOME (SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops,
              ps_after) /\
      block_plan_state liveness dfg (cfg_analyze fn) fn (HD fn.fn_blocks)
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) ps1 /\
      generate_block_insts_plan liveness dfg (cfg_analyze fn) fn
        (HD fn.fn_blocks).bb_label (bb_is_halting (HD fn.fn_blocks))
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
        (LENGTH (HD fn.fn_blocks).bb_instructions) 0
        (non_param_insts (HD fn.fn_blocks)) ps1 = SOME (body_ops, ps_after) /\
      ops = SOLabel (HD fn.fn_blocks).bb_label :: param_ops ++ body_ops ++
            rest_ops /\
      fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label /\
      lookup_block (HD fn.fn_blocks).bb_label fn.fn_blocks =
        SOME (HD fn.fn_blocks) /\
      dfs_block_state liveness dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)
        (HD fn.fn_blocks).bb_label
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) /\
      ps1.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >>
  drule entry_plan_first_block >> strip_tac >>
  drule_all entry_plan_param_boundary >> strip_tac >> gvs[] >-
    (simp[dfs_block_state_def] >>
     qexistsl_tac [`[]`, `[]`] >> simp[dfs_aux_call_entry]) >>
  decide_tac
QED
