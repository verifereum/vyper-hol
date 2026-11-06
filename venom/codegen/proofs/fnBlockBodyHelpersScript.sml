(*
 * Generic helpers for fnBlockBody$block_body_frame_sim: the planner's
 * step from one instruction of a block to the next, the parameter prefix
 * of a block, the function's region and DFS allocator, operand and label
 * facts for the instruction lemmas, and how exec_block unfolds.
 *
 * Some of these copy lemmas of fnBlockStepHelpers, which imports
 * fnBlockBody and so can't be imported here.
 *)

Theory fnBlockBodyHelpers
Ancestors
  fnBlockPlanStatic fnLineageStatic fnPlanPrefix fnPlanLineage
  fnPlanPlaceDfsBlock fnPlanPlaceFnRegion fnPlanCover allocMono
  planSpillBounds contextPlanLayoutProps unitShapeDefs contextCodegenRel
  codegenRel frameRel fnSimSpec venomExecProofs venomExecProps
  venomInstProps stackOpSim blockSimHelpers genBlockSim callLayoutDefs
  stackPlanGen stackPlanTypes stackModel planExec asmSem
  stepWriteFootprintForward venomWf venomExecSemantics venomState venomInst
  asmIR dfgDefs list rich_list arithmetic finite_map option

(* ===== Fields the relations do not read ===== *)

Theorem operand_val_inst_idx:
  !s k lo at.
    operand_val (s with vs_inst_idx := k) lo at = operand_val s lo at
Proof
  rpt gen_tac >> Cases_on `at` >> simp[operand_val_def]
QED

Theorem frame_view_inst_idx:
  !fn ra vs k.
    frame_view fn ra (vs with vs_inst_idx := k) =
    frame_view fn ra vs with vs_inst_idx := k
Proof
  simp[frame_view_def]
QED

Theorem fn_frame_inv_inst_idx:
  !ctx cpl lo fn ra rest mem0 ps vs k as.
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps (vs with vs_inst_idx := k) as <=>
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def, frame_view_inst_idx,
       plan_stack_rel_def, plan_spill_rel_def, operand_val_inst_idx] >>
  simp[frame_view_def]
QED

(* fn_frame_inv reads a planner state's slots and its allocator only. *)
Theorem fn_frame_inv_same_slots:
  !ctx cpl lo fn ra rest mem0 ps ps2 vs as r.
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    ps2.ps_stack = ps.ps_stack /\ ps2.ps_spilled = ps.ps_spilled /\
    MEM r cpl.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps2 vs as
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def] >> rpt strip_tac >>
  TRY (qexists_tac `top` >> simp[]) >> metis_tac[]
QED

(* ===== The function's region (copied from fnBlockStepHelpers) ===== *)

Theorem body_context_regions_fn_name:
  !fns acc out.
    generate_context_regions gen fns acc = SOME out ==>
    !i. i < LENGTH fns ==>
      (EL (LENGTH acc.cpa_regions + i) out.cpa_regions).sr_fn_name =
      (EL i fns).fn_name
Proof
  Induct_on `fns` >- simp[] >>
  rpt gen_tac >>
  simp[Once generate_context_regions_def, AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_context_regions gen fns next` >>
  first_x_assum drule >> strip_tac >>
  drule generate_context_regions_provenance >> strip_tac >>
  gvs[Abbr `next`, LENGTH_SNOC] >>
  Cases_on `i` >> simp[]
  >- (qpat_x_assum `TAKE (SUC _) _ = _`
        (mp_tac o Q.AP_TERM `EL (LENGTH acc.cpa_regions)`) >>
      simp[EL_TAKE, EL_LENGTH_SNOC])
  >> qpat_x_assum `!i. i < LENGTH fns ==> (EL _ _).sr_fn_name = _`
       (qspec_then `n` mp_tac) >> simp[ADD_CLAUSES]
QED

Theorem body_context_region_fn_name:
  !ctx cpl i.
    generate_context_plan ctx = SOME cpl /\ i < LENGTH ctx.ctx_functions ==>
    MEM (EL i cpl.cp_regions) cpl.cp_regions /\
    (EL i cpl.cp_regions).sr_fn_name = (EL i ctx.ctx_functions).fn_name
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_regions_length >> strip_tac >>
  conj_tac >- (irule EL_MEM >> simp[]) >>
  qpat_x_assum `generate_context_plan _ = _` mp_tac >>
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[finish_context_plan_def] >>
  drule body_context_regions_fn_name >> simp[]
QED

Theorem body_region_spill_offsets:
  !ctx cpl r pre ops post off.
    generate_context_plan ctx = SOME cpl /\ MEM r cpl.cp_regions /\
    r.sr_plan = pre ++ ops ++ post /\
    (MEM (SOSpill off) ops \/ MEM (SORestore off) ops) ==>
    off < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_access_bounded >> simp[EVERY_MEM] >>
  strip_tac >>
  drule generate_context_plan_spill_gap >> strip_tac >>
  `region_spill_access r off` by simp[region_spill_access_def] >>
  `off + 32 <= r.sr_spill_end /\ r.sr_spill_end <= cpl.cp_initial_fmp` by
    metis_tac[] >>
  decide_tac
QED

(* ===== The DFS planner's allocator (copied from fnBlockStepHelpers) ===== *)

Theorem body_dfs_calls_alloc_bounded:
  !lv dfg cfg fn ps0.
  (!wl visited ps.
    dfs_aux_call lv dfg cfg fn ps0 wl visited ps ==>
    !entry root_ops root_vis root_ps.
      fn_entry_label fn = SOME entry /\
      generate_fn_plan_aux lv dfg cfg fn [entry] [] ps0 =
        SOME (root_ops, root_vis, root_ps) ==>
      ?ops vis' ps'.
        generate_fn_plan_aux lv dfg cfg fn wl visited ps =
          SOME (ops, vis', ps') /\
        ps'.ps_alloc.sa_spill_base = root_ps.ps_alloc.sa_spill_base /\
        ps'.ps_alloc.sa_next_offset <= root_ps.ps_alloc.sa_next_offset) /\
  (!saved spilled succs visited ps.
    dfs_succs_call lv dfg cfg fn ps0 saved spilled succs visited ps ==>
    !entry root_ops root_vis root_ps.
      fn_entry_label fn = SOME entry /\
      generate_fn_plan_aux lv dfg cfg fn [entry] [] ps0 =
        SOME (root_ops, root_vis, root_ps) ==>
      ?ops vis' ps'.
        generate_succs_plan lv dfg cfg fn saved spilled succs visited ps =
          SOME (ops, vis', ps') /\
        ps'.ps_alloc.sa_spill_base = root_ps.ps_alloc.sa_spill_base /\
        ps'.ps_alloc.sa_next_offset <= root_ps.ps_alloc.sa_next_offset)
Proof
  rpt gen_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[])
  >- suspend "visited"
  >- suspend "missing"
  >- suspend "succs"
  >- suspend "rest"
  >- suspend "branch"
  >> suspend "sibling"
QED

Resume body_dfs_calls_alloc_bounded[visited]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def]
QED

Resume body_dfs_calls_alloc_bounded[missing]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def]
QED

Resume body_dfs_calls_alloc_bounded[succs]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_alloc_mono) >> gvs[]
QED

Resume body_dfs_calls_alloc_bounded[rest]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Resume body_dfs_calls_alloc_bounded[branch]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 2 fn_plan_aux_alloc_mono) >> gvs[]
QED

Resume body_dfs_calls_alloc_bounded[sibling]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Finalise body_dfs_calls_alloc_bounded

Theorem body_dfs_block_alloc_bounded:
  !lv dfg cfg ch growth fn sbase ctr fn_ops ps_end lbl ps bb block_ops
   ps_after.
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sbase ctr =
      SOME (fn_ops, ps_end) /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth sbase ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops, ps_after) ==>
    ps_after.ps_alloc.sa_spill_base = sbase /\
    ps_after.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >>
  gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_entry_exists) >> strip_tac >>
  qpat_x_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`
    mp_tac >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule (cj 1 body_dfs_calls_alloc_bounded) >> disch_then drule_all >>
  strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (lbl::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_alloc_mono) >>
  imp_res_tac (cj 2 fn_plan_aux_alloc_mono) >>
  gvs[init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]
QED

(* The DFS state a block is planned from lies in the function's region. *)
Theorem body_dfs_state_region:
  !lv dfg cfg ch growth fn sbase ctr fn_ops ps_end lbl ps bb block_ops
   ps_after.
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sbase ctr =
      SOME (fn_ops, ps_end) /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth sbase ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops, ps_after) ==>
    ps.ps_alloc.sa_spill_base = sbase /\
    ps.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_dfs_block_alloc_bounded >> strip_tac >>
  drule generate_block_plan_alloc_mono >> strip_tac >> gvs[]
QED

(* ===== The function's static shape ===== *)

Theorem body_ready_fn_no_marker:
  !fn. codegen_ready_fn fn ==>
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks
Proof
  simp[codegen_ready_fn_def, codegen_ready_inst_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem body_fn_shape:
  !ctx unit Inv cpl i fn.
    ctx = unit.cu_context /\ unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cpl /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn ==>
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    fn_entry_label fn = SOME fn.fn_name /\
    EVERY inst_shape_ok (fn_insts fn)
Proof
  simp[unit_shape_ok_def, codegen_context_obligations_def, codegen_ready_def,
       EVERY_EL, fn_shape_ok_def] >>
  metis_tac[]
QED

Theorem body_inst_ready:
  !fn bb inst.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    codegen_ready_inst inst /\ inst_wf inst /\ MEM inst (fn_insts fn)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[MEM_fn_insts_blocks]) >>
  gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[]
QED

(* ===== A block's parameter prefix ===== *)

Theorem no_param_get_params:
  !insts. no_param_insts insts ==> get_params insts = []
Proof
  Cases >> simp[no_param_insts_def, get_params_def]
QED

Theorem filter_non_param_drop:
  !insts.
    no_param_insts (DROP (LENGTH (get_params insts)) insts) ==>
    FILTER (\inst. ~is_param_opcode inst.inst_opcode) insts =
    DROP (LENGTH (get_params insts)) insts
Proof
  Induct >> simp[get_params_def] >> rpt gen_tac >>
  Cases_on `is_param_opcode h.inst_opcode` >> simp[] >>
  simp[no_param_insts_def, FILTER_EQ_ID]
QED

Theorem canonical_after_fmp_drop:
  !k insts. canonical_after_fmp k insts ==>
    no_param_insts (DROP (LENGTH (get_params insts)) insts)
Proof
  gen_tac >> Cases >- simp[get_params_def, no_param_insts_def] >>
  simp[canonical_after_fmp_def] >> IF_CASES_TAC >> strip_tac >>
  imp_res_tac no_param_get_params >>
  gvs[get_params_def, is_param_opcode_def]
QED

Theorem canonical_entry_params_drop:
  !insts k. canonical_entry_params_from k insts ==>
    no_param_insts (DROP (LENGTH (get_params insts)) insts)
Proof
  Induct >- simp[get_params_def, no_param_insts_def] >>
  simp[canonical_entry_params_from_def] >> rpt gen_tac >>
  rpt IF_CASES_TAC >> strip_tac >>
  imp_res_tac no_param_get_params >>
  gvs[get_params_def, is_param_opcode_def]
  >- metis_tac[]
  >> drule canonical_after_fmp_drop >> simp[]
QED

Theorem non_param_insts_drop:
  !fn bb.
    canonical_param_prefix fn /\ MEM bb fn.fn_blocks ==>
    non_param_insts bb =
    DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >> simp[non_param_insts_def] >>
  irule filter_non_param_drop >>
  Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def]
  >- metis_tac[canonical_entry_params_drop] >>
  gvs[EVERY_MEM] >> first_x_assum drule >> strip_tac >>
  imp_res_tac no_param_get_params >> simp[]
QED

(* ===== The planner's step from instruction k to k + 1 ===== *)

Theorem generate_block_insts_prefix_snoc:
  !insts i j ps pre mid ops ps' lv dfg cfg fn lbl hl np len.
    generate_block_insts_prefix lv dfg cfg fn lbl hl np len i j insts ps =
      SOME (pre, mid) /\
    j < LENGTH insts /\
    generate_inst_plan lv dfg cfg fn (EL j insts)
      (if SUC j = LENGTH insts then live_vars_at lv lbl len
       else live_vars_at lv lbl (i + j + np + 1))
      hl (SUC j < LENGTH insts /\ is_terminator (EL (SUC j) insts).inst_opcode)
      lbl mid = SOME (ops, ps') ==>
    generate_block_insts_prefix lv dfg cfg fn lbl hl np len i (SUC j) insts ps =
      SOME (pre ++ ops, ps')
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `j`
  >- (ONCE_REWRITE_TAC [generate_block_insts_prefix_def] >>
      Cases_on `insts` >>
      simp[generate_block_insts_prefix_def, LET_THM] >>
      rpt strip_tac >> gvs[])
  >> rename1 `SUC n` >>
  ONCE_REWRITE_TAC [generate_block_insts_prefix_def] >>
  simp[LET_THM, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >>
  gvs[] >> first_x_assum irule >>
  `i + (np + (SUC n + 1)) = i + (n + (np + 2))` by decide_tac >>
  gvs[]
QED

Theorem generate_block_insts_plan_cons_step:
  !insts lv dfg cfg fn lbl hl np len i ps ops_all ps_end.
    generate_block_insts_plan lv dfg cfg fn lbl hl np len i insts ps =
      SOME (ops_all, ps_end) /\ insts <> [] ==>
    ?ops ps' rest'.
      generate_inst_plan lv dfg cfg fn (HD insts)
        (if TL insts = [] then live_vars_at lv lbl len
         else live_vars_at lv lbl (i + np + 1))
        hl (TL insts <> [] /\ is_terminator (HD (TL insts)).inst_opcode)
        lbl ps = SOME (ops, ps') /\
      generate_block_insts_plan lv dfg cfg fn lbl hl np len (i + 1) (TL insts)
        ps' = SOME (rest', ps_end) /\
      ops_all = ops ++ rest'
Proof
  Cases >> simp[] >> rpt gen_tac >>
  simp[Once generate_block_insts_plan_def, LET_THM, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* The step at instruction k of the block, in the form
   block_plan_state_static takes: lookahead at k + 1. *)
Theorem block_insts_plan_step:
  !lv dfg cfg fn bb k ps ops_all ps_end.
    non_param_insts bb =
      DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    LENGTH (get_params bb.bb_instructions) <= k /\
    k < LENGTH bb.bb_instructions /\
    generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions))
      (DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps = SOME (ops_all, ps_end) ==>
    ?ops ps' rest'.
      generate_inst_plan lv dfg cfg fn (EL k bb.bb_instructions)
        (live_vars_at lv bb.bb_label (k + 1)) (bb_is_halting bb)
        (k + 1 < LENGTH bb.bb_instructions /\
         is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
        bb.bb_label ps = SOME (ops, ps') /\
      generate_block_insts_plan lv dfg cfg fn bb.bb_label (bb_is_halting bb)
        (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
        (SUC k - LENGTH (get_params bb.bb_instructions))
        (DROP (SUC k - LENGTH (get_params bb.bb_instructions))
           (non_param_insts bb))
        ps' = SOME (rest', ps_end) /\
      ops_all = ops ++ rest'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `np = LENGTH (get_params bb.bb_instructions)` >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  `DROP (k - np) (non_param_insts bb) = DROP k insts /\
   DROP (SUC k - np) (non_param_insts bb) = DROP (SUC k) insts` by
    simp[DROP_DROP_T] >>
  `DROP k insts = EL k insts :: DROP (SUC k) insts` by
    simp[DROP_EL_CONS, ADD1] >>
  gvs[] >>
  drule generate_block_insts_plan_cons_step >> simp[] >> strip_tac >>
  `k - np + np = k` by decide_tac >>
  `k - np + 1 = SUC k - np` by decide_tac >>
  Cases_on `k + 1 < LENGTH insts`
  >- (`DROP (SUC k) insts = EL (k + 1) insts :: DROP (SUC (k + 1)) insts` by
        simp[DROP_EL_CONS, ADD1] >>
      gvs[ADD1] >> metis_tac[])
  >> `DROP (SUC k) insts = [] /\ k + 1 = LENGTH insts` by
       simp[DROP_LENGTH_TOO_LONG] >>
  gvs[ADD1] >> metis_tac[]
QED

Theorem block_plan_state_step:
  !lv dfg cfg fn bb ps_in k ps ops ps'.
    block_plan_state lv dfg cfg fn bb ps_in k ps /\
    non_param_insts bb =
      DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\
    generate_inst_plan lv dfg cfg fn (EL k bb.bb_instructions)
      (live_vars_at lv bb.bb_label (k + 1)) (bb_is_halting bb)
      (k + 1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (k + 1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (ops, ps') ==>
    block_plan_state lv dfg cfg fn bb ps_in (SUC k) ps'
Proof
  rpt gen_tac >> simp[block_plan_state_def] >> strip_tac >>
  qexistsl_tac [`param_ops`, `ps1`, `clean_ops`, `ps2`, `pre_ops ++ ops`] >>
  simp[] >>
  qabbrev_tac `np = LENGTH (get_params bb.bb_instructions)` >>
  `SUC k - np = SUC (k - np)` by decide_tac >>
  pop_assum SUBST1_TAC >>
  irule generate_block_insts_prefix_snoc >> simp[] >>
  `k - np < LENGTH bb.bb_instructions - np /\
   EL (k - np) (DROP np bb.bb_instructions) = EL k bb.bb_instructions` by
    simp[EL_DROP] >>
  `k - np + np = k` by decide_tac >>
  simp[EL_DROP, ADD1] >>
  `SUC (k - np) + np = k + 1` by decide_tac >>
  simp[EL_DROP] >>
  Cases_on `k + 1 = LENGTH bb.bb_instructions` >> gvs[] >>
  `k + 1 < LENGTH bb.bb_instructions /\ k + 1 - np + np = k + 1` by
    decide_tac >>
  `EL (k + 1 - np) (DROP np bb.bb_instructions) =
   EL (k + 1) bb.bb_instructions` by metis_tac[EL_DROP] >>
  gvs[]
QED

(* ===== Operands and labels ===== *)

Theorem stack_get_depth_MEM:
  !op stk d. stack_get_depth op stk = SOME d ==> MEM op stk
Proof
  rpt strip_tac >> drule stack_get_depth_props >>
  simp[stack_peek_def] >> strip_tac >>
  `LENGTH stk - (d + 1) < LENGTH stk` by decide_tac >>
  metis_tac[EL_MEM]
QED

(* Labels resolve the same in vs and in the assembly's offsets, so every
   operand evaluates the same both ways. *)
Theorem eval_operand_frame_view:
  !fn ra vs lo op.
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) ==>
    eval_operand op (frame_view fn ra vs) =
    operand_val (frame_view fn ra vs) lo op
Proof
  rpt strip_tac >> Cases_on `op` >>
  simp[eval_operand_def, operand_val_def, lookup_var_def] >>
  simp[frame_view_def]
QED

(* Owned operands are equal to their ASSIGN-chain roots, so equivalent
   operands agree. *)
Theorem owned_operand_equiv:
  !ops ps fn ra vs lo dfg.
    (!op. MEM op ops /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) ==>
    !op at. MEM op ops /\
            (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at ops) /\
            operand_equiv dfg op at ==>
            operand_val (frame_view fn ra vs) lo op =
            operand_val (frame_view fn ra vs) lo at
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op ops ==>
     operand_val (frame_view fn ra vs) lo op =
     operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] op)` by
    (rpt strip_tac >> Cases_on `is_var_operand op`
     >- (first_x_assum irule >>
         first_x_assum (qspec_then `op` mp_tac) >>
         simp[IS_SOME_EXISTS] >> strip_tac >>
         imp_res_tac stack_get_depth_MEM >> gvs[FLOOKUP_DEF]) >>
     Cases_on `op` >> gvs[is_var_operand_def, normalize_operand_def]) >>
  rpt strip_tac >> gvs[operand_equiv_def] >> metis_tac[]
QED

Theorem compute_operands_labels:
  !inst l.
    MEM (Label l) (compute_operands inst) ==>
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\ inst.inst_opcode <> INVOKE /\
    MEM (Label l) inst.inst_operands
Proof
  rpt gen_tac >> simp[compute_operands_def, LET_THM] >>
  Cases_on `MEM inst.inst_opcode [JMP; DJMP; JNZ; INVOKE]`
  >- fs[get_non_label_operands_def, MEM_FILTER] >>
  fs[] >> IF_CASES_TAC >> simp[] >>
  Cases_on `inst.inst_operands` >> simp[]
QED

Theorem label_positions_ok_other:
  !inst.
    label_positions_ok inst /\
    ~MEM inst.inst_opcode [JMP; JNZ; PHI; INVOKE; ADD; CODECOPY] ==>
    EVERY (\op. ~is_label_operand op) inst.inst_operands
Proof
  gen_tac >> simp[label_positions_ok_def] >>
  Cases_on `inst.inst_opcode` >> simp[]
QED

Theorem label_eval_error:
  !inst s op.
    (inst.inst_opcode = ADD \/ inst.inst_opcode = CODECOPY) /\
    MEM op inst.inst_operands /\ eval_operand op s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >> gvs[step_inst_base_opcode_eqs, exec_pure2_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* label_positions_ok leaves label operands to ADD and CODECOPY outside
   jumps, calls and PHIs, and both evaluate every operand. *)
Theorem step_label_operands_resolve:
  !inst s l.
    label_positions_ok inst /\ inst.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands inst) /\
    (!e. step_inst_base inst s <> Error e) ==>
    IS_SOME (FLOOKUP s.vs_labels l)
Proof
  rpt gen_tac >> strip_tac >>
  drule compute_operands_labels >> strip_tac >>
  Cases_on `inst.inst_opcode = ADD \/ inst.inst_opcode = CODECOPY`
  >- (CCONTR_TAC >>
      `eval_operand (Label l) s = NONE` by
        (Cases_on `FLOOKUP s.vs_labels l` >> fs[eval_operand_def]) >>
      drule_all label_eval_error >> metis_tac[]) >>
  `EVERY (\op. ~is_label_operand op) inst.inst_operands` by
    (irule label_positions_ok_other >> fs[]) >>
  fs[EVERY_MEM] >> res_tac >> fs[is_label_operand_def]
QED

(* ===== The block's code ===== *)

Theorem block_ops_at:
  !prog pc0 fmp lbl prefix_ops ops rest'.
    asm_block_at prog pc0
      (execute_plan fmp (SOLabel lbl :: prefix_ops ++ ops ++ rest')) ==>
    asm_block_at prog
      (pc0 + LENGTH (execute_plan fmp (SOLabel lbl :: prefix_ops)))
      (execute_plan fmp ops)
Proof
  rpt gen_tac >>
  REWRITE_TAC [GSYM APPEND_ASSOC, GSYM (cj 2 APPEND)] >>
  simp[execute_plan_append, asm_block_at_append]
QED

Theorem asm_block_labels:
  !prog lo o2pc pc ops.
    asm_symbols_ok prog /\ asm_block_at prog pc ops /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog ==>
    !lbl i. i < LENGTH ops /\ EL i ops = AsmLabel lbl ==>
      ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
            FLOOKUP o2pc off = SOME (pc + i)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[asm_block_at_def] >>
  irule asm_symbols_ok_label_index >> simp[]
QED

Theorem reachable_fn_mem_inst:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    MEM inst bb.bb_instructions /\ inst.inst_opcode <> PHI ==>
    MEM inst (fn_insts (reachable_fn fn))
Proof
  rpt strip_tac >>
  simp[reachable_fn_def, fn_insts_def, MEM_fn_insts_blocks_iff, MEM_MAP,
       MEM_FILTER, PULL_EXISTS] >>
  qexists_tac `bb` >> simp[] >>
  qexists_tac `inst` >> simp[reachable_inst_fields]
QED

(* ===== How exec_block unfolds at an instruction ===== *)

Theorem exec_block_step:
  !fuel ctx bb vs inst.
    get_instruction bb vs.vs_inst_idx = SOME inst ==>
    exec_block fuel ctx bb vs =
      case step_inst fuel ctx inst vs of
        OK s' =>
          if is_terminator inst.inst_opcode then
            if s'.vs_halted then Halt s' else OK s'
          else exec_block fuel ctx bb
                 (s' with vs_inst_idx := SUC vs.vs_inst_idx)
      | IntRet vals s' => IntRet vals s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | Error e => Error e
Proof
  rpt strip_tac >> simp[Once exec_block_def]
QED

Theorem exec_block_out_of_range:
  !fuel ctx bb vs.
    LENGTH bb.bb_instructions <= vs.vs_inst_idx ==>
    ?e. exec_block fuel ctx bb vs = Error e
Proof
  rpt strip_tac >> simp[Once exec_block_def, get_instruction_def]
QED

(* A revert forwarding's run ends in Abort or Error. *)
Theorem step_revert_no_halt:
  inst.inst_opcode = REVERT ==>
  step_inst fuel ctx inst s <> Halt t /\ step_inst fuel ctx inst s <> OK t
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()]
QED

Theorem assign_suffix_no_halt:
  !n s j bb fuel ctx t.
    j = s.vs_inst_idx + n /\
    (?inst. get_instruction bb j = SOME inst /\
            inst.inst_opcode = REVERT) /\
    (!k inst. s.vs_inst_idx <= k /\ k < j /\
              get_instruction bb k = SOME inst ==>
              inst.inst_opcode = ASSIGN) ==>
    exec_block fuel ctx bb s <> Halt t
Proof
  Induct_on `n`
  >- (rpt strip_tac >> gvs[] >>
      gvs[Once exec_block_def] >>
      drule step_revert_no_halt >> strip_tac >>
      Cases_on `step_inst fuel ctx inst s` >> gvs[AllCaseEqs()] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[Once exec_block_def] >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME cur` >>
  `cur.inst_opcode = ASSIGN` by
    (first_x_assum irule >> qexists_tac `s.vs_inst_idx` >> simp[]) >>
  drule step_assign_cases >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] strip_assume_tac) >>
  once_rewrite_tac [exec_block_def] >> simp[is_terminator_def] >>
  first_x_assum irule >> qexists_tac `j` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  qexists_tac `k` >> simp[]
QED

Theorem revert_forward_pair_no_halt:
  revert_forward_pair bb s.vs_inst_idx j ==>
  exec_block fuel ctx bb s <> Halt t
Proof
  simp[revert_forward_pair_def] >> strip_tac >>
  drule_all step_forward_copy_cases >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] strip_assume_tac) >>
  once_rewrite_tac [exec_block_def] >> simp[is_terminator_def] >>
  irule assign_suffix_no_halt >>
  qexistsl_tac [`j`, `j - SUC s.vs_inst_idx`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> qexists_tac `k` >> simp[]
QED

(* ===== Opcode classes ===== *)

Theorem step_ok_terminator_jump:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_terminator inst.inst_opcode ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[])
QED
