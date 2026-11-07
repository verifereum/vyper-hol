(*
 * Helpers for fnBlockStep$fn_block_frame_step: the static facts the block
 * step needs about a non-entry block, its region and its DFS code, and
 * the assembly of the block's prefix step (label, cleanup, PHIs) in front
 * of fnBlockBody$block_body_frame_sim.
 *
 * TOP-LEVEL:
 *   block_step_prefix - from the block-boundary premises of
 *                       gen_fn_frame_sim_at and the block's PHI result,
 *                       the premises block_body_frame_sim takes over with
 *)

Theory fnBlockStepHelpers
Ancestors
  fnBlockBody fnBlockPlanStatic fnFrameSinglePred fnFrameSteps fnLineageStatic fnPlanPrefix
  fnPlanLineage fnPlanPlaceDfsBlock fnPlanPlaceFnRegion allocMono
  planSpillBounds contextPlanLayoutProps unitShapeDefs contextCodegenRel
  codegenRel frameRel fnSimSpec venomExecProofs venomExecProps stackOpSim
  blockSimHelpers genBlockSim callLayoutDefs stackPlanGen stackPlanTypes
  planExec asmSem venomExecSemantics venomState venomInst
  list rich_list arithmetic

(* ===== Fields the relations do not read ===== *)

Theorem fn_frame_inv_cleanup_fields:
  !ctx cp lo fn ra rest mem0 ps h promised vs as.
    fn_frame_inv ctx cp lo fn ra rest mem0
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      vs as <=>
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def]
QED

Theorem fn_frame_inv_pc:
  !ctx cp lo fn ra rest mem0 ps vs as pc.
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs (as with as_pc := pc) <=>
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def]
QED

Theorem operand_val_frame_view_inst_idx:
  !fn ra s k lo at.
    operand_val (frame_view fn ra (s with vs_inst_idx := k)) lo at =
    operand_val (frame_view fn ra s) lo at
Proof
  rpt gen_tac >> Cases_on `at` >> simp[operand_val_def, frame_view_def]
QED

(* ===== The function's region ===== *)

Theorem generate_context_regions_fn_name:
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

Theorem context_region_fn_name:
  !ctx cp i.
    generate_context_plan ctx = SOME cp /\ i < LENGTH ctx.ctx_functions ==>
    MEM (EL i cp.cp_regions) cp.cp_regions /\
    (EL i cp.cp_regions).sr_fn_name = (EL i ctx.ctx_functions).fn_name
Proof
  rpt gen_tac >> strip_tac >>
  drule generate_context_plan_regions_length >> strip_tac >>
  conj_tac >- (irule EL_MEM >> simp[]) >>
  qpat_x_assum `generate_context_plan _ = _` mp_tac >>
  simp[generate_context_plan_def, generate_context_plan_with_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[finish_context_plan_def] >>
  drule generate_context_regions_fn_name >> simp[]
QED

(* Every spill or restore offset of a region's code is a word. *)
Theorem region_subplan_spill_offsets:
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

(* ===== The DFS planner's allocator ===== *)

(* Every call the DFS planner makes ends with the spill base it started
   from and a high-water mark no higher than the whole function's. *)
Theorem dfs_calls_alloc_bounded:
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

Resume dfs_calls_alloc_bounded[visited]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def]
QED

Resume dfs_calls_alloc_bounded[missing]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def]
QED

Resume dfs_calls_alloc_bounded[succs]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_alloc_mono) >> gvs[]
QED

Resume dfs_calls_alloc_bounded[rest]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_::_) visited _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Resume dfs_calls_alloc_bounded[branch]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 2 fn_plan_aux_alloc_mono) >> gvs[]
QED

Resume dfs_calls_alloc_bounded[sibling]:
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `generate_succs_plan _ _ _ _ _ _ (_::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[]
QED

Finalise dfs_calls_alloc_bounded

(* The state after a block's DFS code has the function's spill base and
   a high-water mark no higher than the function plan's final one. *)
Theorem dfs_block_alloc_bounded:
  !lv dfg cfg ch growth fn base ctr fn_ops ps_end lbl ps bb block_ops
   ps_after.
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
      SOME (fn_ops, ps_end) /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth base ctr) lbl ps /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb ps = SOME (block_ops, ps_after) ==>
    ps_after.ps_alloc.sa_spill_base = base /\
    ps_after.ps_alloc.sa_next_offset <= ps_end.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >>
  gvs[dfs_block_state_def] >>
  drule (cj 1 dfs_calls_entry_exists) >> strip_tac >>
  qpat_x_assum `generate_fn_plan_with_cleanup_analyzed _ _ _ _ _ _ _ _ = _`
    mp_tac >>
  simp[generate_fn_plan_with_cleanup_analyzed_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule (cj 1 dfs_calls_alloc_bounded) >> disch_then drule_all >>
  strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ (lbl::_) _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_alloc_mono) >>
  imp_res_tac (cj 2 fn_plan_aux_alloc_mono) >>
  gvs[init_cleanup_plan_state_def, init_plan_state_def, init_spill_alloc_def]
QED

(* ===== The function's static shape ===== *)

Theorem step_fn_shape:
  !ctx unit Inv cp i fn.
    ctx = unit.cu_context /\ unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    i < LENGTH ctx.ctx_functions /\ EL i ctx.ctx_functions = fn ==>
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn
Proof
  simp[unit_shape_ok_def, codegen_context_obligations_def, codegen_ready_def,
       EVERY_EL, fn_shape_ok_def] >>
  metis_tac[]
QED


(* ===== The block's code ===== *)

Theorem generate_block_plan_nonentry:
  !liveness dfg cfg fn bb ps ops ps'.
    bb <> HD fn.fn_blocks /\
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
    ?clean_ops ps2 inst_ops.
      (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
       then clean_stack_plan liveness cfg fn bb ps
       else ([], ps)) = (clean_ops, ps2) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 =
        SOME (inst_ops, ps') /\
      ops = SOLabel bb.bb_label :: clean_ops ++ inst_ops
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem label_block_steps:
  !lo o2pc prog as fmp lbl ops.
    asm_block_at prog as.as_pc (execute_plan fmp (SOLabel lbl :: ops)) ==>
    asm_steps lo o2pc prog 1 as = AsmOK (as with as_pc := as.as_pc + 1) /\
    asm_block_at prog (as.as_pc + 1) (execute_plan fmp ops)
Proof
  rpt gen_tac >>
  simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons] >>
  strip_tac >>
  qspecl_then [`lo`, `o2pc`, `prog`, `as`, `lbl`] mp_tac label_op_asm_steps >>
  simp[asm_block_at_cons, asm_block_at_def]
QED

Theorem execute_plan_label_length:
  !fmp lbl ops.
    LENGTH (execute_plan fmp (SOLabel lbl :: ops)) =
    LENGTH (execute_plan fmp ops) + 1
Proof
  simp[execute_plan_def, exec_stack_op_def]
QED

(* ===== Composing assembly runs ===== *)

(* The function-frame conclusions survive running n assembly steps in
   front. *)
Theorem frame_conclusions_prefix:
  !lo o2pc prog n as as1 res pc_ret rets cp ctx fn mem0.
    asm_steps lo o2pc prog n as = AsmOK as1 /\
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as1 = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as1 = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as1 = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. res = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as1 = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rets /\
               context_memory_rel cp vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cp b /\
                    ~closure_spill_byte ctx cp fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
    ==>
    (!vs'. res = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. res = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as') /\
    (!ret vs'. res = IntRet ret vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
               as'.as_pc = pc_ret /\
               as'.as_stack = REVERSE ret.iret_values ++ rets /\
               context_memory_rel cp vs'.vs_memory as'.as_memory /\
               (!b. context_spill_byte cp b /\
                    ~closure_spill_byte ctx cp fn.fn_name b ==>
                    read_byte b as'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  rename1 `asm_steps lo o2pc prog m as1` >>
  qexistsl_tac [`n + m`, `as'`] >>
  qpat_x_assum `asm_steps _ _ _ n as = _`
    (fn th => REWRITE_TAC [MATCH_MP asm_steps_add_ok th]) >>
  simp[]
QED

(* ===== The block's prefix: cleanup and PHIs ===== *)

Theorem take_drop_phi_prefix[local]:
  !bb. non_param_insts bb = bb.bb_instructions ==>
    LENGTH (TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)) =
      phi_prefix_length bb.bb_instructions
Proof
  rw[LENGTH_TAKE_EQ, phi_prefix_length_le]
QED

(* Both prefix lemmas (one predecessor: cleanup then PHIs; otherwise PHIs
   only), with the lineage state's cleanup fields set as
   lineage_state_block_plan chose them. *)
Theorem block_prefix_step:
  !ctx cpl lo o2pc prog liveness dfg cfg ch growth spill_base lbl_ctr fn bb
   pred ps_l h promised vs as s_phi clean_ops ps2 ops ps3 r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    vs.vs_prev_bb = SOME pred /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps_l /\
    generated_plan_state_wf_marked spill_base ps_l /\
    (!op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
       ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                       (collect_phis bb.bb_instructions))) /\
       (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
       ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 ==>
     !op v. (MEM op ps_l.ps_stack \/ op IN FDOM ps_l.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM r cpl.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps3.ps_alloc.sa_spill_base /\
    ps3.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) (clean_ops ++ ops) \/
           MEM (SORestore off) (clean_ops ++ ops) ==>
           off < dimword (:256)) /\
    (!at. MEM at ps_l.ps_stack \/ at IN FDOM ps_l.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps_l vs as /\
    eval_phis vs bb.bb_instructions = OK s_phi /\
    non_param_insts bb = bb.bb_instructions /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan liveness cfg fn bb
            (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
     else ([], ps_l with <| ps_cleanup_height := h;
                            ps_cleanup_promised := promised |>)) =
      (clean_ops, ps2) /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 = SOME (ops, ps3) /\
    asm_block_at prog as.as_pc
      (execute_plan cpl.cp_initial_fmp (clean_ops ++ ops))
    ==>
    ?phi_ops ps1 body_ops n as'.
      ops = phi_ops ++ body_ops /\
      generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (phi_prefix_length bb.bb_instructions)
        (non_param_insts bb) ps2 = SOME (phi_ops, ps1) /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) (phi_prefix_length bb.bb_instructions)
        (DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb))
        ps1 = SOME (body_ops, ps3) /\
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cpl.cp_initial_fmp (clean_ops ++ phi_ops)) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as' /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra s_phi) lo at =
         operand_val (frame_view fn ra s_phi) lo (normalize_operand dfg [] at))
Proof
  rpt gen_tac >> strip_tac >>
  drule take_drop_phi_prefix >> strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1`
  >- suspend "single"
  >> suspend "join"
QED

Resume block_prefix_step[single]:
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  pop_assum (fn th => REWRITE_TAC [th] >> assume_tac th) >> strip_tac >>
  qpat_x_assum `LENGTH _ <= 1 ==> _` mp_tac >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`,
     `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`, `fn`, `bb`, `pred`,
     `ps_l`, `h`, `promised`,
     `ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`,
     `spill_base`, `vs`, `as`, `s_phi`, `clean_ops`, `ps2`,
     `TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `ops`, `ps3`, `r`, `ra`, `rest`, `mem0`] single_pred_prefix_frame_sim |>
   REWRITE_RULE [plan_state_accfupds, combinTheory.K_THM,
                 wf_marked_cleanup_fields, fn_frame_inv_cleanup_fields,
                 TAKE_DROP]) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >> qexistsl_tac [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]
QED

Resume block_prefix_step[join]:
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  pop_assum (fn th => REWRITE_TAC [th, pairTheory.PAIR_EQ] >> assume_tac th) >>
  strip_tac >>
  qpat_x_assum `[] = clean_ops` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = ps2` (SUBST_ALL_TAC o SYM) >>
  mp_tac (Q.SPECL [`ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`,
     `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`, `fn`, `bb`, `pred`,
     `ps_l`, `h`, `promised`,
     `ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`,
     `spill_base`, `vs`, `as`, `s_phi`,
     `TAKE (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `DROP (phi_prefix_length bb.bb_instructions) (non_param_insts bb)`,
     `ops`, `ps3`, `r`, `ra`, `rest`, `mem0`] phi_prefix_frame_sim |>
   REWRITE_RULE [plan_state_accfupds, combinTheory.K_THM,
                 wf_marked_cleanup_fields, fn_frame_inv_cleanup_fields,
                 TAKE_DROP]) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]) >>
  strip_tac >> qexistsl_tac [`phi_ops`, `ps1`, `body_ops`, `n`, `as'`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[]
QED

Finalise block_prefix_step

(* ===== From the block boundary to the block body ===== *)

(* At the start of a non-entry block whose PHIs evaluate to s_phi: the
   label's JUMPDEST and the block's prefix run, reaching the premises of
   fnBlockBody$block_body_frame_sim at k = phi_prefix_length (the block
   has no parameters), with the cleanup fields lineage_state_block_plan
   picks. *)
Theorem block_step_prefix:
  !unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch growth spill_base
   lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after vs as Inv
   ra rest mem0 s_phi.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    codegen_context_obligations Inv ctx cpl /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    bb <> HD fn.fn_blocks /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      pred bb.bb_label ps /\
    vs.vs_prev_bb = SOME pred /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      vs.vs_current_bb ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    asm_block_at prog as.as_pc (execute_plan cpl.cp_initial_fmp block_ops) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs as /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    eval_phis vs bb.bb_instructions = OK s_phi
    ==>
    ?h promised ps_after prefix_ops rest_ops ps1 n as1.
      generate_block_plan liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
      block_plan_state liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
        (phi_prefix_length bb.bb_instructions) ps1 /\
      generate_block_insts_plan liveness dfg cfg fn bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions)
        (phi_prefix_length bb.bb_instructions -
         LENGTH (get_params bb.bb_instructions))
        (DROP (phi_prefix_length bb.bb_instructions -
               LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
        ps1 = SOME (rest_ops, ps_after) /\
      block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
      asm_steps lo o2pc prog n as = AsmOK as1 /\
      as1.as_pc = as.as_pc + LENGTH (execute_plan cpl.cp_initial_fmp
                                       (SOLabel bb.bb_label :: prefix_ops)) /\
      fn_frame_inv ctx cpl lo fn ra rest mem0 ps1
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) as1 /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)) lo at =
         operand_val (frame_view fn ra
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)) lo
           (normalize_operand dfg [] at))
Proof
  rpt gen_tac >> strip_tac >>
  drule venomExecPropsTheory.lookup_block_label >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
   dfs_block_state liveness dfg cfg fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr)
     bb.bb_label ps_dfs` by
    (qpat_x_assum `bb.bb_label = _` (fn th => REWRITE_TAC [th]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all step_fn_shape >> strip_tac >>
  `canonical_param_prefix fn` by fs[codegen_ready_fn_def] >>
  drule_all nonentry_block_no_params >> strip_tac >>
  drule codegen_ready_fn_no_marker >> strip_tac >>
  drule lineage_entry_lineage_state >> strip_tac >>
  mp_tac (Q.SPECL [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
    `lbl_ctr`, `fn`, `fn_ops`, `ps_end`, `bb.bb_label`, `bb`, `ps`, `ps_dfs`,
    `block_ops`, `ps_dfs_after`] lineage_state_block_plan) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `spill_base`,
    `lbl_ctr`, `fn`, `fn_ops`, `ps_end`, `bb.bb_label`, `bb`, `ps`]
    lineage_state_static) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`liveness`, `dfg`, `cfg`, `fn`, `bb`,
    `ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`,
    `block_ops`, `ps_after`] generate_block_plan_nonentry) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `fn`,
    `spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `bb.bb_label`, `ps_dfs`,
    `bb`, `block_ops`, `ps_dfs_after`] dfs_block_plan_contained) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`liveness`, `dfg`, `cfg`, `ch`, `growth`, `fn`,
    `spill_base`, `lbl_ctr`, `fn_ops`, `ps_end`, `bb.bb_label`, `ps_dfs`,
    `bb`, `block_ops`, `ps_dfs_after`] dfs_block_alloc_bounded) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`ctx`, `cpl`, `i`] context_region_fn_name) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `EL i cpl.cp_regions = r` (fn th => REWRITE_TAC [th] >> assume_tac th) >>
  qpat_x_assum `EL i ctx.ctx_functions = fn` (fn th => REWRITE_TAC [th] >> assume_tac th) >>
  strip_tac >>
  `r.sr_spill_base <= ps_after.ps_alloc.sa_spill_base /\
   ps_after.ps_alloc.sa_next_offset <= r.sr_spill_end` by
    (gvs[] >> decide_tac) >>
  `!off. MEM (SOSpill off) (clean_ops ++ inst_ops) \/
         MEM (SORestore off) (clean_ops ++ inst_ops) ==> off < dimword (:256)` by
    (rpt strip_tac >>
     mp_tac (Q.SPECL [`ctx`, `cpl`, `r`, `pre`, `block_ops`, `post`, `off`]
       region_subplan_spill_offsets) >> gvs[]) >>
  qpat_x_assum `block_ops = _` (fn eq =>
    qpat_assum `asm_block_at _ _ _` (fn th =>
      strip_assume_tac (MATCH_MP (Q.SPECL [`lo`, `o2pc`] label_block_steps)
                          (REWRITE_RULE [eq, APPEND] th))) >> assume_tac eq) >>
  mp_tac (Q.SPECL [`ctx`, `cpl`, `lo`, `o2pc`, `prog`, `liveness`, `dfg`,
    `cfg`, `ch`, `growth`, `spill_base`, `lbl_ctr`, `fn`, `bb`, `pred`, `ps`,
    `h`, `promised`, `vs`, `as with as_pc := as.as_pc + 1`, `s_phi`,
    `clean_ops`, `ps2`, `inst_ops`, `ps_after`, `r`, `ra`, `rest`, `mem0`]
    block_prefix_step) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
               simp[fn_frame_inv_pc]) >>
  strip_tac >>
  `asm_steps lo o2pc prog (1 + n) as = AsmOK as'` by
    (qpat_x_assum `asm_steps _ _ _ 1 as = _`
       (fn th => REWRITE_TAC [MATCH_MP asm_steps_add_ok th]) >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`h`, `promised`, `ps_after`, `clean_ops ++ phi_ops`,
                `body_ops`, `ps1`, `1 + n`, `as'`] >>
  rpt conj_tac >> REWRITE_TAC [operand_val_frame_view_inst_idx] >>
  TRY (first_assum ACCEPT_TAC)
  >- (REWRITE_TAC [block_plan_state_def] >>
      qexistsl_tac [`[]`,
        `ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>`,
        `clean_ops`, `ps2`, `phi_ops`] >>
      gvs[])
  >> gvs[execute_plan_label_length, operand_val_frame_view_inst_idx]
QED

(* A revert forwarding starts at a RETURNDATACOPY, not a PHI, so it lies
   past the block's PHI prefix. *)
Theorem phi_prefix_length_el[local]:
  !l i. i < phi_prefix_length l ==>
        i < LENGTH l /\ (EL i l).inst_opcode = PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rw[] >> Cases_on `i` >> gvs[]
QED

Theorem revert_forward_pair_past_phis:
  !bb i j. revert_forward_pair bb i j ==>
           phi_prefix_length bb.bb_instructions <= i \/
           j < phi_prefix_length bb.bb_instructions
Proof
  rw[revert_forward_pair_def] >> CCONTR_TAC >>
  `i < phi_prefix_length bb.bb_instructions` by decide_tac >>
  drule phi_prefix_length_el >>
  gvs[venomInstTheory.get_instruction_def, AllCaseEqs()]
QED
