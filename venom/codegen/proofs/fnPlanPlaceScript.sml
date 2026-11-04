(*
 * Placement of planned code in the assembled program, for the block
 * induction behind venomToAsmProps$gen_fn_frame_simulation.
 *
 * codegen_assembly lays out the context plan as the regions' plans in
 * order, then the revert postamble, then the data segment.  A block's
 * code starts with AsmLabel of its label, so with symbols unique in prog
 * the label's offset in compute_label_offsets is that AsmLabel's, and
 * build_offset_to_pc maps the offset back to its index.
 *
 * Symbol uniqueness and the program size come from codegen_assembly's
 * asm_symbols_ok check: every AsmLabel/AsmDataHeader name is distinct, as
 * Python's assembler requires, and the program fits 2-byte label pushes.
 *
 * TOP-LEVEL:
 *   dfs_block_code_placed   — a planned block's code sits at its label
 *   fn_region_placed        — a function's whole plan sits at its entry label
 *   revert_postamble_placed — the shared revert postamble sits at "revert"
 *)

Theory fnPlanPlace
Ancestors
  fnPlanLineage codegen asmSem symbolResolve planExec stackPlanGen
  stackPlanTypes fnPlanPlaceRevertPostamble fnPlanPlaceFnRegion
  fnPlanPlaceDfsBlock

(* Used at each jump of the block induction: the successor's code
   (planned from its DFS state, fnPlanCover) is at the PC its label
   resolves to, which gives gen_fn_frame_simulation's asm_block_at premise
   at the successor and gen_jmp_frame_sim's / gen_jnz_frame_sim's
   FLOOKUP lo / FLOOKUP o2pc premises.  The last conjunct is
   gen_inst_frame_sim's premise that labels defined in an instruction's
   own code (INVOKE return labels, ASSERT_UNREACHABLE's) resolve to their
   own positions; an instruction's code is a slice of its block's.

   Why it should hold: region i's plan is r.sr_plan (the premise fixes it
   whatever lbl_ctr is), and a DFS state's block plan is a slice of it, so
   execute_plan_append places block_ops at the sum of the earlier regions'
   and blocks' asm lengths.  The first asm instruction is AsmLabel lbl;
   with every AsmLabel/AsmDataHeader name distinct (asm_symbols_ok) it is
   the only binding
   of lbl in compute_label_offsets.  AsmLabel has size 1, so no later
   instruction shares its offset and build_offset_to_pc maps it to its
   index.  off < 65536 < dimword (:256) from asm_symbols_ok's size bound. *)
Theorem dfs_block_code_placed:
  !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth lbl_ctr
   ps_end lbl bb ps_dfs block_ops ps_dfs_after.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      r.sr_spill_base lbl_ctr = SOME (r.sr_plan, ps_end) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth r.sr_spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after)
    ==>
    ?off pc.
      FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc (execute_plan cp.cp_initial_fmp block_ops) /\
      (!l j. j < LENGTH (execute_plan cp.cp_initial_fmp block_ops) /\
             EL j (execute_plan cp.cp_initial_fmp block_ops) = AsmLabel l ==>
             ?off'. FLOOKUP lo l = SOME off' /\ off' < dimword (:256) /\
                    FLOOKUP o2pc off' = SOME (pc + j))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ctx = _` SUBST_ALL_TAC >>
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  qpat_x_assum `o2pc = _` SUBST_ALL_TAC >>
  rename1 `generate_context_plan _ = SOME plan` >>
  drule generate_context_plan_regions_length >> strip_tac >>
  `MEM r plan.cp_regions` by metis_tac[listTheory.MEM_EL] >>
  drule_all dfs_block_plan_contained >> strip_tac >>
  drule_all codegen_region_subplan_contained >> strip_tac >>
  drule_all lookup_block_plan_leading_label >> strip_tac >>
  drule codegen_assembly_symbols_ok >> strip_tac >>
  qpat_x_assum `block_ops = _` SUBST_ALL_TAC >>
  fs[execute_plan_def, exec_stack_op_def] >>
  qabbrev_tac `asm_tail = FLAT (MAP (exec_stack_op plan.cp_initial_fmp) tail)` >>
  `prog = pre' ++ (AsmLabel lbl :: asm_tail) ++ post'` by simp[] >>
  drule_all labelled_asm_slice_placed >> strip_tac >>
  drule asm_slice_internal_labels >>
  disch_then (qspecl_then [`pre'`, `AsmLabel lbl :: asm_tail`, `post'`] mp_tac) >>
  strip_tac >>
  qpat_x_assum `prog = pre' ++ [AsmLabel lbl] ++ asm_tail ++ post'`
    (fn th => rewrite_tac[GSYM th]) >>
  qexistsl_tac [`off`, `LENGTH pre'`] >> simp[arithmeticTheory.ADD_COMM] >>
  metis_tac[listTheory.LENGTH, arithmeticTheory.ADD_COMM]
QED

(* Used for INVOKE (gen_invoke_frame_sim's callee-placement premise: the
   call jumps to the callee's entry label, where gen_fn_simulation wants
   the callee's whole plan) and for gen_fn_simulation's own asm_block_at
   premise.

   Why it should hold: generate_context_plan = SOME makes every function's
   plan SOME, so canonical_param_prefix holds and fn has blocks; the DFS
   starts at the entry block, so r.sr_plan begins with
   SOLabel (HD fn.fn_blocks).bb_label; the rest is dfs_block_code_placed's
   argument for the region's start. *)
Theorem fn_region_placed:
  !rpolicy unit cp prog ctx lo o2pc i fn r.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r
    ==>
    ?off pc.
      FLOOKUP lo (HD fn.fn_blocks).bb_label = SOME off /\
      off < dimword (:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc (execute_plan cp.cp_initial_fmp r.sr_plan)
Proof
  rpt strip_tac >>
  drule_all context_region_leading_label >> strip_tac >>
  gvs[] >>
  drule codegen_region_slice >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  gvs[execute_plan_def, exec_stack_op_def] >>
  drule (SRULE [] labelled_asm_slice_placed) >> strip_tac >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  metis_tac[]
QED

(* Used by the ASSERT case of the abort step (gen_inst_abort_frame_sim's
   premise, as genBlockSim$gen_inst_abort_sim's) and by gen_inst_frame_sim's
   IS_SOME (FLOOKUP lo "revert") premise.

   Why it should hold: context_plan_ops ends with revert_postamble, which
   starts with SOLabel "revert", the only "revert" symbol by
   asm_symbols_ok. *)
Theorem revert_postamble_placed:
  !rpolicy unit cp prog ctx lo o2pc.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog
    ==>
    ?off pc.
      FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME pc /\
      asm_block_at prog pc (execute_plan cp.cp_initial_fmp revert_postamble)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_all codegen_revert_slice >> strip_tac >>
  drule_all labelled_asm_slice_placed >> strip_tac >>
  metis_tac[]
QED
