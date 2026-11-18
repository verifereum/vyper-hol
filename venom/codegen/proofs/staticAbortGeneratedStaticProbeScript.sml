(* Shared planner witnesses and universal instruction-boundary edges.
   This deliberately does not claim micro-window coverage or control tags. *)
Theory staticAbortGeneratedStaticProbe
Ancestors
  staticAbortPrefix staticAbortInst fnBlockBodyHelpers fnBlockPlanStatic
  staticAbortDefs staticAbortTrace planExec stackOpSim venomState unitShapeDefs
  fnPlanPrefix stackPlanGen list arithmetic rich_list livenessDefs venomInst asmSem

Theorem generated_static_prefix_shared_edge:
  !i j unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end
   lbl bb ps_l ps_dfs ps_dfs_after height promised block_ops ps_after
   ps ops qs pc hrest ctx req.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
    SOME (fn_ops,ps_end) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) =
    SOME (block_ops,ps_after) /\
  block_plan_state lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) i ps /\
  phi_prefix_length bb.bb_instructions <= i /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\ EVERY codegen_ready_inst bb.bb_instructions /\
  static_abort_pair bb i j /\
  generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (i - LENGTH (get_params bb.bb_instructions)) (SUC j - i)
    (DROP i bb.bb_instructions) ps = SOME (ops,qs) /\
  (!k inst l. i <= k /\ k <= j /\ get_instruction bb k = SOME inst /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  asm_block_at prog pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?a mid b.
    generate_inst_plan lv dfg cfg fn (EL i bb.bb_instructions)
      (live_vars_at lv bb.bb_label (i+1)) (bb_is_halting bb)
      (i+1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (i+1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (a,mid) /\
    generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (SUC i - LENGTH (get_params bb.bb_instructions)) (SUC j - SUC i)
      (DROP (SUC i) bb.bb_instructions) mid = SOME (b,qs) /\
    ops = a ++ b /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>)
      (SUC i) mid /\
    asm_block_at prog pc (execute_plan cplan.cp_initial_fmp a) /\
    asm_block_at prog (pc + LENGTH (execute_plan cplan.cp_initial_fmp a))
      (execute_plan cplan.cp_initial_fmp b) /\
    (i < j ==> static_abort_pair bb (SUC i) j /\
                SUC j - SUC i < SUC j - i) /\
    (!t. t.as_pc = pc /\ LENGTH t.as_stack = LENGTH ps.ps_stack + hrest /\
         t.as_call_ctx = ctx /\ t.as_requests = req /\
         (i = j ==> t.as_call_ctx.cc_static) ==>
       ((i < j /\
         ?q u. q <= LENGTH (execute_plan cplan.cp_initial_fmp a) /\
           static_abort_normal (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog q t u /\
           u.as_pc = pc + LENGTH (execute_plan cplan.cp_initial_fmp a) /\
           LENGTH u.as_stack = LENGTH mid.ps_stack + hrest /\
           u.as_call_ctx = ctx /\ u.as_requests = req) \/
        (?q u. q <= LENGTH (execute_plan cplan.cp_initial_fmp a) + 4 /\
           static_abort_exception (SND (compute_label_offsets prog))
             (build_offset_to_pc prog) prog q t u)))
Proof
  rpt gen_tac >> strip_tac >>
  `i <= j /\ j < LENGTH bb.bb_instructions /\ i < LENGTH bb.bb_instructions` by
    gvs[static_abort_pair_def] >>
  `SUC j - i = SUC (SUC j - SUC i)` by decide_tac >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `SUC j - i = _` (fn th =>
    qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o ONCE_REWRITE_RULE [th])) >>
  drule_all static_abort_prefix_head >> strip_tac >>
  qexistsl [`a`, `mid`, `b`] >>
  `block_plan_state lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>)
    (SUC i) mid` by metis_tac[block_plan_state_step] >>
  `asm_block_at prog pc (execute_plan cplan.cp_initial_fmp a) /\
   asm_block_at prog (pc + LENGTH (execute_plan cplan.cp_initial_fmp a))
     (execute_plan cplan.cp_initial_fmp b)` by
    gvs[execute_plan_append, asm_block_at_append] >>
  simp[] >> conj_tac
  >- (strip_tac >> qpat_assum `static_abort_pair _ _ _` mp_tac >>
      pure_rewrite_tac[static_abort_pair_def] >>
      strip_tac >> simp[] >> rpt gen_tac >> strip_tac >>
      `i <= k` by decide_tac >>
      qpat_x_assum `!k inst. _` (qspecl_then [`k`, `inst`] mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks` by
    metis_tac[codegen_ready_fn_no_marker] >>
  `inst_shape_ok (EL i bb.bb_instructions) /\
   codegen_ready_inst (EL i bb.bb_instructions)` by metis_tac[EVERY_EL] >>
  `get_instruction bb i = SOME (EL i bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `!l. MEM (Label l) (compute_operands (EL i bb.bb_instructions)) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl [`EL i bb.bb_instructions`, `i`] >> simp[]) >>
  `t.as_stack = TAKE (LENGTH ps.ps_stack) t.as_stack ++
                DROP (LENGTH ps.ps_stack) t.as_stack /\
   LENGTH (TAKE (LENGTH ps.ps_stack) t.as_stack) = LENGTH ps.ps_stack /\
   LENGTH (DROP (LENGTH ps.ps_stack) t.as_stack) = hrest` by simp[] >>
  Cases_on `i = j`
  >- (disj2_tac >>
      `MEM (EL i bb.bb_instructions).inst_opcode [SSTORE;TSTORE;LOG]` by
        metis_tac[static_abort_pair_def] >>
      irule static_abort_inst_terminal >>
      first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
      rpt (first_assum (irule_at Any)) >> simp[]) >>
  `~is_terminator (EL i bb.bb_instructions).inst_opcode /\
   ~MEM (EL i bb.bb_instructions).inst_opcode
     [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;SSTORE;TSTORE;LOG]` by
    (fs[static_abort_pair_def] >> first_x_assum irule >>
     qexists `i` >> simp[]) >>
  `(?q u. q <= LENGTH (execute_plan cplan.cp_initial_fmp a) /\
     static_abort_normal (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog q t u /\
     u.as_pc = t.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp a) /\
     LENGTH u.as_stack = LENGTH mid.ps_stack +
       LENGTH (DROP (LENGTH ps.ps_stack) t.as_stack) /\
     u.as_call_ctx = t.as_call_ctx) \/
   (?q u. q <= LENGTH (execute_plan cplan.cp_initial_fmp a)+4 /\
     static_abort_exception (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog q t u)` by
    (irule static_abort_inst_progress >>
     first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  gvs[static_abort_normal_def]
  >- (disj1_tac >> qexistsl [`q`, `u`] >> simp[]) >>
  disj2_tac >> qexistsl [`q`, `u`] >> simp[]
QED
