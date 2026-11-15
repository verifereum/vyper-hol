(* Finite source-prefix composition of height-only instruction traces. *)
Theory staticAbortPrefix
Ancestors
  staticAbortInst fnBlockBodyHelpers fnPlanPrefix stackPlanGen list arithmetic rich_list
  staticAbortDefs staticAbortTrace planExec stackOpSim venomState unitShapeDefs
  fnBlockPlanStatic livenessDefs venomInst asmSem

Theorem static_abort_prefix_head:
  !lv dfg cfg fn bb i n ps ops qs.
  i < LENGTH bb.bb_instructions /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (i - LENGTH (get_params bb.bb_instructions)) (SUC n)
    (DROP i bb.bb_instructions) ps = SOME (ops,qs) ==>
  ?a mid b.
    generate_inst_plan lv dfg cfg fn (EL i bb.bb_instructions)
      (live_vars_at lv bb.bb_label (i+1)) (bb_is_halting bb)
      (i+1 < LENGTH bb.bb_instructions /\
       is_terminator (EL (i+1) bb.bb_instructions).inst_opcode)
      bb.bb_label ps = SOME (a,mid) /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (SUC i - LENGTH (get_params bb.bb_instructions)) n
      (DROP (SUC i) bb.bb_instructions) mid = SOME (b,qs) /\
    ops = a ++ b
Proof
  rpt gen_tac >> strip_tac >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (SUC i) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL] >>
  `i - LENGTH (get_params bb.bb_instructions) + LENGTH (get_params bb.bb_instructions) = i /\
   SUC i - LENGTH (get_params bb.bb_instructions) =
     i - LENGTH (get_params bb.bb_instructions) + 1` by decide_tac >>
  gvs[Once generate_block_insts_prefix_def, AllCaseEqs()] >>
  Cases_on `DROP (SUC i) bb.bb_instructions`
  >- (gvs[DROP_EQ_NIL] >>
      `LENGTH bb.bb_instructions = i+1` by decide_tac >> gvs[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `i+1 < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP (SUC i) _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  `EL (i+1) bb.bb_instructions = h` by
    (qpat_x_assum `DROP (SUC i) _ = _` (mp_tac o AP_TERM ``HD : instruction list -> instruction``) >> simp[HD_DROP, ADD1]) >>
  gvs[] >> goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem static_abort_block_prefix:
  !n i j unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end
   lbl bb ps_l ps_dfs ps_dfs_after height promised block_ops ps_after
   ps ops qs s top rest.
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
  static_abort_pair bb i j /\ n = SUC j - i /\
  generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (i - LENGTH (get_params bb.bb_instructions)) n
    (DROP i bb.bb_instructions) ps = SOME (ops,qs) /\
  (!k inst l. i <= k /\ k <= j /\ get_instruction bb k = SOME inst /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  s.as_call_ctx.cc_static /\ s.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
  asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q s t
Proof
  Induct_on `n` >- (rpt gen_tac >> strip_tac >> fs[static_abort_pair_def]) >>
  rpt gen_tac >> strip_tac >>
  `i <= j /\ j < LENGTH bb.bb_instructions /\ i < LENGTH bb.bb_instructions` by
    gvs[static_abort_pair_def] >>
  `EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks` by
    metis_tac[codegen_ready_fn_no_marker] >>
  `inst_shape_ok (EL i bb.bb_instructions) /\
   codegen_ready_inst (EL i bb.bb_instructions)` by
    metis_tac[EVERY_EL] >>
  `get_instruction bb i = SOME (EL i bb.bb_instructions)` by
    simp[get_instruction_def] >>
  qpat_x_assum `bb.bb_label = lbl` (SUBST_ALL_TAC o SYM) >>
  drule_all static_abort_prefix_head >> strip_tac >>
  `asm_block_at prog s.as_pc (execute_plan cplan.cp_initial_fmp a) /\
   asm_block_at prog (s.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp a))
     (execute_plan cplan.cp_initial_fmp b)` by
    gvs[execute_plan_append, asm_block_at_append] >>
  `!l. MEM (Label l) (compute_operands (EL i bb.bb_instructions)) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl [`EL i bb.bb_instructions`, `i`] >> simp[]) >>
  Cases_on `i = j`
  >- (`MEM (EL i bb.bb_instructions).inst_opcode [SSTORE;TSTORE;LOG]` by
        metis_tac[static_abort_pair_def] >>
      `?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp a)+4 /\
        static_abort_exception (SND (compute_label_offsets prog))
          (build_offset_to_pc prog) prog q s t` by
        (irule static_abort_inst_terminal >>
         first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
         rpt (first_assum (irule_at Any)) >> simp[]) >>
      qexistsl [`q`, `t`] >> gvs[execute_plan_append] >> decide_tac) >>
  `~is_terminator (EL i bb.bb_instructions).inst_opcode /\
   ~MEM (EL i bb.bb_instructions).inst_opcode
     [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;SSTORE;TSTORE;LOG]` by
    (fs[static_abort_pair_def] >> first_x_assum irule >>
     qexists `i` >> simp[]) >>
  `(?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp a) /\
     static_abort_normal (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
       prog q s t /\
     t.as_pc = s.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp a) /\
     LENGTH t.as_stack = LENGTH mid.ps_stack + LENGTH rest /\
     t.as_call_ctx = s.as_call_ctx) \/
   (?q t. q <= LENGTH (execute_plan cplan.cp_initial_fmp a)+4 /\
     static_abort_exception (SND (compute_label_offsets prog))
       (build_offset_to_pc prog) prog q s t)` by
    (irule static_abort_inst_progress >>
     first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  all_tac >- (
  `block_plan_state lv dfg cfg fn bb
     (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>)
     (SUC i) mid` by metis_tac[block_plan_state_step] >>
  `SUC i <= j /\ n = SUC j - SUC i /\
   phi_prefix_length bb.bb_instructions <= SUC i /\
   LENGTH (get_params bb.bb_instructions) <= SUC i` by decide_tac >>
  `static_abort_pair bb (SUC i) j` by
    (qpat_assum `static_abort_pair _ _ _` mp_tac >>
     pure_rewrite_tac[static_abort_pair_def] >>
     metis_tac[LESS_EQ_TRANS, LESS_EQ_SUC_REFL]) >>
  `t.as_stack = TAKE (LENGTH mid.ps_stack) t.as_stack ++
                  DROP (LENGTH mid.ps_stack) t.as_stack /\
   LENGTH (TAKE (LENGTH mid.ps_stack) t.as_stack) = LENGTH mid.ps_stack` by simp[] >>
  `?q' out. q' <= LENGTH (execute_plan cplan.cp_initial_fmp b)+4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog q' t out` by
    (first_x_assum irule >>
     first_assum (irule_at (Pat `block_plan_state _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
     rpt (first_assum (irule_at Any)) >> simp[] >>
     conj_tac >- metis_tac[ADD_COMM] >>
     rpt strip_tac >>
     qpat_x_assum `!k inst l. _` irule >>
     qexistsl [`inst`, `k`] >> simp[] >> decide_tac) >>
  qexistsl [`q+q'`, `out`] >> conj_tac
  >- (simp[execute_plan_append] >> decide_tac) >>
  irule static_abort_exception_append >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl [`q`, `t`] >> gvs[execute_plan_append] >> decide_tac
QED
