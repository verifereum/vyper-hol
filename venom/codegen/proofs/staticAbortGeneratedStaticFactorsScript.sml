(* Structural factors of the first generated instruction in a static interval. *)
Theory staticAbortGeneratedStaticFactors
Ancestors
  staticAbortGeneratedStaticProbe staticAbortPlanBoundary staticAbortInst
  fnBlockPlanStatic fnBlockBodySteps fnBlockBodyHelpers staticAbortPrefix fnPlanPrefix
  staticAbortDefs stackPlanGen planExec stackOpSim unitShapeDefs venomWf
  list arithmetic rich_list livenessDefs venomInst asmSem

Theorem generated_static_head_factors:
  !i j unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end
   lbl bb ps_l ps_dfs ps_dfs_after height promised block_ops ps_after
   ps ops qs pc.
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
    (let inst = EL i bb.bb_instructions;
         lo = SND (compute_label_offsets prog);
         fmp = cplan.cp_initial_fmp;
         topics = (case inst.inst_opcode of LOG =>
           (case HD inst.inst_operands of Lit v => w2n v | _ => 0) | _ => 0)
     in
       (inst.inst_opcode = NOP /\ a = [] /\ mid = ps) \/
       ?pre emit post ps6 ps7 m h.
         a = pre ++ emit ++ post /\
         prefix_wf lo (LENGTH ps.ps_stack) pre /\
         prefix_end_len lo (LENGTH ps.ps_stack) pre = m /\
         LENGTH (compute_operands inst) <= m /\
         h + LENGTH (compute_operands inst) = m + LENGTH inst.inst_outputs /\
         LENGTH ps6.ps_stack = h /\
         generate_emit_ops inst topics ps6 = (emit,ps7) /\
         LENGTH ps7.ps_stack = h /\
         prefix_wf lo h post /\ prefix_end_len lo h post = LENGTH mid.ps_stack /\
         asm_block_at prog pc (execute_plan fmp pre) /\
         asm_block_at prog (pc + LENGTH (execute_plan fmp pre))
           (execute_plan fmp emit) /\
         asm_block_at prog
           (pc + LENGTH (execute_plan fmp pre) + LENGTH (execute_plan fmp emit))
           (execute_plan fmp post) /\
         (i < j ==> ?nin nout. static_abort_emit_io inst nin nout /\
                              nin <= m /\ h + nin = m + nout) /\
         (i = j ==> MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
           (inst.inst_opcode = LOG ==> topics <= 4) /\
           (if inst.inst_opcode = LOG then 2 + topics else 2) <= m))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all generated_static_prefix_shared_edge >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `!t. _` kall_tac >>
  (* E0140: qexistsl [`a`, `mid`, `b`] >> simp[] >> simp[LET_THM]
     eliminated the nested accounting witnesses too early. *)
  map_every Q.EXISTS_TAC [`a`, `mid`, `b`] >>
  ntac 7 (conj_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac [LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `inst.inst_opcode = NOP` >>
  `i <= j /\ j < LENGTH bb.bb_instructions /\ i < LENGTH bb.bb_instructions` by
    gvs[static_abort_pair_def] >>
  `inst_shape_ok inst /\ codegen_ready_inst inst` by
    (simp[Abbr `inst`] >> metis_tac[EVERY_EL]) >>
  Cases_on `inst.inst_opcode = NOP`
  >- (disj1_tac >>
      gvs[Abbr `inst`, generate_inst_plan_def, codegen_ready_inst_def, is_param_opcode_def,
          is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
          is_unlowered_internal_call_opcode_def]) >>
  disj2_tac >> suspend "regular"
QED

Resume generated_static_head_factors[regular]:
  `EVERY (\bb'. EVERY (\v. EVERY (\op. op <> dead_stack_marker)
    v.inst_operands) bb'.bb_instructions) fn.fn_blocks` by
    metis_tac[codegen_ready_fn_no_marker] >>
  qpat_assum `dfs_block_state _ _ _ _ _ _ ps_dfs`
    (mp_then (Pat `dfs_block_state _ _ _ _ _ _ _`) mp_tac
      block_plan_state_static) >>
  disch_then (fn th =>
    qpat_assum `block_plan_state _ _ _ _ _ _ i ps`
      (mp_then (Pat `block_plan_state _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => drule_all (SRULE [] th)) >>
  (* E0145: simp[] >> strip_tac traversed the existential conclusion. *)
  disch_then (strip_assume_tac o SRULE []) >>
  `inst.inst_opcode <> PHI` by
    (`bb_well_formed bb` by
      (fs[codegen_ready_fn_def, wf_function_def] >>
       metis_tac[livenessTransferProofsTheory.lookup_block_mem]) >>
     qspecl_then [`bb.bb_instructions`, `i`] mp_tac phi_prefix_not_phi >>
     (impl_tac >- metis_tac[bb_well_formed_def]) >> simp[Abbr `inst`]) >>
  `inst.inst_opcode <> JMP` by
    (Cases_on `i = j`
     >- (fs[static_abort_pair_def, Abbr `inst`]) >>
     `~is_terminator inst.inst_opcode` by
       (qpat_assum `static_abort_pair bb i j`
          (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
            REWRITE_RULE [static_abort_pair_def]) >>
        disch_then (qspecl_then [`i`, `inst`] mp_tac) >>
        simp[get_instruction_def, Abbr `inst`]) >>
     strip_tac >> gvs[is_terminator_def]) >>
  `LENGTH (compute_operands inst) <= 16 /\ inst.inst_opcode <> OFFSET /\
   ~is_pre_codegen_opcode inst.inst_opcode` by
    gvs[codegen_ready_inst_def, inst_shape_ok_def] >>
  `generate_regular_inst_plan lv dfg cfg fn inst
    (live_vars_at lv bb.bb_label (i+1)) (bb_is_halting bb)
    (i+1 < LENGTH bb.bb_instructions /\
      is_terminator (EL (i+1) bb.bb_instructions).inst_opcode)
    bb.bb_label ps = (a,mid)` by
    gvs[generate_inst_plan_def] >>
  `!l. MEM (Label l) (compute_operands inst) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (rpt strip_tac >> first_x_assum irule >>
     qexistsl [`inst`, `i`] >> simp[get_instruction_def, Abbr `inst`]) >>
  (* E0124: drule_all on the mixed lv/lbl forms resisted matching. *)
  (* E0131: fs[] retained analysis equalities without normalizing. *)
  qpat_x_assum `lv = _` SUBST_ALL_TAC >>
  qpat_x_assum `dfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qpat_x_assum `bb.bb_label = lbl`
    (* E0145: rewrite_tac [th] implicitly unwound accounting binders. *)
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> pure_rewrite_tac [th]) >>
  (* Incoming state facts retain EL i; normalize only the needed bound. *)
  `LENGTH (compute_operands inst) <=
   LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst)
     (live_vars_at (liveness_analyze fn) lbl (i+1)) ps)).ps_stack` by
    simp[Abbr `inst`] >>
  drule_all regular_plan_admin_decomposition >> strip_tac >>
  (* Earlier diagnostic stopped here: FAIL_TAC "placements and arities". *)
  `asm_block_at prog pc (execute_plan cplan.cp_initial_fmp pre) /\
   asm_block_at prog (pc + LENGTH (execute_plan cplan.cp_initial_fmp pre))
     (execute_plan cplan.cp_initial_fmp emit) /\
   asm_block_at prog
     (pc + LENGTH (execute_plan cplan.cp_initial_fmp pre) +
       LENGTH (execute_plan cplan.cp_initial_fmp emit))
     (execute_plan cplan.cp_initial_fmp post)` by
    (qpat_assum `asm_block_at prog pc (execute_plan _ a)` mp_tac >>
     (* Broad simp[execute_plan_append, asm_block_at_append, ADD_ASSOC]
        timed out on the full planner context. *)
     qpat_assum `a = _` (fn th =>
       pure_rewrite_tac [th, execute_plan_append, asm_block_at_append,
         LENGTH_APPEND, GSYM ADD_ASSOC]) >>
     strip_tac >> asm_rewrite_tac[]) >>
  (* E0138: five-witness simp[] left an addition-order placement goal;
     simp[AC ADD_ASSOC ADD_COMM] timed out. Use explicit projection. *)
  map_every Q.EXISTS_TAC [`pre`, `emit`, `post`, `ps6`, `ps7`, `m`, `h`] >>
  ntac 13 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "nonterminal_io" >> suspend "terminal_io"
QED

Resume generated_static_head_factors[nonterminal_io]:
  strip_tac >>
  `~is_terminator inst.inst_opcode /\
   ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                         SSTORE;TSTORE;LOG]` by
    (qpat_assum `static_abort_pair bb i j`
       (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
         REWRITE_RULE [static_abort_pair_def]) >>
     disch_then (qspecl_then [`i`, `inst`] mp_tac) >>
     simp[get_instruction_def, Abbr `inst`]) >>
  (* Earlier drule_all lacked the folded inst_wf and param facts. *)
  `inst_wf inst /\ ~is_param_opcode inst.inst_opcode` by
    simp[Abbr `inst`] >>
  drule_all static_abort_regular_net_io >> simp[]
QED

Resume generated_static_head_factors[terminal_io]:
  (* Earlier diagnostic: strip_tac >> FAIL_TAC "terminal accounting". *)
  strip_tac >>
  `MEM inst.inst_opcode [SSTORE;TSTORE;LOG]` by
    gvs[static_abort_pair_def, Abbr `inst`, get_instruction_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `inst_wf inst` by simp[Abbr `inst`] >>
  qpat_x_assum `MEM inst.inst_opcode [SSTORE;TSTORE;LOG]`
    (strip_assume_tac o REWRITE_RULE [MEM]) >>
  gvs[inst_wf_def, codegen_ready_inst_def,
    compute_operands_def, python_stack_operands_def,
    ir_specific_operand_order_def, AllCaseEqs()]
QED

Finalise generated_static_head_factors
