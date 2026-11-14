Theory fnStaticAbortBoundary
Ancestors
  fnStaticAbortSim staticAbortExec frameRel contextCodegenRel codegenRel
  contextStaticAbortRel fnBlockBodySteps stackOpSim fnBlockBodyHelpers
  fnPlanPrefix venomWf stackPlanGen staticAbortDefs list venomInst
  venomExecProps unitShapeDefs fnBlockPlanStatic planExec

(* The full pre-cut frame relation exposes exactly the concrete stack shape
   and shared fields needed by generated_lineage_static_abort_prefix.
   No relation on spill values is asserted after this cut. *)
Theorem static_abort_frame_cut:
  !ctx cp lo fn ra rest mem0 ps vs ast.
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs ast ==>
  (?top. ast.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack) /\
  ast.as_call_ctx = vs.vs_call_ctx /\
  ast.as_requests = vs.vs_requests
Proof
  simp[fn_frame_inv_def, context_venom_asm_rel_def,
       plan_stack_rel_def, frame_view_def] >> metis_tac[]
QED

(* Only the memory premise is relaxed, and only after independently
   classifying the current source suffix. The concrete frame stays full. *)
Definition body_inv_abort_def:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 <=>
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cpl /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\ EL i cpl.cp_regions = r /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    codegen_context_obligations_abort Inv ctx cpl /\
    (!f inst l.
       MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
       inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
       IS_SOME (FLOOKUP lo l)) /\
    reachability_closed Inv ctx /\
    (!inst. active_inst fn inst vs ==> Inv ctx fn inst vs) /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    ch = cleanup_caller_height (LENGTH ctx.ctx_functions) ctx
           (fcg_analyze ctx) fn.fn_name /\
    growth = cleanup_growth_table ctx (fcg_analyze ctx) /\
    spill_base = r.sr_spill_base /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_ops = r.sr_plan /\
    ps_end.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    fn_reachable fn bb.bb_label /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_l /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)
      bb.bb_label ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after) /\
    generate_block_plan liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    ps_after.ps_alloc = ps_dfs_after.ps_alloc /\
    ps_after.ps_spilled = ps_dfs_after.ps_spilled /\
    (?prefixL prefixD core.
       ps_after.ps_stack = prefixL ++ core /\
       ps_dfs_after.ps_stack = prefixD ++ core /\
       (!v. MEM v (live_vars_at liveness bb.bb_label
                     (LENGTH bb.bb_instructions)) ==>
          ~MEM (Var v) prefixL /\ ~MEM (Var v) prefixD)) /\
    block_plan_state liveness dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      k ps /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions))
      (DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb))
      ps = SOME (rest_ops, ps_after) /\
    block_ops = SOLabel bb.bb_label :: prefix_ops ++ rest_ops /\
    phi_prefix_length bb.bb_instructions <= k /\
    (!i j. revert_forward_pair bb i j ==> k <= i \/ j < k) /\
    vs.vs_inst_idx = k /\
    asm_block_at prog pc0 (execute_plan cpl.cp_initial_fmp block_ops) /\
    ast.as_pc = pc0 + LENGTH (execute_plan cpl.cp_initial_fmp
                                 (SOLabel bb.bb_label :: prefix_ops)) /\
    fn_frame_inv ctx cpl lo fn ra rest mem0 ps vs ast /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
End

(* Halt and IntRet retain the exact original clauses. Only Abort may
   forget the source exception constructor and irrelevant spill values. *)
Definition body_result_abort_def:
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast res <=>
    (!vs'. res = Halt vs' ==>
       ?n ast'. asm_steps lo o2pc prog n ast = AsmHalt ast' /\
               venom_asm_terminal_rel vs' ast') /\
    (!a vs'. res = Abort a vs' ==>
       ?n ast'. (asm_steps lo o2pc prog n ast = AsmRevert ast' \/
                 asm_steps lo o2pc prog n ast = AsmFault ast') /\
                ast'.as_requests = vs'.vs_requests) /\
    (!ret vs'. res = IntRet ret vs' ==>
       ?n ast'. asm_steps lo o2pc prog n ast = AsmOK ast' /\
               ast'.as_pc = pc_ret /\
               ast'.as_stack = REVERSE ret.iret_values ++ rest /\
               context_memory_rel cpl vs'.vs_memory ast'.as_memory /\
               (!b. context_spill_byte cpl b /\
                    ~closure_spill_byte ctx cpl fn.fn_name b ==>
                    read_byte b ast'.as_memory = read_byte b mem0) /\
               shared_state_rel vs' ast')
End

Theorem body_result_abort_prefix:
  !lo o2pc prog cpl ctx fn mem0 pc_ret rest ast ast1 n res.
    asm_steps lo o2pc prog n ast = AsmOK ast1 /\
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast1 res ==>
    body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast res
Proof
  rw[body_result_abort_def] >> gvs[] >>
  qexistsl_tac [`n + n'`, `ast'`] >>
  metis_tac[asm_steps_add_ok]
QED

(* This is the single implementation-level cut: all later consumers use
   the full invariant up to here and only the exception witness afterwards. *)
Theorem body_inv_abort_pending:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  in_static_abort_prefix fn vs ==>
  ?n out. (asm_steps lo o2pc prog n ast = AsmFault out \/
           asm_steps lo o2pc prog n ast = AsmRevert out) /\
          out.as_requests = vs.vs_requests
Proof
  pure_rewrite_tac[body_inv_abort_def] >> strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[EL_MEM] >>
  `codegen_ready_fn fn` by
    (fs[codegen_context_obligations_abort_def, codegen_ready_def, EVERY_MEM]) >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = vs.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM r cpl.cp_regions /\ r.sr_fn_name = fn.fn_name` by
    metis_tac[body_context_region_fn_name] >>
  `bb_well_formed bb` by fs[codegen_ready_fn_def, wf_function_def] >>
  `non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions))
                                   bb.bb_instructions` by
    metis_tac[non_param_insts_drop, codegen_ready_fn_def] >>
  `LENGTH (get_params bb.bb_instructions) <= k` by
    fs[block_plan_state_def] >>
  `vs.vs_call_ctx.cc_static /\ static_abort_at bb k` by
    gvs[in_static_abort_prefix_def] >>
  `?j. static_abort_pair bb k j` by
    metis_tac[static_abort_at_def] >>
  `k <= j /\ j < LENGTH bb.bb_instructions` by fs[static_abort_pair_def] >>
  `DROP (k - LENGTH (get_params bb.bb_instructions)) (non_param_insts bb) =
   DROP k bb.bb_instructions` by simp[rich_listTheory.DROP_DROP_T] >>
  `?ops ps' post.
    generate_block_insts_prefix liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions)
      (k - LENGTH (get_params bb.bb_instructions)) (SUC j - k)
      (DROP k bb.bb_instructions) ps = SOME (ops, ps') /\
    rest_ops = ops ++ post` by
    (`SUC j - k <= LENGTH (DROP k bb.bb_instructions)` by
       (simp[] >> decide_tac) >>
     qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _`
       mp_tac >>
     simp[] >>
     qpat_x_assum `SUC j - k <= LENGTH (DROP k _)` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[generate_block_insts_plan_split]) >>
  `asm_block_at prog ast.as_pc (execute_plan cpl.cp_initial_fmp ops)` by
    (qpat_x_assum `asm_block_at _ _ _` mp_tac >>
     gvs[execute_plan_append, execute_plan_def, asm_block_at_append,
         APPEND_ASSOC]) >>
  `!q inst l. k <= q /\ q <= j /\ get_instruction bb q = SOME inst /\
       MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)` by
    (rpt strip_tac >>
     `q < LENGTH bb.bb_instructions /\ EL q bb.bb_instructions = inst` by
       gvs[get_instruction_def] >>
     `inst.inst_opcode <> PHI` by
       (qpat_x_assum `EL q _ = inst` (SUBST1_TAC o SYM) >>
        irule phi_prefix_not_phi >>
        fs[bb_well_formed_def] >> first_assum ACCEPT_TAC) >>
     `MEM inst (fn_insts fn)` by
       (simp[fn_insts_def] >> irule MEM_fn_insts_blocks >>
        qexists `bb` >> simp[] >> metis_tac[EL_MEM]) >>
     metis_tac[]) >>
  drule static_abort_frame_cut >> strip_tac >>
  `?n out.
     n <= LENGTH (execute_plan cpl.cp_initial_fmp ops) + 4 /\
     (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog n ast = AsmFault out \/
      asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog n ast = AsmRevert out) /\
     out.as_requests = ast.as_requests /\ out.as_returndata = [] /\
     !q mid. q < n /\
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog q ast = AsmOK mid ==>
       mid.as_requests = ast.as_requests /\ mid.as_pc < LENGTH prog /\
       case EL mid.as_pc prog of
         AsmOp name => IS_SOME (evm_opcode_byte name) /\
           ~MEM name ["CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
                      "CREATE"; "CREATE2"; "SELFDESTRUCT"]
       | AsmDataHeader _ => F | AsmDataItem _ => F | AsmDataLabel _ => F
       | _ => T` suffices_by metis_tac[] >>
  irule generated_lineage_static_abort_prefix >>
  first_assum (irule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
  rpt (first_assum (irule_at Any)) >>
  fs[codegen_context_obligations_abort_def] >>
  metis_tac[]
QED

(* Source classification is supplied by staticAbortExec, not by a second
   instruction induction. In particular a pending suffix cannot return. *)
Theorem body_result_abort_pending:
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
      growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
      block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 vs ast Inv
      ra pc_ret rest mem0 /\
  in_static_abort_prefix fn vs ==>
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast
    (exec_block fuel ctx bb vs)
Proof
  strip_tac >>
  `vs.vs_call_ctx.cc_static /\ static_abort_at bb vs.vs_inst_idx` by
    gvs[body_inv_abort_def, in_static_abort_prefix_def] >>
  simp[body_result_abort_def, static_abort_at_no_halt,
       static_abort_at_no_normal] >> rpt strip_tac >>
  drule_all body_inv_abort_pending >> strip_tac >>
  drule_all static_abort_at_abort_requests >> strip_tac >>
  metis_tac[]
QED

(* Existing strict instruction conclusions can still be consumed unchanged.
   This implication never relaxes either normal-result relation. *)
Theorem body_result_abort_from_strict:
  body_result_simple lo o2pc prog cpl ctx fn mem0 pc_ret rest ast res ==>
  body_result_abort lo o2pc prog cpl ctx fn mem0 pc_ret rest ast res
Proof
  simp[body_result_simple_def, body_result_def, fnSimSpecTheory.cost_le_def,
       body_result_abort_def, venom_asm_terminal_rel_def] >>
  metis_tac[]
QED
