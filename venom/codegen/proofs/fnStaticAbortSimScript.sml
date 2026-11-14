Theory fnStaticAbortSim
Ancestors
  staticAbortDefs fnBlockPlanStatic fnPlanPrefix contextCodegenRel
  codegen unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem asmIR
  symbolResolve list staticAbortPrefix fnBlockBodyHelpers fnPlanLineage
  staticAbortTrace venomInst

(* Only planner provenance and concrete stack shape survive memory overlap.
   Operand labels must resolve: an unknown label is an assembly error,
   rather than an EVM exception. ASSERT may revert before the static write,
   so this companion does not assert a matching source abort constructor. *)
Theorem generated_lineage_static_abort_prefix:
  !rpolicy unit cp prog fn r lv dfg cfg ch growth base ctr fn_ops ps_end
    lbl bb ps_l ps_dfs ps_dfs_after h promised block_ops ps_after
    i j ps ops ps' ast top rest.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\ context_plan_layout_wf cp /\
    codegen_ready unit.cu_context /\ ctx_wf unit.cu_context /\
    fmp_lowered_context_wf unit.cu_context /\
    reachable_call_graph_acyclic unit.cu_context /\
    MEM fn unit.cu_context.ctx_functions /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    base = r.sr_spill_base /\ fn_ops = r.sr_plan /\
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
      SOME (fn_ops,ps_end) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth base ctr) lbl ps_l /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth base ctr) lbl ps_dfs /\
    generate_block_plan lv dfg cfg fn bb ps_dfs =
      SOME (block_ops,ps_dfs_after) /\
    generate_block_plan lv dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops,ps_after) /\
    block_plan_state lv dfg cfg fn bb
      (ps_l with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>)
      i ps /\
    phi_prefix_length bb.bb_instructions <= i /\
    static_abort_pair bb i j /\
    generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (i - LENGTH (get_params bb.bb_instructions)) (SUC j - i)
      (DROP i bb.bb_instructions) ps = SOME (ops,ps') /\
    (!k inst l.
      i <= k /\ k <= j /\ get_instruction bb k = SOME inst /\
      MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    ast.as_call_ctx.cc_static /\
    ast.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops)
    ==>
    ?n out.
      n <= LENGTH (execute_plan cp.cp_initial_fmp ops) + 4 /\
      (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast = AsmFault out \/
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast = AsmRevert out) /\
      out.as_requests = ast.as_requests /\ out.as_returndata = [] /\
      !k mid.
        k < n /\
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog k ast = AsmOK mid ==>
        mid.as_requests = ast.as_requests /\ mid.as_pc < LENGTH prog /\
        case EL mid.as_pc prog of
          AsmOp name => IS_SOME (evm_opcode_byte name) /\
            ~MEM name ["CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
                       "CREATE"; "CREATE2"; "SELFDESTRUCT"]
        | AsmDataHeader _ => F
        | AsmDataItem _ => F
        | AsmDataLabel _ => F
        | _ => T
Proof
  rpt gen_tac >> strip_tac >>
  `codegen_ready_fn fn` by
    metis_tac[codegen_ready_def, EVERY_MEM] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >> drule stackPlanGenTheory.FIND_SOME_MEM >> simp[]) >>
  `EVERY codegen_ready_inst bb.bb_instructions` by
    (fs[codegen_ready_fn_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY inst_shape_ok bb.bb_instructions` by
    (fs[unit_shape_ok_def, EVERY_MEM, fn_shape_ok_def] >>
     metis_tac[MEM_fn_insts_blocks, fn_insts_def]) >>
  `non_param_insts bb =
     DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions` by
    metis_tac[non_param_insts_drop, codegen_ready_fn_def] >>
  `LENGTH (get_params bb.bb_instructions) <= i` by
    fs[block_plan_state_def] >>
  rename1 `generate_context_plan _ = SOME cplan` >>
  `?n out. n <= LENGTH (execute_plan cplan.cp_initial_fmp ops) + 4 /\
    static_abort_exception (SND (compute_label_offsets prog))
      (build_offset_to_pc prog) prog n ast out` suffices_by
    simp[static_abort_exception_def, static_abort_trace_def, static_abort_safe_at_def] >>
  gvs[] >> irule static_abort_block_prefix >>
  simp[] >> conj_tac >- metis_tac[] >>
  first_assum (irule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
  rpt (first_assum (irule_at Any)) >>
  qexists `rest` >> simp[] >> metis_tac[]
QED

Theorem generated_static_abort_prefix:
  !rpolicy unit cp prog fn r lv dfg cfg ch growth base ctr fn_ops ps_end
    lbl bb ps0 block_ops ps_after i j ps ops ps' ast top rest.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\ context_plan_layout_wf cp /\
    codegen_ready unit.cu_context /\ ctx_wf unit.cu_context /\
    fmp_lowered_context_wf unit.cu_context /\
    reachable_call_graph_acyclic unit.cu_context /\
    MEM fn unit.cu_context.ctx_functions /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    base = r.sr_spill_base /\ fn_ops = r.sr_plan /\
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
      SOME (fn_ops,ps_end) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    dfs_block_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth base ctr) lbl ps0 /\
    generate_block_plan lv dfg cfg fn bb ps0 = SOME (block_ops,ps_after) /\
    block_plan_state lv dfg cfg fn bb ps0 i ps /\
    phi_prefix_length bb.bb_instructions <= i /\
    static_abort_pair bb i j /\
    generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
      (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
      (i - LENGTH (get_params bb.bb_instructions)) (SUC j - i)
      (DROP i bb.bb_instructions) ps = SOME (ops,ps') /\
    (!k inst l.
      i <= k /\ k <= j /\ get_instruction bb k = SOME inst /\
      MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    ast.as_call_ctx.cc_static /\
    ast.as_stack = top ++ rest /\ LENGTH top = LENGTH ps.ps_stack /\
    asm_block_at prog ast.as_pc (execute_plan cp.cp_initial_fmp ops)
    ==>
    ?n out.
      n <= LENGTH (execute_plan cp.cp_initial_fmp ops) + 4 /\
      (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast = AsmFault out \/
       asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
         prog n ast = AsmRevert out) /\
      out.as_requests = ast.as_requests /\ out.as_returndata = [] /\
      !k mid.
        k < n /\
        asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
          prog k ast = AsmOK mid ==>
        mid.as_requests = ast.as_requests /\ mid.as_pc < LENGTH prog /\
        case EL mid.as_pc prog of
          AsmOp name => IS_SOME (evm_opcode_byte name) /\
            ~MEM name ["CALL"; "CALLCODE"; "STATICCALL"; "DELEGATECALL";
                       "CREATE"; "CREATE2"; "SELFDESTRUCT"]
        | AsmDataHeader _ => F
        | AsmDataItem _ => F
        | AsmDataLabel _ => F
        | _ => T
Proof
  rpt gen_tac >> strip_tac >>
  drule fnPlanLineageTheory.dfs_block_state_lineage_state >> strip_tac >>
  `ps0 with <|ps_cleanup_height := ps0.ps_cleanup_height;
              ps_cleanup_promised := ps0.ps_cleanup_promised|> = ps0` by simp[] >>
  gvs[] >> irule (SRULE [] generated_lineage_static_abort_prefix) >>
  first_assum (irule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `dfs_block_state _ _ _ _ _ _ _`)) >>
  rpt (first_assum (irule_at Any)) >>
  qexistsl [`ps_after`, `ps0.ps_cleanup_promised`, `ps0.ps_cleanup_height`] >>
  simp[] >> metis_tac[]
QED
