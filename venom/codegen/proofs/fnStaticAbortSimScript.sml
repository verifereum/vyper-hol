Theory fnStaticAbortSim
Ancestors
  staticAbortDefs fnBlockPlanStatic fnPlanPrefix contextCodegenRel
  codegen unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem asmIR
  symbolResolve list

(* Only planner provenance and concrete stack shape survive memory overlap.
   Operand labels must resolve: an unknown label is an assembly error,
   rather than an EVM exception. ASSERT may revert before the static write,
   so this companion does not assert a matching source abort constructor. *)
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
  rpt strip_tac
QED
