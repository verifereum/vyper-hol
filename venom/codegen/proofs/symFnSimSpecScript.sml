(*
 * The function-level statements of the label-discipline proof at one fixed
 * fuel: fnSimSpec's gen_fn_sim_at and gen_fn_frame_sim_at with the symbolic
 * run added.  The symbolic run starts from a state related to the concrete
 * one and takes the same n steps: it ends where the concrete run halts,
 * reverts or faults, and at an internal return it is OK, related, and holds
 * the returned values as words above the caller's symbolic stack.  The
 * control leaves (INVOKE, RET, JMP, JNZ) and the fuel induction share them.
 *
 * TOP-LEVEL:
 *   sym_fn_sim_at        - gen_fn_sim_at with the symbolic run
 *   sym_fn_frame_sim_at  - gen_fn_frame_sim_at with the symbolic run
 *)

Theory symFnSimSpec
Ancestors
  fnSimSpec codegenSymRel asmSymBridge asmSymSem frameRel codegenRel
  contextCodegenRelProps fnPlanLineage codegen venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs

(* The symbolic run's static premises are those of the top theorem: the
   label-flow facts of the unit, the code_end offset bound at every
   invariant point, the data segment's shape, the program's static
   well-formedness, and every data label of the program in env.  The entry
   symbolic state holds the return label ret (Lab ret 0, ret a code label of
   the program) and the parameters as words above the caller's symbolic
   stack srest; its memory labels lie in spill regions. *)
Definition sym_fn_sim_at_def:
  sym_fn_sim_at fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i r fn vs as Inv ra pc_ret rest
     env ret srest ss.
      ctx = unit.cu_context /\
      lo = SND (compute_label_offsets prog) /\
      o2pc = build_offset_to_pc prog /\
      generate_context_plan ctx = SOME cp /\
      codegen_assembly rpolicy unit = SOME prog /\
      unit_shape_ok unit /\
      i < LENGTH ctx.ctx_functions /\
      EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
      MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
      (!f inst callee_name args callee.
         MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
         MEM inst (fn_insts f) /\
         inst.inst_opcode = INVOKE /\
         inst.inst_operands = Label callee_name :: args /\
         lookup_function callee_name ctx.ctx_functions = SOME callee ==>
         fn_has_retpc callee) /\
      (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
      codegen_context_obligations Inv ctx cp /\
      reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
      ~vs.vs_call_ctx.cc_static /\
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
      fn_entry_state_rel cp fn vs as ra rest /\
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
      (* ----- The symbolic side ----- *)
      label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
      sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      asm_sym_rel prog env as ss /\
      ss.sym_stack =
        (if fn_has_retpc fn then [Lab ret 0] else []) ++
        MAP Val (REVERSE vs.vs_params) ++ srest /\
      (fn_has_retpc fn ==> MEM (AsmLabel ret) prog) /\
      (!b. b IN FDOM ss.sym_mem_labels ==> context_spill_byte cp b)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as' /\
                 sym_terminal (sym_steps prog env n ss)) /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as' /\
                 sym_terminal (sym_steps prog env n ss)) /\
      (!rv vs'. run_blocks fuel ctx fn vs = IntRet rv vs' ==>
         ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE rv.iret_values ++ rest /\
                 fn_return_state_rel ctx cp fn vs' as as' /\
                 sym_steps prog env n ss = SymOK ss' /\
                 asm_sym_rel prog env as' ss' /\
                 ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
                 (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
End

(* From a later block of the function, in the symbolic frame invariant with
   labs0 the memory labels at the function's entry. *)
Definition sym_fn_frame_sim_at_def:
  sym_fn_frame_sim_at fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
     spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
     vs as Inv ra pc_ret rest mem0 env ret srest labs0 ss.
      ctx = unit.cu_context /\
      lo = SND (compute_label_offsets prog) /\
      o2pc = build_offset_to_pc prog /\
      generate_context_plan ctx = SOME cp /\
      codegen_assembly rpolicy unit = SOME prog /\
      unit_shape_ok unit /\
      i < LENGTH ctx.ctx_functions /\
      EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
      MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
      (!f inst callee_name args callee.
         MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
         MEM inst (fn_insts f) /\
         inst.inst_opcode = INVOKE /\
         inst.inst_operands = Label callee_name :: args /\
         lookup_function callee_name ctx.ctx_functions = SOME callee ==>
         fn_has_retpc callee) /\
      (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
      codegen_context_obligations Inv ctx cp /\
      reachability_closed Inv ctx /\ fn_entry_inv Inv ctx fn vs /\
      ~vs.vs_call_ctx.cc_static /\
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
      bb <> HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
      lineage_entry liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)
        pred bb.bb_label ps /\
      vs.vs_prev_bb = SOME pred /\
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)
        vs.vs_current_bb ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_dfs_after) /\
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp block_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
      (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
         operand_val (frame_view fn ra vs) lo at =
         operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
      (* ----- The symbolic side ----- *)
      label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
      sym_unit_static_ok unit /\ asm_static_wf prog /\
      (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
      sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as' /\
                 sym_terminal (sym_steps prog env n ss)) /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as' /\
                 sym_terminal (sym_steps prog env n ss)) /\
      (!rv vs'. run_blocks fuel ctx fn vs = IntRet rv vs' ==>
         ?n as' ss'. asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE rv.iret_values ++ rest /\
                 context_memory_rel cp vs'.vs_memory as'.as_memory /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      read_byte b as'.as_memory = read_byte b mem0) /\
                 shared_state_rel vs' as' /\
                 sym_steps prog env n ss = SymOK ss' /\
                 asm_sym_rel prog env as' ss' /\
                 ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b) /\
                 (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
End
