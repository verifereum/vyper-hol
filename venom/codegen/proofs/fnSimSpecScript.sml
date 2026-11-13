(*
 * The two function-level simulation statements of venomToAsmProps
 * (gen_fn_simulation, gen_fn_frame_simulation) at one fixed fuel, so the
 * fuel induction that proves them can name its hypothesis and its step.
 * Each definition's body is its theorem's statement with fuel free.
 *
 * TOP-LEVEL:
 *   gen_fn_sim_at        - gen_fn_simulation at fuel
 *   gen_fn_frame_sim_at  - gen_fn_frame_simulation at fuel
 *)

Theory fnSimSpec
Ancestors
  frameRel codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers
  cleanOpsSim genBlockSim codegen symbolResolve venomExecSemantics venomState
  venomInst fcgDefs livenessDefs dfgDefs cfgDefs fnPlanLineage
  list rich_list finite_map arithmetic dftGasToListBound asmRunBounded venomRunBounded

Definition gen_fn_sim_at_def:
  gen_fn_sim_at fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i r fn vs as Inv ra pc_ret rest.
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
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
      fn_entry_state_rel cp fn vs as ra rest /\
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 fn_return_state_rel ctx cp fn vs' as as')
End

Definition gen_fn_frame_sim_at_def:
  gen_fn_frame_sim_at fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
     spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
     vs as Inv ra pc_ret rest mem0.
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
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 context_memory_rel cp vs'.vs_memory as'.as_memory /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      read_byte b as'.as_memory = read_byte b mem0) /\
                 shared_state_rel vs' as')
End

(* NONE retains the original qualitative interface.  SOME records a bound
   on the very same witness, not on an independently chosen execution. *)
Definition cost_le_def:
  (cost_le NONE n = T) /\
  (cost_le (SOME B) (n:num) = (n <= B))
End

Theorem cost_le_mono:
  cost_le b n /\
  (c = NONE \/ ?B C. b = SOME B /\ c = SOME C /\ B <= C) ==>
  cost_le c n
Proof
  Cases_on `b` >> Cases_on `c` >> simp[cost_le_def] >> decide_tac
QED

Theorem cost_le_add:
  cost_le b m ==> cost_le (OPTION_MAP (\B. n + B) b) (n + m)
Proof
  Cases_on `b` >> simp[cost_le_def]
QED

(* A static source size and a deliberately generous fuel recurrence. *)
Definition context_inst_count_def:
  context_inst_count ctx =
    SUM (MAP (\fn. SUM (MAP (\bb. LENGTH bb.bb_instructions) fn.fn_blocks))
             ctx.ctx_functions)
End

Theorem context_inst_count_block:
  MEM fn ctx.ctx_functions /\ MEM bb fn.fn_blocks ==>
  LENGTH bb.bb_instructions <= context_inst_count ctx
Proof
  strip_tac >>
  qspecl_then [`fn.fn_blocks`, `\bb. LENGTH bb.bb_instructions`]
    (drule_then assume_tac) member_measure_le_sum >>
  qspecl_then [`ctx.ctx_functions`,
    `\fn. SUM (MAP (\bb. LENGTH bb.bb_instructions) fn.fn_blocks)`]
    (drule_then assume_tac) member_measure_le_sum >>
  gvs[context_inst_count_def] >> decide_tac
QED

Definition fn_sim_coefficient_def:
  fn_sim_coefficient ctx prog =
    (context_inst_count ctx + 2) * (LENGTH prog + 9)
End

Definition fn_sim_budget_def:
  (fn_sim_budget ctx prog 0 = 0) /\
  (fn_sim_budget ctx prog (SUC fuel) =
     fn_sim_coefficient ctx prog * (fn_sim_budget ctx prog fuel + 1))
End

Theorem fn_sim_budget_absorb:
  !d s p b c:num. d <= s ==>
  p + (d + 1) * (p + b + c + 1) <= (s + 2) * (p + c + 2) * (b + 1)
Proof
  rpt strip_tac >>
  `p + b + c + 1 <= (p + c + 2) * (b + 1)` by
    simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  `p <= (p + c + 2) * (b + 1)` by
    simp[LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB] >>
  `(d + 1) * (p + b + c + 1) <= (s + 1) * ((p + c + 2) * (b + 1))` by
    (irule LESS_MONO_MULT2 >> simp[]) >>
  `s + 2 = (s + 1) + 1` by decide_tac >>
  asm_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_ASSOC] >> decide_tac
QED

(* q is static but program-dependent; it is chosen outside all runtime
   states, invariants, return stacks and oracle readings. *)
Definition gen_fn_sim_cost_at_def:
  gen_fn_sim_cost_at q fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i r fn vs as Inv ra pc_ret rest.
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
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
      fn_entry_state_rel cp fn vs as ra rest /\
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 fn_return_state_rel ctx cp fn vs' as as')
End

Definition gen_fn_frame_sim_cost_at_def:
  gen_fn_frame_sim_cost_at q fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
     spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
     vs as Inv ra pc_ret rest mem0.
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
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 context_memory_rel cp vs'.vs_memory as'.as_memory /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      read_byte b as'.as_memory = read_byte b mem0) /\
                 shared_state_rel vs' as')
End

Theorem gen_fn_sim_cost_none[simp]:
  gen_fn_sim_cost_at NONE fuel <=> gen_fn_sim_at fuel
Proof
  simp[gen_fn_sim_cost_at_def, gen_fn_sim_at_def, cost_le_def]
QED

Theorem gen_fn_frame_sim_cost_none[simp]:
  gen_fn_frame_sim_cost_at NONE fuel <=> gen_fn_frame_sim_at fuel
Proof
  simp[gen_fn_frame_sim_cost_at_def, gen_fn_frame_sim_at_def, cost_le_def]
QED

(* Independent resource modes: NONE removes cost, F removes creation safety. *)
Definition gen_fn_sim_resource_at_def:
  gen_fn_sim_resource_at safe q fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i r fn vs as Inv ra pc_ret rest.
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
      asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
      fn_entry_state_rel cp fn vs as ra rest /\
      (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
      (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 fn_return_state_rel ctx cp fn vs' as as')
End

Definition gen_fn_frame_sim_resource_at_def:
  gen_fn_frame_sim_resource_at safe q fuel <=>
    !rpolicy unit cp prog ctx lo o2pc i fn r liveness dfg cfg ch growth
     spill_base lbl_ctr fn_ops ps_end bb pred ps ps_dfs block_ops ps_dfs_after
     vs as Inv ra pc_ret rest mem0.
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
      (safe ==> !f inst s. Inv ctx f inst s ==> inst_create_size_ok inst s)
      ==>
      (!vs'. run_blocks fuel ctx fn vs = Halt vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 asm_steps lo o2pc prog n as = AsmHalt as' /\
                 venom_asm_terminal_rel vs' as') /\
      (!a vs'. run_blocks fuel ctx fn vs = Abort a vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                  (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
                 venom_asm_terminal_rel vs' as') /\
      (!ret vs'. run_blocks fuel ctx fn vs = IntRet ret vs' ==>
         ?n as'. cost_le (OPTION_MAP (\F. F unit cp prog) q) n /\
                 (safe ==> create_safe_prefix lo o2pc prog n as) /\
                 asm_steps lo o2pc prog n as = AsmOK as' /\
                 as'.as_pc = pc_ret /\
                 as'.as_stack = REVERSE ret.iret_values ++ rest /\
                 context_memory_rel cp vs'.vs_memory as'.as_memory /\
                 (!b. context_spill_byte cp b /\
                      ~closure_spill_byte ctx cp fn.fn_name b ==>
                      read_byte b as'.as_memory = read_byte b mem0) /\
                 shared_state_rel vs' as')
End

Theorem gen_fn_sim_resource_off[simp]:
  gen_fn_sim_resource_at F q fuel <=> gen_fn_sim_cost_at q fuel
Proof
  simp[gen_fn_sim_resource_at_def, gen_fn_sim_cost_at_def]
QED

Theorem gen_fn_frame_sim_resource_off[simp]:
  gen_fn_frame_sim_resource_at F q fuel <=> gen_fn_frame_sim_cost_at q fuel
Proof
  simp[gen_fn_frame_sim_resource_at_def, gen_fn_frame_sim_cost_at_def]
QED
