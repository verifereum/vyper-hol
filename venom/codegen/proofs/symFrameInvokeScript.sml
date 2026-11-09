(*
 * Leaf B of the label-discipline proof, INVOKE: the call runs on the
 * symbolic machine without SymBad, from the callee's symbolic
 * function-level simulation at the same fuel (sym_fn_sim_at).  The
 * statement is codegen's own gen_invoke_frame_sim_deep with the symbolic
 * premises and conclusions added, over the same n steps.
 *
 * TOP-LEVEL:
 *   sym_invoke_frame_sim_deep
 *)
Theory symFrameInvoke
Ancestors
  symFnSimSpec codegenSymRel fnFrameDeepInvoke asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs list

(* INVOKE cannot consume the opaque code-end pointer. *)
Theorem sym_invoke_argument_not_code_end:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  rw[label_flow_ok_def] >>
  first_x_assum drule_all >> simp[] >> metis_tac[]
QED

Theorem sym_invoke_argument_shape:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args ==>
  opaque_use_ok fn /\ EVERY (\op. ~is_label_operand op) args
Proof
  strip_tac >>
  `opaque_use_ok fn /\ label_positions_ok inst` by
    (gvs[fn_shape_ok_def, EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  gvs[label_positions_ok_def]
QED

Theorem sym_invoke_argument_word_kind:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\ MEM op args /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  strip_tac >>
  drule_all sym_invoke_argument_shape >> strip_tac >>
  `~is_label_operand op` by gvs[EVERY_MEM] >>
  Cases_on `op` >> gvs[is_label_operand_def, op_kind_ok_def] >>
  metis_tac[fnFrameBoundaryInvokeTheory.invoke_arguments_not_retpc,
            sym_invoke_argument_not_code_end, MEM]
QED

Theorem sym_invoke_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  strip_tac >> strip_tac >> drule_all code_end_var_def_inst >> simp[]
QED

Theorem sym_invoke_output_word_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ MEM x inst.inst_outputs ==>
  op_kind_ok fn ret (Var x) (Val w)
Proof
  strip_tac >>
  `~code_end_var fn x /\ ~retpc_var fn x` by
    (conj_tac >- metis_tac[sym_invoke_output_not_code_end] >>
     drule_at (Pat `MEM inst (fn_insts fn)`)
       frameViewFactsTheory.noncopy_output_not_retpc >> simp[]) >>
  simp[op_kind_ok_def]
QED

Theorem mem_sval_at_range_cong:
  (!b. in_mem_range off 32 b ==> FLOOKUP m b = FLOOKUP m' b) ==>
  (mem_sval_at m off sv <=> mem_sval_at m' off sv)
Proof
  strip_tac >>
  `FLOOKUP m off = FLOOKUP m' off /\
   !i. MEM i (COUNT_LIST 32) ==>
       FLOOKUP m (off + i) = FLOOKUP m' (off + i)` by
    gvs[in_mem_range_def, rich_listTheory.MEM_COUNT_LIST] >>
  Cases_on `sv` >>
  simp[mem_sval_at_def, mem_label_at_def, EVERY_MEM,
       GSYM (cj 1 finite_mapTheory.flookup_thm)] >> metis_tac[]
QED

Theorem sym_invoke_external_labels_preserved:
  !ctx cp caller callee m1 m0.
  fn_directly_calls ctx caller callee /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
       FLOOKUP m1 b = FLOOKUP m0 b) ==>
  !b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp caller b ==>
      FLOOKUP m1 b = FLOOKUP m0 b
Proof
  metis_tac[fnFrameBoundaryInvokeTheory.invoke_closure_subset]
QED

Theorem sym_invoke_caller_spill_labels_preserved:
  !ctx cp caller callee r off m1 m0.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = caller /\ r.sr_spill_base <= off /\
  off + 32 <= r.sr_spill_end /\ fn_directly_calls ctx caller callee /\
  ~TC (fn_directly_calls ctx) caller caller /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
       FLOOKUP m1 b = FLOOKUP m0 b) ==>
  !b. in_mem_range off 32 b ==> FLOOKUP m1 b = FLOOKUP m0 b
Proof
  rpt strip_tac >>
  `r.sr_spill_base <= b /\ b < r.sr_spill_end` by
    gvs[in_mem_range_def] >>
  metis_tac[contextCodegenRelPropsTheory.context_spill_byte_of_region,
            fnFrameBoundaryInvokeTheory.invoke_caller_region_outside_callee]
QED

Theorem sym_invoke_frame_sim_deep:
  !fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops
   env ret srest labs0 ss.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    MEM fn ctx.ctx_functions /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    Inv ctx fn inst vs /\ active_inst fn inst vs /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    ~vs.vs_call_ctx.cc_static /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
    (* The callee's function-level simulation at this fuel. *)
    (!j callee rj cvs cas cra crest cpc.
       j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
       EL j cp.cp_regions = rj /\
       MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
       (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
       fn_entry_inv Inv ctx callee cvs /\
       ~cvs.vs_call_ctx.cc_static /\
       asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
       LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
       fn_entry_state_rel cp callee cvs cas cra crest /\
       (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
       (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as') /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE rv.iret_values ++ crest /\
                  fn_return_state_rel ctx cp callee vs' cas as')) /\
    opaque_use_ok fn /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    (* ----- The symbolic side ----- *)
    dfg = dfg_build_function fn /\
    MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    asm_static_wf prog /\
    code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
    (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
    (* The callee's symbolic function-level simulation at this fuel. *)
    sym_fn_sim_at fuel /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as' ss'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
         sym_steps prog env n ss = SymOK ss' /\
         sym_frame_inv prog env ctx cp fn ret srest labs0 ps' as' ss') /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss)) /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as' /\
               sym_terminal (sym_steps prog env n ss))
Proof
  cheat
QED
