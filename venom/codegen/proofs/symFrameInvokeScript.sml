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
  dfgDefs list symPlannerSim

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

(* Label-free INVOKE preparation is precisely ADD preparation.  This is
   the same reduction used by invoke_selected_prefix_sim_marked. *)
Theorem sym_invoke_selected_prefix_sim_marked:
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cplan.cp_regions /\ r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp (iops ++ rops)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp (iops ++ rops))) ss =
          SymOK ss' /\
        sym_kinds_ok cplan fn ret srest arranged ss' /\
        ss'.sym_base.as_pc =
          ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp (iops ++ rops)) /\
        (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
             FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `emit_input_plan ADD operands nl ps = (iops,prepared)` by
    metis_tac[fnFrameBoundaryInvokeTheory.invoke_label_free_input] >>
  `ADD <> INVOKE /\ PERM operands operands` by simp[] >>
  drule_all sym_selected_prefix_sim_marked >> simp[]
QED

Theorem sym_invoke_call_packet:
  !p env ss ret_lbl nm pc.
  asm_block_at p ss.sym_base.as_pc
    [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  INDEX_OF (AsmLabel nm) p = SOME pc ==>
  sym_steps p env 3 ss =
    SymOK (ss with <| sym_base := ss.sym_base with as_pc := pc;
                     sym_stack := Lab ret_lbl 0 :: ss.sym_stack |> )
Proof
  rpt strip_tac >>
  gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_steps_compute, sym_step_def, sym_set_stack_def,
       sym_step_op_def, sym_jump_def, sym_jump_dest_def, asm_next_def]
QED

Theorem sym_invoke_prefix_frame_transport:
  !p env ctx cp fn ret srest labs0 ps cs ss ps' cs' ss' r.
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_sym_rel p env cs' ss' /\ sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rw[sym_frame_inv_def] >>
  `~(r.sr_spill_base <= b /\ b < r.sr_spill_end)` by
    (strip_tac >> gvs[closure_spill_byte_def, fcgDefsTheory.fcg_path_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  metis_tac[]
QED

Theorem sym_invoke_prefix_pair:
  !lo o2pc p env ctx cp fn ret srest labs0 ps cs ss r n cs' ss' ps'.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  asm_steps lo o2pc p n cs = AsmOK cs' /\
  sym_steps p env n ss = SymOK ss' /\
  sym_kinds_ok cp fn ret srest ps' ss' /\
  (!b. ~(r.sr_spill_base <= b /\ b < r.sr_spill_end) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 ps' cs' ss'
Proof
  rpt strip_tac >>
  `asm_sym_rel p env cs' ss'` by
    (gvs[sym_frame_inv_def] >> drule_all asm_sym_steps_lockstep >> simp[]) >>
  drule_all sym_invoke_prefix_frame_transport >> simp[]
QED

Theorem sym_invoke_selected_frame_prefix:
  !p env ctx cp fn ret srest labs0 ps cs ss mid operands nl iops prepared
   dfg rops arranged base r lo o2pc.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\
  EVERY (\op. ~is_label_operand op) operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE operands nl ps = (iops,prepared) /\
  reorder_plan dfg operands prepared = (rops,arranged) /\
  LENGTH operands <= 16 /\ LENGTH operands <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) operands /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= ps.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs =
    AsmOK mid ==>
  ?sms. sym_steps p env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) ss =
          SymOK sms /\
        sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms
Proof
  rpt strip_tac >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  rename1 `generated_plan_state_wf_marked spillbase ps` >>
  `sym_kinds_ok cplan fn ret srest ps ss /\
   asm_block_at p ss.sym_base.as_pc
     (execute_plan cplan.cp_initial_fmp (iops ++ rops))` by
    gvs[sym_frame_inv_def, asm_sym_rel_def] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   plan_slots_bounded spillbase ps /\ residual_budget_wf_marked spillbase [] ps` by
    metis_tac[fnPlanPrefixTheory.generated_plan_state_wf_marked_def,
              deepResidualSimTheory.generated_plan_state_wf_marked_residual_nil] >>
  drule_all sym_invoke_selected_prefix_sim_marked >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  drule_all sym_invoke_prefix_pair >> simp[]
QED

Theorem sval_conc_words:
  !svs ws lo.
  EVERY (\sv. ?w. sv = Val w) svs /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) svs ws ==>
  svs = MAP Val ws
Proof
  Induct >> Cases_on `ws` >> simp[] >>
  rpt strip_tac >> gvs[sval_conc_def] >> metis_tac[]
QED

Theorem sym_invoke_argument_list_words:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  LIST_REL (op_kind_ok fn ret) (REVERSE args) svs ==>
  EVERY (\sv. ?w. sv = Val w) svs
Proof
  rw[EVERY_MEM] >>
  drule_all LIST_REL_MEM_IMP_R >> strip_tac >>
  gvs[MEM_REVERSE] >>
  `x <> dead_stack_marker` by metis_tac[] >>
  drule_all sym_invoke_argument_word_kind >> simp[]
QED

Theorem sym_invoke_arranged_stack:
  !p env ctx cp fn ret srest ps cs ss inst nm args saved_ops values saved rest.
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_kinds_ok cp fn ret srest ps ss /\ asm_sym_rel p env cs ss /\
  ps.ps_stack = saved_ops ++ args /\
  cs.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args ==>
  ?saved_sym.
    ss.sym_stack = MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym
Proof
  rpt strip_tac >>
  gvs[sym_kinds_ok_def, REVERSE_APPEND, LIST_REL_SPLIT1] >>
  rename1 `LIST_REL (op_kind_ok fn ret) (REVERSE args) arg_syms` >>
  `EVERY (\sv. ?w. sv = Val w) arg_syms` by
    (drule_all sym_invoke_argument_list_words >> simp[]) >>
  `LENGTH arg_syms = LENGTH values` by
    metis_tac[LIST_REL_LENGTH, LENGTH_REVERSE] >>
  `LIST_REL (\sv w. sval_conc (SND (compute_label_offsets p)) sv = SOME w)
     arg_syms values` by
    metis_tac[asm_sym_rel_def, GSYM APPEND_ASSOC, LIST_REL_APPEND_EQ] >>
  drule_all sval_conc_words >> strip_tac >> gvs[]
QED

Theorem sym_invoke_callee_code_label:
  !ctx cp i fn r p pc.
  generate_context_plan ctx = SOME cp /\ i < LENGTH ctx.ctx_functions /\
  EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
  fn_shape_ok fn /\
  asm_block_at p pc (execute_plan cp.cp_initial_fmp r.sr_plan) ==>
  MEM (AsmLabel fn.fn_name) p
Proof
  rpt strip_tac >>
  drule_all fnPlanPlaceFnRegionTheory.context_region_leading_label >> strip_tac >>
  `fn.fn_name = (HD fn.fn_blocks).bb_label` by
    gvs[fn_shape_ok_def, fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
  irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >> simp[execute_plan_def, exec_stack_op_def]
QED

Theorem sym_invoke_call_entry_pair:
  !p env lo o2pc mid sms cas ret_lbl nm.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ asm_sym_rel p env mid sms /\
  asm_block_at p mid.as_pc
    [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"] /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?scas. sym_steps p env 3 sms = SymOK scas /\
    asm_sym_rel p env cas scas /\
    scas.sym_stack = Lab ret_lbl 0 :: sms.sym_stack /\
    scas.sym_mem_labels = sms.sym_mem_labels
Proof
  rpt strip_tac >>
  `?pc. INDEX_OF (AsmLabel nm) p = SOME pc` by
    (Cases_on `INDEX_OF (AsmLabel nm) p` >> gvs[INDEX_OF_eq_NONE]) >>
  `asm_block_at p sms.sym_base.as_pc
     [AsmPushLabel ret_lbl; AsmPushLabel nm; AsmOp "JUMP"]` by
    (gvs[asm_sym_rel_def] >> simp[]) >>
  drule_all sym_invoke_call_packet >>
  disch_then (qspec_then `env` assume_tac) >>
  drule_all asm_sym_steps_lockstep >> strip_tac >>
  gvs[]
QED

Theorem sym_invoke_return_code_label:
  !p pc fmp ret nm post.
  asm_block_at p pc (execute_plan fmp
    ([SOPushLabel ret; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret] ++ post)) ==>
  MEM (AsmLabel ret) p
Proof
  rpt strip_tac >> irule spillWordBoundsTheory.asm_block_at_member >>
  goal_assum (drule_at Any) >> simp[execute_plan_def, exec_stack_op_def]
QED

Theorem sym_invoke_entry_symbolic_boundary:
  !p env lo o2pc ctx cp fn ret srest labs0 arranged mid sms cas inst nm args
   saved_ops values saved rest ret_lbl fmp post n ss.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms /\
  arranged.ps_stack = saved_ops ++ args /\
  mid.as_stack = values ++ saved ++ rest /\ LENGTH values = LENGTH args /\
  asm_block_at p mid.as_pc (execute_plan fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas /\
  sym_steps p env n ss = SymOK sms ==>
  ?scas saved_sym.
    sym_steps p env (n + 3) ss = SymOK scas /\
    sym_steps p env 3 sms = SymOK scas /\ asm_sym_rel p env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val values ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt strip_tac >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 arranged mid sms` >>
  `asm_sym_rel p env mid sms /\ sym_kinds_ok cplan fn ret srest arranged sms` by
    gvs[sym_frame_inv_def] >>
  drule_all sym_invoke_arranged_stack >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_packet_block >> strip_tac >>
  drule_all sym_invoke_call_entry_pair >> strip_tac >>
  drule_all sym_invoke_return_code_label >> strip_tac >>
  gvs[sym_kinds_ok_def, sym_steps_add]
QED

Theorem sym_invoke_return_output_kinds:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP Var inst.inst_outputs))
    (MAP Val (REVERSE vals))
Proof
  strip_tac >>
  simp[GSYM MAP_REVERSE, LIST_REL_EL_EQN, EL_MAP] >>
  rpt strip_tac >> irule sym_invoke_output_word_kind >>
  simp[] >> qexists `inst` >> simp[GSYM MEM_REVERSE, EL_MEM]
QED

Theorem sym_invoke_return_spill_kinds:
  !ctx cp fn callee r ps ss ssr ret srest.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\
  fn_directly_calls ctx fn.fn_name callee /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  (!op off. FLOOKUP ps.ps_spilled op = SOME off ==>
     r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) /\
  sym_kinds_ok cp fn ret srest ps ss /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
       FLOOKUP ssr.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  !op off. FLOOKUP ps.ps_spilled op = SOME off ==>
    ?sv. op_kind_ok fn ret op sv /\ mem_sval_at ssr.sym_mem_labels off sv
Proof
  rpt strip_tac >>
  rename1 `sym_kinds_ok cplan fn ret srest ps ss` >>
  `!b. in_mem_range off 32 b ==>
       FLOOKUP ssr.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b` by
    metis_tac[sym_invoke_caller_spill_labels_preserved] >>
  drule mem_sval_at_range_cong >>
  gvs[sym_kinds_ok_def] >> metis_tac[]
QED

Theorem sym_invoke_return_called_kinds:
  !cp fn ret srest arranged ssr saved_ops saved_sym inst vals called ret_lbl.
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
  ssr.sym_stack = MAP Val (REVERSE vals) ++ saved_sym ++ srest /\
  (!op off. FLOOKUP arranged.ps_spilled op = SOME off ==>
    ?sv. op_kind_ok fn ret op sv /\ mem_sval_at ssr.sym_mem_labels off sv) /\
  (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cp b) /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := saved_ops) inst.inst_outputs) = (ret_lbl, called) ==>
  sym_kinds_ok cp fn ret srest called ssr
Proof
  rpt strip_tac >>
  drule fnFrameBoundaryInvokeTheory.invoke_called_plan_fields >> strip_tac >>
  drule_all sym_invoke_return_output_kinds >>
  rw[sym_kinds_ok_def, REVERSE_APPEND] >> metis_tac[LIST_REL_APPEND]
QED

Theorem mem_sval_at_store_label:
  mem_sval_at (labs |++ GENLIST (\i. (off + i, (l,d,i))) 32) off (Lab l d)
Proof
  simp[mem_sval_at_def, mem_label_at_def, mstore_labels_lookup,
       EVERY_MEM, rich_listTheory.MEM_COUNT_LIST]
QED

Theorem mem_labels_clear_lookup:
  FLOOKUP (mem_labels_clear labs P) b = if P b then NONE else FLOOKUP labs b
Proof
  Cases_on `P b` >> simp[mem_labels_clear_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem mem_sval_at_store_word:
  mem_sval_at (mem_labels_clear labs (in_mem_range off 32)) off (Val w)
Proof
  simp[mem_sval_at_def, mem_labels_clear_def, finite_mapTheory.FDOM_DRESTRICT]
QED

Theorem sym_mstore_slot:
  ss.sym_stack = Val (n2w off) :: sv :: stk /\ off < dimword (:256) ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    mem_sval_at ss'.sym_mem_labels off sv /\
    (!b. ~in_mem_range off 32 b ==>
         FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> Cases_on `sv` >>
  simp[sym_mstore_def, sym_step_concrete_def, asm_op_arity_def,
       sval_val_def, sym_lift_def, asmOpSimTheory.asm_step_op_mstore, asm_mstore_def,
       asm_op_arity_table_def, log_table_def,
       asm_next_def, asm_op_mem_reads_def, asm_op_mem_writes_def,
       mem_labels_hit_def, Excl "GENLIST_NUMERALS", mem_sval_at_store_label,
       mem_sval_at_store_word, mem_labels_clear_lookup, mstore_labels_lookup,
       in_mem_range_def] >>
  pure_once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  simp[mem_sval_at_store_label, mstore_labels_lookup, Excl "GENLIST_NUMERALS"]
QED

Theorem mem_sval_at_word_no_label:
  mem_sval_at labs off (Val w) ==> mem_label_at labs off = NONE
Proof
  rw[mem_sval_at_def] >>
  `off NOTIN FDOM labs` by gvs[in_mem_range_def] >>
  simp[mem_label_at_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem sym_mload_slot_label:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword (:256) /\
  mem_sval_at ss.sym_mem_labels off (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Lab l d :: stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  simp[mem_sval_at_def, sym_mload_def, asm_next_def]
QED

Theorem sym_mload_slot_word:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword (:256) /\
  mem_sval_at ss.sym_mem_labels off (Val w) ==>
  ?ss' v. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val v :: stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> drule mem_sval_at_word_no_label >> strip_tac >>
  simp[sym_mload_def, sym_step_concrete_def, asm_op_arity_def,
       asm_op_arity_table_def, sval_val_def, sym_lift_def,
       asmOpSimTheory.asm_step_op_mload, asm_mload_def, asm_next_def,
       asm_op_mem_reads_def, asm_op_mem_writes_def, mem_labels_hit_def,
       mem_labels_clear_def, finite_mapTheory.DRESTRICT_UNIV] >>
  gvs[mem_sval_at_def] >>
  `~?i. i IN FDOM ss.sym_mem_labels /\ in_mem_range off 32 i` by metis_tac[] >>
  simp[] >> simp[finite_mapTheory.fmap_eq_flookup,
                  finite_mapTheory.FLOOKUP_DRESTRICT]
QED

Theorem sym_scratch_push:
  off < dimword (:256) ==>
  sym_step p env (AsmPush (encode_num_bytes off)) ss =
  SymOK (ss with <| sym_base := asm_next (ss.sym_base with as_stack := []);
                   sym_stack := Val (n2w off) :: ss.sym_stack |>)
Proof
  strip_tac >>
  `word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes off)) = n2w off` by
    (mp_tac (Q.SPEC `n2w off` (GEN_ALL strongPrefixSimTheory.push_encode_roundtrip)) >> simp[]) >>
  simp[sym_step_def, stackOpAsmSimTheory.asm_step_push_ok, sym_lift_def,
       asm_next_def, sym_state_component_equality]
QED

Theorem sym_scratch_spill:
  asm_block_at p ss.sym_base.as_pc
    [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] /\
  ss.sym_stack = sv :: stk /\ off < dimword (:256) ==>
  ?ss'. sym_steps p env 2 ss = SymOK ss' /\ ss'.sym_stack = stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    mem_sval_at ss'.sym_mem_labels off sv /\
    (!b. ~in_mem_range off 32 b ==>
         FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_steps_compute, sym_scratch_push, asm_next_def] >>
  simp[sym_step_def, sym_step_op_def] >>
  qmatch_goalsub_abbrev_tac `sym_mstore mid` >>
  `?ss'. sym_mstore mid = SymOK ss' /\ ss'.sym_stack = stk /\
     ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
     mem_sval_at ss'.sym_mem_labels off sv /\
     (!b. ~in_mem_range off 32 b ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)` by
    (mp_tac (Q.INST [`ss` |-> `mid`] sym_mstore_slot) >>
     simp[Abbr `mid`]) >>
  gvs[]
QED

Theorem sym_scratch_restore_label:
  asm_block_at p ss.sym_base.as_pc
    [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] /\
  off < dimword (:256) /\ mem_sval_at ss.sym_mem_labels off (Lab l d) ==>
  ?ss'. sym_steps p env 2 ss = SymOK ss' /\
    ss'.sym_stack = Lab l d :: ss.sym_stack /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_steps_compute, sym_scratch_push, asm_next_def] >>
  simp[sym_step_def, sym_step_op_def] >>
  qmatch_goalsub_abbrev_tac `sym_mload mid` >>
  mp_tac (Q.INST [`ss` |-> `mid`, `stk` |-> `ss.sym_stack`]
                 sym_mload_slot_label) >>
  simp[Abbr `mid`] >> strip_tac >> gvs[]
QED

Theorem sym_scratch_restore_word:
  asm_block_at p ss.sym_base.as_pc
    [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] /\
  off < dimword (:256) /\ mem_sval_at ss.sym_mem_labels off (Val w) ==>
  ?ss' v. sym_steps p env 2 ss = SymOK ss' /\
    ss'.sym_stack = Val v :: ss.sym_stack /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> gvs[stackOpSimTheory.asm_block_at_cons] >>
  simp[sym_steps_compute, sym_scratch_push, asm_next_def] >>
  simp[sym_step_def, sym_step_op_def] >>
  qmatch_goalsub_abbrev_tac `sym_mload mid` >>
  mp_tac (Q.INST [`ss` |-> `mid`, `stk` |-> `ss.sym_stack`]
                 sym_mload_slot_word) >>
  simp[Abbr `mid`] >> strip_tac >> gvs[]
QED

Theorem sym_scratch_spill_cons_compose:
  sym_steps p env 2 ss = SymOK mid /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  mem_sval_at mid.sym_mem_labels off sv /\
  (!b. ~in_mem_range off 32 b ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  sym_steps p env n mid = SymOK last /\ last.sym_stack = stk /\
  last.sym_base.as_pc = mid.sym_base.as_pc + n /\
  LIST_REL (mem_sval_at last.sym_mem_labels) offs vals /\
  (!b. (!a. MEM a offs ==> ~in_mem_range a 32 b) ==>
    FLOOKUP last.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b) /\
  (!a b. MEM a offs /\ in_mem_range off 32 b ==> ~in_mem_range a 32 b) ==>
  sym_steps p env (n + 2) ss = SymOK last /\ last.sym_stack = stk /\
  last.sym_base.as_pc = ss.sym_base.as_pc + (n + 2) /\
  LIST_REL (mem_sval_at last.sym_mem_labels) (off :: offs) (sv :: vals) /\
  (!b. (!a. MEM a (off :: offs) ==> ~in_mem_range a 32 b) ==>
    FLOOKUP last.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `!b. in_mem_range off 32 b ==>
    FLOOKUP last.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b` by metis_tac[] >>
  `mem_sval_at last.sym_mem_labels off sv` by metis_tac[mem_sval_at_range_cong] >>
  reverse conj_tac >- (simp[] >> metis_tac[]) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[sym_steps_add]
QED

Theorem sym_scratch_spills_cons:
  (!vals ss stk.
    LENGTH vals = LENGTH offs /\ ss.sym_stack = vals ++ stk /\
    EVERY (\off. off < dimword (:256)) offs /\ ALL_DISTINCT offs /\
    (!a b i. MEM a offs /\ MEM b offs /\ a <> b /\ in_mem_range a 32 i ==>
      ~in_mem_range b 32 i) /\
    asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill offs)) ==>
    ?ss'. sym_steps p env (LENGTH (execute_plan fmp (MAP SOSpill offs))) ss = SymOK ss' /\
      ss'.sym_stack = stk /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SOSpill offs)) /\
      LIST_REL (mem_sval_at ss'.sym_mem_labels) offs vals /\
      (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
        FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)) ==>
  !vals ss stk.
  LENGTH vals = LENGTH (h :: offs) /\ ss.sym_stack = vals ++ stk /\
  EVERY (\off. off < dimword (:256)) (h :: offs) /\ ALL_DISTINCT (h :: offs) /\
  (!a b i. MEM a (h :: offs) /\ MEM b (h :: offs) /\ a <> b /\ in_mem_range a 32 i ==>
    ~in_mem_range b 32 i) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill (h :: offs))) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp (MAP SOSpill (h :: offs)))) ss = SymOK ss' /\
    ss'.sym_stack = stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SOSpill (h :: offs))) /\
    LIST_REL (mem_sval_at ss'.sym_mem_labels) (h :: offs) vals /\
    (!b. (!off. MEM off (h :: offs) ==> ~in_mem_range off 32 b) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  disch_tac >> rpt gen_tac >> Cases_on `vals` >> simp[] >> strip_tac >>
  rename1 `ss.sym_stack = v :: (vs ++ stk)` >>
  `execute_plan fmp (SOSpill h :: MAP SOSpill offs) =
     [AsmPush (encode_num_bytes h); AsmOp "MSTORE"] ++
     execute_plan fmp (MAP SOSpill offs)` by
    simp[execute_plan_def, exec_stack_op_def] >>
  qpat_x_assum `execute_plan _ (SOSpill _ :: _) = _` (fn th =>
    (rewrite_tac[th] >> rule_assum_tac (REWRITE_RULE [th]))) >>
  qpat_x_assum `asm_block_at _ _ (_ ++ _)` mp_tac >>
  simp[stackOpSimTheory.asm_block_at_append] >> strip_tac >>
  drule_all sym_scratch_spill >> disch_then (qspec_then `env` strip_assume_tac) >>
  first_x_assum (qspecl_then [`vs`, `ss'`, `stk`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >> qexists_tac `ss''` >>
  `!a b. MEM a offs /\ in_mem_range h 32 b ==> ~in_mem_range a 32 b` by metis_tac[] >>
  drule_all sym_scratch_spill_cons_compose >> simp[]
QED

Theorem sym_scratch_spills:
  !offs vals ss stk.
  LENGTH vals = LENGTH offs /\ ss.sym_stack = vals ++ stk /\
  EVERY (\off. off < dimword (:256)) offs /\ ALL_DISTINCT offs /\
  (!a b i. MEM a offs /\ MEM b offs /\ a <> b /\ in_mem_range a 32 i ==>
           ~in_mem_range b 32 i) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SOSpill offs)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp (MAP SOSpill offs))) ss = SymOK ss' /\
    ss'.sym_stack = stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SOSpill offs)) /\
    LIST_REL (mem_sval_at ss'.sym_mem_labels) offs vals /\
    (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
       FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  Induct >- simp[execute_plan_def, sym_steps_def] >>
  drule sym_scratch_spills_cons >> simp[]
QED

Theorem op_kind_ok_word_replace:
  op_kind_ok fn ret op (Val w) ==> op_kind_ok fn ret op (Val v)
Proof
  Cases_on `op` >> simp[op_kind_ok_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem sym_scratch_restore_kind:
  asm_block_at p ss.sym_base.as_pc
    [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] /\
  off < dimword (:256) /\ op_kind_ok fn ret op sv /\
  mem_sval_at ss.sym_mem_labels off sv ==>
  ?ss' v. sym_steps p env 2 ss = SymOK ss' /\
    ss'.sym_stack = v :: ss.sym_stack /\ op_kind_ok fn ret op v /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  Cases_on `sv` >> strip_tac
  >- (drule_all sym_scratch_restore_word >>
      disch_then (qspec_then `env` strip_assume_tac) >>
      metis_tac[op_kind_ok_word_replace]) >>
  drule_all sym_scratch_restore_label >>
  disch_then (qspec_then `env` strip_assume_tac) >> metis_tac[]
QED

Theorem sym_scratch_restore_cons_compose:
  sym_steps p env 2 ss = SymOK mid /\
  mid.sym_stack = v :: stk /\ op_kind_ok fn ret op v /\
  mid.sym_base.as_pc = ss.sym_base.as_pc + 2 /\
  mid.sym_mem_labels = ss.sym_mem_labels /\
  sym_steps p env n mid = SymOK last /\ last.sym_stack = top ++ (v :: stk) /\
  LIST_REL (op_kind_ok fn ret) (REVERSE operands) top /\
  last.sym_base.as_pc = mid.sym_base.as_pc + n /\
  last.sym_mem_labels = mid.sym_mem_labels ==>
  sym_steps p env (n + 2) ss = SymOK last /\
  last.sym_stack = (top ++ [v]) ++ stk /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (op :: operands)) (top ++ [v]) /\
  last.sym_base.as_pc = ss.sym_base.as_pc + (n + 2) /\
  last.sym_mem_labels = ss.sym_mem_labels
Proof
  strip_tac >> reverse conj_tac >- simp[LIST_REL_APPEND_suff] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> simp[sym_steps_add]
QED

Theorem sym_scratch_restores_cons:
  (!operands ss stk.
    LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\
      mem_sval_at ss.sym_mem_labels off sv) operands offs /\
    ss.sym_stack = stk /\ EVERY (\off. off < dimword (:256)) offs /\
    asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SORestore offs)) ==>
    ?ss' top. sym_steps p env (LENGTH (execute_plan fmp (MAP SORestore offs))) ss = SymOK ss' /\
      ss'.sym_stack = top ++ stk /\
      LIST_REL (op_kind_ok fn ret) (REVERSE operands) top /\
      ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SORestore offs)) /\
      ss'.sym_mem_labels = ss.sym_mem_labels) ==>
  !operands ss stk.
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\
    mem_sval_at ss.sym_mem_labels off sv) operands (h :: offs) /\
  ss.sym_stack = stk /\ EVERY (\off. off < dimword (:256)) (h :: offs) /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SORestore (h :: offs))) ==>
  ?ss' top. sym_steps p env (LENGTH (execute_plan fmp (MAP SORestore (h :: offs)))) ss = SymOK ss' /\
    ss'.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE operands) top /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SORestore (h :: offs))) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  disch_tac >> rpt gen_tac >> Cases_on `operands` >> simp[] >> strip_tac >>
  rename1 `op_kind_ok fn ret op sv` >>
  `execute_plan fmp (SORestore h :: MAP SORestore offs) =
     [AsmPush (encode_num_bytes h); AsmOp "MLOAD"] ++
     execute_plan fmp (MAP SORestore offs)` by
    simp[execute_plan_def, exec_stack_op_def] >>
  qpat_x_assum `execute_plan _ (SORestore _ :: _) = _` (fn th =>
    (rewrite_tac[th] >> rule_assum_tac (REWRITE_RULE [th]))) >>
  qpat_x_assum `asm_block_at _ _ (_ ++ _)` mp_tac >>
  simp[stackOpSimTheory.asm_block_at_append] >> strip_tac >>
  drule_all sym_scratch_restore_kind >>
  disch_then (qspec_then `env` strip_assume_tac) >>
  first_x_assum (qspecl_then [`t`, `ss'`, `v :: stk`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`ss''`, `top ++ [v]`] >>
  `ss'.sym_stack = v :: stk` by simp[] >>
  drule_all sym_scratch_restore_cons_compose >> simp[]
QED

Theorem sym_scratch_restores_kinds:
  !offs operands ss stk.
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\
       mem_sval_at ss.sym_mem_labels off sv) operands offs /\
  ss.sym_stack = stk /\ EVERY (\off. off < dimword (:256)) offs /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (MAP SORestore offs)) ==>
  ?ss' top.
    sym_steps p env (LENGTH (execute_plan fmp (MAP SORestore offs))) ss = SymOK ss' /\
    ss'.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE operands) top /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (MAP SORestore offs)) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  Induct
  >- (rpt gen_tac >> Cases_on `operands` >> simp[execute_plan_def, sym_steps_def]) >>
  drule sym_scratch_restores_cons >> simp[]
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
