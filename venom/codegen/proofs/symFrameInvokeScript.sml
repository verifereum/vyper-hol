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
  symFrameInvokeSupport symFrameInvokePrefixOwn
  symInvokeEntryFacts symInvokeEntryOwn asmSymOwnStep
  symPostfixSim
  symFnSimSpec codegenSymRel fnFrameDeepInvoke asmSymBridge asmSymSem
  frameRel contextCodegenRel codegenRel unitShapeDefs stackPlanGen
  stackPlanTypes planExec asmSem venomExecSemantics venomState venomInst
  dfgDefs list symPlannerSim prefixExec mixedPrefixSim symShuffleSim gasFrameSim
  fnFrameStepsRevertForward

(* Canonical entry APIs are corollaries of the shared entry facts. *)
Theorem sym_invoke_argument_not_code_end:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  MEM (Var x) inst.inst_operands ==> ~code_end_var fn x
Proof
  metis_tac[sym_invoke_argument_not_code_end_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_argument_shape:
  fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: args ==>
  opaque_use_ok fn /\ EVERY (\op. ~is_label_operand op) args
Proof
  ACCEPT_TAC sym_invoke_argument_shape_core
QED

Theorem sym_invoke_argument_word_kind:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\ MEM op args /\
  op <> dead_stack_marker /\ op_kind_ok fn ret op sv ==>
  ?w. sv = Val w
Proof
  metis_tac[sym_invoke_argument_word_kind_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_output_not_code_end:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ MEM x inst.inst_outputs ==>
  ~code_end_var fn x
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_output_not_code_end
QED

Theorem sym_invoke_output_word_kind:
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ MEM x inst.inst_outputs ==>
  op_kind_ok fn ret (Var x) (Val w)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_output_word_kind
QED

Theorem sym_invoke_external_labels_preserved:
  !ctx cp caller callee m1 m0.
  fn_directly_calls ctx caller callee /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
       FLOOKUP m1 b = FLOOKUP m0 b) ==>
  !b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp caller b ==>
      FLOOKUP m1 b = FLOOKUP m0 b
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_external_labels_preserved
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_caller_spill_labels_preserved
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
  ACCEPT_TAC sym_invoke_selected_prefix_sim_marked_core
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
  ACCEPT_TAC sym_invoke_call_packet_core
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
  qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[sym_invoke_frame_own_canonical] >>
  `sym_steps_mode F p env cs.as_code n ss = SymOK ss'` by
    simp[sym_steps_mode_def] >>
  drule_all sym_invoke_prefix_pair_own >>
  simp[sym_invoke_frame_own_canonical]
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
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[sym_invoke_frame_own_canonical] >>
  drule_all sym_invoke_selected_frame_prefix_own >>
  simp[sym_steps_mode_def, sym_invoke_frame_own_canonical] >> metis_tac[]
QED

Theorem sval_conc_words:
  !svs ws lo.
  EVERY (\sv. ?w. sv = Val w) svs /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) svs ws ==>
  svs = MAP Val ws
Proof
  ACCEPT_TAC sval_conc_words_core
QED

Theorem sym_invoke_argument_list_words:
  fn_shape_ok fn /\ label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: args /\
  EVERY (\op. op <> dead_stack_marker) args /\
  LIST_REL (op_kind_ok fn ret) (REVERSE args) svs ==>
  EVERY (\sv. ?w. sv = Val w) svs
Proof
  metis_tac[sym_invoke_argument_list_words_own,
    codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
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
  rpt strip_tac >> irule sym_invoke_arranged_stack_core >>
  gvs[asm_sym_rel_def] >>
  metis_tac[codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok]
QED

Theorem sym_invoke_callee_code_label:
  !ctx cp i fn r p pc.
  generate_context_plan ctx = SOME cp /\ i < LENGTH ctx.ctx_functions /\
  EL i ctx.ctx_functions = fn /\ EL i cp.cp_regions = r /\
  fn_shape_ok fn /\
  asm_block_at p pc (execute_plan cp.cp_initial_fmp r.sr_plan) ==>
  MEM (AsmLabel fn.fn_name) p
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_callee_code_label
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
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`mid.as_code`, `env`] assume_tac) >>
  `asm_sym_rel_own (SND (compute_label_offsets p)) p env mid.as_code mid sms` by
    simp[asm_sym_rel_own_canonical] >>
  drule_all sym_invoke_call_entry_pair_own >>
  simp[sym_steps_mode_def, asm_sym_rel_own_canonical] >> metis_tac[]
QED

Theorem sym_invoke_return_code_label:
  !p pc fmp ret nm post.
  asm_block_at p pc (execute_plan fmp
    ([SOPushLabel ret; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret] ++ post)) ==>
  MEM (AsmLabel ret) p
Proof
  ACCEPT_TAC sym_invoke_return_code_label_core
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
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 arranged mid sms` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`mid.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env mid.as_code
     ctx cplan fn ret srest labs0 arranged mid sms` by
    simp[sym_invoke_frame_own_canonical] >>
  `sym_steps_mode F p env mid.as_code n ss = SymOK sms` by
    simp[sym_steps_mode_def] >>
  drule_all (REWRITE_RULE [boolTheory.COND_CLAUSES] (Q.SPEC `F` sym_invoke_entry_symbolic_boundary_own)) >>
  simp[sym_steps_mode_def, asm_sym_rel_own_canonical] >> metis_tac[]
QED

Theorem sym_invoke_return_output_kinds:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs ==>
  LIST_REL (op_kind_ok fn ret) (REVERSE (MAP Var inst.inst_outputs))
    (MAP Val (REVERSE vals))
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_output_kinds
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_spill_kinds
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_called_kinds
QED

Theorem sym_mstore_slot:
  ss.sym_stack = Val (n2w off) :: sv :: stk /\ off < dimword (:256) ==>
  ?ss'. sym_mstore ss = SymOK ss' /\ ss'.sym_stack = stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    mem_sval_at ss'.sym_mem_labels off sv /\
    (!b. ~in_mem_range off 32 b ==>
         FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_mstore_slot
QED

Theorem sym_mload_slot_label:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword (:256) /\
  mem_sval_at ss.sym_mem_labels off (Lab l d) ==>
  ?ss'. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Lab l d :: stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_mload_slot_label
QED

Theorem sym_mload_slot_word:
  ss.sym_stack = Val (n2w off) :: stk /\ off < dimword (:256) /\
  mem_sval_at ss.sym_mem_labels off (Val w) ==>
  ?ss' v. sym_mload ss = SymOK ss' /\ ss'.sym_stack = Val v :: stk /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + 1 /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_mload_slot_word
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_spill
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restore_label
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restore_word
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_spill_cons_compose
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_spills_cons
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_spills
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restore_kind
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restore_cons_compose
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restores_cons
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
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restores_kinds
QED

Theorem sym_scratch_restore_witnesses:
  LIST_REL (op_kind_ok fn ret) operands vals /\
  LIST_REL (mem_sval_at labs) offs vals /\
  EVERY (\i. i < LENGTH operands) indices ==>
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\ mem_sval_at labs off sv)
    (MAP (\i. EL i operands) indices) (MAP (\i. EL i offs) indices)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_restore_witnesses
QED

Theorem sym_scratch_post_spill:
  sym_steps p env n ss = SymOK mid /\
  mid.sym_stack = stk /\ mid.sym_base.as_pc = ss.sym_base.as_pc + n /\
  (!b. (!off. MEM off saved ==> ~in_mem_range off 32 b) ==>
    FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  LIST_REL (\op off. ?sv. op_kind_ok fn ret op sv /\
    mem_sval_at mid.sym_mem_labels off sv) operands offs /\
  EVERY (\off. off < dimword (:256)) offs /\
  asm_block_at p mid.sym_base.as_pc (execute_plan fmp (MAP SORestore offs)) ==>
  ?ss' top.
    sym_steps p env (n + LENGTH (execute_plan fmp (MAP SORestore offs))) ss = SymOK ss' /\
    ss'.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE operands) top /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      (n + LENGTH (execute_plan fmp (MAP SORestore offs))) /\
    (!b. (!off. MEM off saved ==> ~in_mem_range off 32 b) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_post_spill
QED

Theorem sym_scratch_schedule_kinds:
  !offs operands vals indices ss stk p fmp env.
  LIST_REL (op_kind_ok fn ret) operands vals /\ LENGTH vals = LENGTH offs /\
  ss.sym_stack = vals ++ stk /\
  EVERY (\off. off < dimword (:256)) offs /\ ALL_DISTINCT offs /\
  (!a b i. MEM a offs /\ MEM b offs /\ a <> b /\ in_mem_range a 32 i ==>
    ~in_mem_range b 32 i) /\
  EVERY (\i. i < LENGTH operands) indices /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan fmp (MAP SOSpill offs ++
      MAP SORestore (MAP (\i. EL i offs) indices))) ==>
  ?ss' top.
    sym_steps p env (LENGTH (execute_plan fmp (MAP SOSpill offs ++
      MAP SORestore (MAP (\i. EL i offs) indices)))) ss = SymOK ss' /\
    ss'.sym_stack = top ++ stk /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (MAP (\i. EL i operands) indices)) top /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan fmp (MAP SOSpill offs ++
        MAP SORestore (MAP (\i. EL i offs) indices))) /\
    (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_schedule_kinds
QED

Theorem sym_scratch_preserves_spilled_kind:
  (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
    FLOOKUP labs' b = FLOOKUP labs b) /\
  (!off b. MEM off offs /\ in_mem_range old 32 b ==> ~in_mem_range off 32 b) /\
  op_kind_ok fn ret op sv /\ mem_sval_at labs old sv ==>
  op_kind_ok fn ret op sv /\ mem_sval_at labs' old sv
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_preserves_spilled_kind
QED

Theorem sym_scratch_preserves_label_domain:
  !cplan labs labs' offs.
  (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
    FLOOKUP labs' b = FLOOKUP labs b) /\
  (!off b. MEM off offs /\ in_mem_range off 32 b ==> context_spill_byte cplan b) /\
  (!b. b IN FDOM labs ==> context_spill_byte cplan b) ==>
  (!b. b IN FDOM labs' ==> context_spill_byte cplan b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_preserves_label_domain
QED

Theorem sym_kinds_ok_scratch_finish:
  !cplan fn ret srest ps ss ps' ss' offs top.
  sym_kinds_ok cplan fn ret srest ps ss /\
  ps'.ps_spilled = ps.ps_spilled /\ ss'.sym_stack = top ++ srest /\
  LIST_REL (op_kind_ok fn ret) (REVERSE ps'.ps_stack) top /\
  (!b. (!off. MEM off offs ==> ~in_mem_range off 32 b) ==>
    FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
  (!op old off b. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offs /\
    in_mem_range old 32 b ==> ~in_mem_range off 32 b) /\
  (!off b. MEM off offs /\ in_mem_range off 32 b ==> context_spill_byte cplan b) ==>
  sym_kinds_ok cplan fn ret srest ps' ss'
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_kinds_ok_scratch_finish
QED

Theorem sym_scratch_schedule_framed:
  !base.
  sym_kinds_ok cplan fn ret srest ps ss /\
  ss.sym_stack = vals ++ (tail ++ srest) /\
  LIST_REL (op_kind_ok fn ret) operands vals /\
  LIST_REL (op_kind_ok fn ret) (REVERSE base) tail /\
  LENGTH vals = LENGTH offs /\
  ps'.ps_stack = base ++ MAP (\i. EL i operands) indices /\
  ps'.ps_spilled = ps.ps_spilled /\
  EVERY (\off. off < dimword (:256)) offs /\ ALL_DISTINCT offs /\
  (!a b i. MEM a offs /\ MEM b offs /\ a <> b /\ in_mem_range a 32 i ==>
    ~in_mem_range b 32 i) /\
  EVERY (\i. i < LENGTH operands) indices /\
  (!op old off b. FLOOKUP ps.ps_spilled op = SOME old /\ MEM off offs /\
    in_mem_range old 32 b ==> ~in_mem_range off 32 b) /\
  (!off b. MEM off offs /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  asm_block_at p ss.sym_base.as_pc
    (execute_plan fmp (MAP SOSpill offs ++
      MAP SORestore (MAP (\i. EL i offs) indices))) ==>
  ?ss'.
    sym_steps p env (LENGTH (execute_plan fmp (MAP SOSpill offs ++
      MAP SORestore (MAP (\i. EL i offs) indices)))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc +
      LENGTH (execute_plan fmp (MAP SOSpill offs ++
        MAP SORestore (MAP (\i. EL i offs) indices))) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_schedule_framed
QED

Theorem sym_scratch_ranges_separated:
  (a + 32 <= b \/ b + 32 <= a) /\ in_mem_range a 32 i ==>
  ~in_mem_range b 32 i
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_ranges_separated
QED

Theorem sym_scratch_numeric_layout:
  spill_alloc_layout_wf al sp /\ offs = FST (doSwapSim$spill_alloc_n [] al items) ==>
  LENGTH offs = LENGTH items /\ ALL_DISTINCT offs /\
  (!a b i. MEM a offs /\ MEM b offs /\ a <> b /\ in_mem_range a 32 i ==>
    ~in_mem_range b 32 i) /\
  (!op old off b. FLOOKUP sp op = SOME old /\ MEM off offs /\
    in_mem_range old 32 b ==> ~in_mem_range off 32 b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_scratch_numeric_layout
QED

Theorem sym_kinds_ok_stack_chunk:
  !cplan fn ret srest ps ss n.
  sym_kinds_ok cplan fn ret srest ps ss /\ n <= LENGTH ps.ps_stack ==>
  ?vals tail.
    ss.sym_stack = vals ++ (tail ++ srest) /\
    LENGTH vals = n /\
    LIST_REL (op_kind_ok fn ret) (REVERSE (stackPlanOps$top_n n ps.ps_stack)) vals /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (TAKE (LENGTH ps.ps_stack - n) ps.ps_stack)) tail
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_kinds_ok_stack_chunk
QED

Theorem sym_do_swap_small_prefix:
  !dist ps ops ps' initial_fmp lo.
  do_swap dist ps = (ops, ps') /\ dist <= 16 /\ dist < LENGTH ps.ps_stack ==>
  prefix_wf lo (LENGTH ps.ps_stack) ops /\
  prefix_spill_wf initial_fmp lo ops ps /\ EVERY is_prefix_op ops /\
  EVERY (\op. !l d. op <> SOPushOfst l d) ops /\
  (!off. ~MEM (SOSpill off) ops) /\
  apply_prefix_ops initial_fmp lo ops ps = ps'
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_do_swap_small_prefix
QED

Theorem sym_do_swap_small:
  !dist ps ops ps' cp fn ret srest ss p initial_fmp env.
  do_swap dist ps = (ops, ps') /\ dist <= 16 /\
  dist < LENGTH ps.ps_stack /\
  sym_kinds_ok cp fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cp fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    ss'.sym_mem_labels = ss.sym_mem_labels
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_do_swap_small
QED

Theorem sym_do_swap_big_numeric:
  !dist ps ops ps' cplan fn ret srest ss p initial_fmp env R.
  do_swap dist ps = (ops, ps') /\ dist > 16 /\
  dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_do_swap_big_numeric
QED

Theorem sym_do_swap_numeric:
  !dist ps ops ps' cplan fn ret srest ss p initial_fmp env R.
  do_swap dist ps = (ops, ps') /\ dist < LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan initial_fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan initial_fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_do_swap_numeric
QED

Theorem sym_swap_pop_numeric:
  do_swap dist ps = (swaps, swapped) /\ dist < LENGTH ps.ps_stack /\
  n <= LENGTH ps.ps_stack /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) swaps /\
  (!off b. MEM (SOSpill off) swaps /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (swaps ++ [SOPop n])) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp (swaps ++ [SOPop n]))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest
      (swapped with ps_stack := stack_pop n swapped.ps_stack) ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (swaps ++ [SOPop n])) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_swap_pop_numeric
QED

Theorem sym_pop_one_spill_bounds:
  pop_one_step item ps = (ops, ps') /\ plan_slots_bounded sb ps ==>
  plan_slots_bounded sb ps' /\ ops_spill_bounded sb ps'.ps_alloc.sa_next_offset ops
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_pop_one_spill_bounds
QED

Theorem sym_pop_steps_alloc_mono:
  !items ps ops ps'. plan_steps pop_one_step items ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_pop_steps_alloc_mono
QED

Theorem sym_pop_steps_spill_bounds:
  !items ps ops ps'.
  plan_steps pop_one_step items ps = (ops, ps') /\ plan_slots_bounded sb ps ==>
  plan_slots_bounded sb ps' /\ ops_spill_bounded sb ps'.ps_alloc.sa_next_offset ops
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_pop_steps_spill_bounds
QED

Theorem sym_popmany_spill_bounds:
  popmany_plan items ps = (ops, ps') /\ plan_slots_bounded sb ps ==>
  plan_slots_bounded sb ps' /\ ops_spill_bounded sb ps'.ps_alloc.sa_next_offset ops
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_popmany_spill_bounds
QED

Theorem sym_optimistic_spill_bounds:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') /\ plan_slots_bounded sb ps ==>
  plan_slots_bounded sb ps' /\ ops_spill_bounded sb ps'.ps_alloc.sa_next_offset ops
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_optimistic_spill_bounds
QED

Theorem sym_pop_one_numeric:
  pop_one_step item ps = (ops, ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_pop_one_numeric
QED

Theorem sym_pop_steps_numeric:
  !items ps ops ps' ss.
  plan_steps pop_one_step items ps = (ops, ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_pop_steps_numeric
QED

Theorem sym_popmany_contiguous_numeric:
  items <> [] /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) items) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) items)) /\
  popmany_plan items ps = (ops, ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_popmany_contiguous_numeric
QED

Theorem sym_popmany_numeric:
  popmany_plan items ps = (ops, ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_popmany_numeric
QED

Theorem sym_optimistic_swap_numeric:
  optimistic_swap_plan dfg inst live term ps = (ops, ps') /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  (!off b. MEM (SOSpill off) ops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp ops) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp ops) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_optimistic_swap_numeric
QED

Theorem sym_invoke_cleanup_pops_numeric:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) pops /\
  (!off b. MEM (SOSpill off) pops /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest called ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp pops) ==>
  ?mid. sym_steps p env (LENGTH (execute_plan fmp pops)) ss = SymOK mid /\
    sym_kinds_ok cplan fn ret srest popped mid /\
    mid.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp pops) /\
    (!b. ~R b ==> FLOOKUP mid.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) /\
    spill_alloc_layout_wf popped.ps_alloc popped.ps_spilled
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_pops_numeric
QED

Theorem sym_invoke_cleanup_opts_numeric:
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  spill_alloc_layout_wf popped.ps_alloc popped.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) opts /\
  (!off b. MEM (SOSpill off) opts /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest popped mid /\
  asm_block_at p mid.sym_base.as_pc (execute_plan fmp opts) ==>
  ?fin. sym_steps p env (LENGTH (execute_plan fmp opts)) mid = SymOK fin /\
    sym_kinds_ok cplan fn ret srest swapped fin /\
    fin.sym_base.as_pc = mid.sym_base.as_pc + LENGTH (execute_plan fmp opts) /\
    (!b. ~R b ==> FLOOKUP fin.sym_mem_labels b = FLOOKUP mid.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_opts_numeric
QED

Theorem sym_invoke_cleanup_kinds_numeric:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest called ss /\
  asm_block_at p ss.sym_base.as_pc (execute_plan fmp (pops ++ opts)) ==>
  ?ss'. sym_steps p env (LENGTH (execute_plan fmp (pops ++ opts))) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest final ss' /\
    ss'.sym_base.as_pc = ss.sym_base.as_pc + LENGTH (execute_plan fmp (pops ++ opts)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_kinds_numeric
QED

Theorem sym_invoke_cleanup_spill_bounds:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled ==>
  ops_spill_bounded called.ps_alloc.sa_spill_base final.ps_alloc.sa_next_offset (pops ++ opts)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_spill_bounds
QED

Theorem sym_invoke_cleanup_footprint:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  !off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    closure_spill_byte ctx cplan name b /\ context_spill_byte cplan b
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_footprint
QED

Theorem sym_invoke_cleanup_numeric:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  (!off b. MEM (SOSpill off) (pops ++ opts) /\ in_mem_range off 32 b ==>
    R b /\ context_spill_byte cplan b) /\
  sym_kinds_ok cplan fn ret srest called ss /\
  asm_static_wf p /\ asm_sym_rel p env cs ss /\
  context_venom_asm_rel cplan (SND (compute_label_offsets p)) called vs cs /\
  asm_block_at p cs.as_pc (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end ==>
  ?cs' ss'.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) cs = AsmOK cs' /\
    sym_steps p env (LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ss = SymOK ss' /\
    asm_sym_rel p env cs' ss' /\
    context_venom_asm_rel cplan (SND (compute_label_offsets p)) final vs cs' /\
    sym_kinds_ok cplan fn ret srest final ss' /\
    cs'.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts)) /\
    (!b. ~R b ==> FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_numeric
QED

Theorem sym_invoke_return_frame_transport:
  sym_frame_inv p env ctx cplan fn ret srest labs0 arranged mid sms /\
  fn_directly_calls ctx fn.fn_name callee /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan callee b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP sms.sym_mem_labels b) /\
  asm_sym_rel p env asr ssr /\ sym_kinds_ok cplan fn ret srest called ssr ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0 called asr ssr
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_transport
QED

Theorem sym_invoke_return_label_step:
  asm_block_at p ss.sym_base.as_pc [AsmLabel lbl] ==>
  sym_steps p env 1 ss =
    SymOK (ss with sym_base := ss.sym_base with
      <|as_stack := []; as_pc := ss.sym_base.as_pc + 1|>)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_label_step
QED

Theorem sym_invoke_return_label_pair:
  asm_static_wf p /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 called asr ssr /\
  asm_block_at p asr.as_pc [AsmLabel lbl] ==>
  ?cs ss.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 asr = AsmOK cs /\
    sym_steps p env 1 ssr = SymOK ss /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 called cs ss /\
    cs.as_pc = asr.as_pc + 1 /\ ss.sym_mem_labels = ssr.sym_mem_labels
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_label_pair
QED

Theorem sym_invoke_cleanup_frame_rebuild:
  sym_frame_inv p env ctx cplan fn ret srest labs0 old cs ss /\
  asm_sym_rel p env fin sfin /\ sym_kinds_ok cplan fn ret srest final sfin /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP sfin.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv p env ctx cplan fn ret srest labs0 final fin sfin
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_frame_rebuild
QED

(* Shared symbolic execution of the return label and numeric cleanup. *)
Theorem sym_invoke_return_suffix_kinds_mode:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cplan fn ret srest called ssr /\
  asm_block_at p ssr.sym_base.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) ==>
  ?sfin.
    sym_steps_mode allow_own p env own
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_kinds_ok cplan fn ret srest final sfin /\
    sfin.sym_base.as_pc = ssr.sym_base.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP sfin.sym_mem_labels b = FLOOKUP ssr.sym_mem_labels b)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_suffix_kinds_mode
QED

Theorem sym_invoke_return_suffix_frame:
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  asm_static_wf p /\
  sym_frame_inv p env ctx cplan fn ret srest labs0 called asr ssr /\
  asm_block_at p asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) ==>
  ?fin sfin.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
    sym_steps p env
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_frame_inv p env ctx cplan fn ret srest labs0 final fin sfin
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_suffix_frame
QED

Theorem sym_invoke_return_frame_numeric:
  ordered_spill_regions cplan.cp_regions /\ MEM r cplan.cp_regions /\
  r.sr_fn_name = fn.fn_name /\
  fn_directly_calls ctx fn.fn_name callee.fn_name /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 arranged vs mid /\
  arranged.ps_stack = stack_pop (LENGTH operands) arranged.ps_stack ++ operands /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\ LENGTH args = LENGTH operands /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T) outs)
    arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) outs) /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  fn_return_state_rel ctx cplan callee rvs mid asr /\
  asr.as_stack = REVERSE vals ++ saved ++ rest /\
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state vs rvs)) = SOME vs' /\
  ALL_DISTINCT outs /\ EVERY (\x. ~retpc_var fn x) outs /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
      outs) = (ret_lbl, called) /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts) /\
  asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  asm_static_wf prog /\
  sym_frame_inv prog env ctx cplan fn sret srest labs0 called asr ssr ==>
  ?fin sfin.
    asm_steps lo o2pc prog
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
    fin.as_pc = asr.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
    sym_steps prog env
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_frame_inv prog env ctx cplan fn sret srest labs0 final fin sfin
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_numeric
QED

(* The function contract specialized to a callee installed by INVOKE. *)
Theorem sym_invoke_callee_sim_own:
  !allow_own fuel ctx unit lo o2pc prog cp rpolicy j callee rj vs Inv cvs args cas cra
   crest cpc env own scas ret_lbl srest.
  sym_fn_sim_at_own allow_own fuel /\
  ctx = unit.cu_context /\
  code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\
  j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
  EL j cp.cp_regions = rj /\
  MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx callee cvs /\
  setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
  asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
  LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
  fn_entry_state_rel cp callee cvs cas cra crest /\
  FLOOKUP o2pc (w2n cra) = SOME cpc /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_data_env_lo_ok lo prog env own /\ vs.vs_code = own /\
  asm_sym_rel_own lo prog env own cas scas /\
  scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ srest /\
  MEM (AsmLabel ret_lbl) prog /\
  (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
  (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
     ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
       venom_asm_terminal_rel vs' as' /\
       sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
  (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
     ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
              (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
       venom_asm_terminal_rel vs' as' /\
       sym_terminal (sym_steps_mode allow_own prog env own n scas)) /\
  (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
     ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
       as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
       fn_return_state_rel ctx cp callee vs' cas as' /\
       sym_steps_mode allow_own prog env own n scas = SymOK ss' /\
       asm_sym_rel_own lo prog env own as' ss' /\
       ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
       (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
       (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_callee_sim_own
QED

Theorem sym_invoke_callee_sim:
  !fuel ctx unit lo o2pc prog cp rpolicy j callee rj vs Inv cvs args cas cra
   crest cpc env scas ret_lbl srest.
  sym_fn_sim_at fuel /\
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\
  j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
  EL j cp.cp_regions = rj /\
  MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  codegen_context_obligations Inv ctx cp /\ reachability_closed Inv ctx /\
  fn_entry_inv Inv ctx callee cvs /\
  setup_callee callee args vs = SOME cvs /\ fn_has_retpc callee /\
  asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
  LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
  fn_entry_state_rel cp callee cvs cas cra crest /\
  FLOOKUP o2pc (w2n cra) = SOME cpc /\
  label_flow_ok ctx /\ code_end_offset_ok Inv ctx /\
  sym_unit_static_ok unit /\ asm_static_wf prog /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  asm_sym_rel prog env cas scas /\
  scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ srest /\
  MEM (AsmLabel ret_lbl) prog /\
  (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) ==>
  (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
     ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
       venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
  (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
     ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
              (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
       venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
  (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
     ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
       as'.as_pc = cpc /\ as'.as_stack = REVERSE rv.iret_values ++ crest /\
       fn_return_state_rel ctx cp callee vs' cas as' /\
       sym_steps prog env n scas = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
       ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ srest /\
       (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
       (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_callee_sim
QED

(* Paired call-prefix composition keeps the witness chosen by the callee. *)
Theorem sym_invoke_halt_compose_mode:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps_mode allow_own prog env own k ss = SymOK scas /\
  asm_steps lo o2pc prog n cas = AsmHalt fin /\
  venom_asm_terminal_rel vs' fin /\
  sym_terminal (sym_steps_mode allow_own prog env own n scas) ==>
  ?m as'. asm_steps lo o2pc prog m cs = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_halt_compose_mode
QED

Theorem sym_invoke_abort_compose_mode:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps_mode allow_own prog env own k ss = SymOK scas /\
  ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert fin) \/
   (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault fin)) /\
  venom_asm_terminal_rel vs' fin /\
  sym_terminal (sym_steps_mode allow_own prog env own n scas) ==>
  ?m as'. ((a = Revert_abort /\ asm_steps lo o2pc prog m cs = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog m cs = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\
    sym_terminal (sym_steps_mode allow_own prog env own m ss)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_abort_compose_mode
QED

Theorem sym_invoke_ok_compose_own:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps_mode allow_own prog env own k ss = SymOK scas /\
  asm_steps lo o2pc prog n cas = AsmOK asr /\
  sym_steps_mode allow_own prog env own n scas = SymOK ssr /\
  asm_steps lo o2pc prog m asr = AsmOK fin /\
  sym_steps_mode allow_own prog env own m ssr = SymOK sfin /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
  sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 final fin sfin /\
  fin.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) ==>
  ?j as' ss'. asm_steps lo o2pc prog j cs = AsmOK as' /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    sym_steps_mode allow_own prog env own j ss = SymOK ss' /\
    sym_frame_inv_own lo prog env own ctx cplan fn ret srest labs0 final as' ss'
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_ok_compose_own
QED

Theorem sym_invoke_halt_compose:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps prog env k ss = SymOK scas /\
  asm_steps lo o2pc prog n cas = AsmHalt fin /\
  venom_asm_terminal_rel vs' fin /\ sym_terminal (sym_steps prog env n scas) ==>
  ?m as'. asm_steps lo o2pc prog m cs = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env m ss)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_halt_compose
QED

Theorem sym_invoke_abort_compose:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps prog env k ss = SymOK scas /\
  ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert fin) \/
   (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault fin)) /\
  venom_asm_terminal_rel vs' fin /\ sym_terminal (sym_steps prog env n scas) ==>
  ?m as'. ((a = Revert_abort /\ asm_steps lo o2pc prog m cs = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog m cs = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env m ss)
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_abort_compose
QED

Theorem sym_invoke_ok_compose:
  asm_steps lo o2pc prog k cs = AsmOK cas /\
  sym_steps prog env k ss = SymOK scas /\
  asm_steps lo o2pc prog n cas = AsmOK asr /\
  sym_steps prog env n scas = SymOK ssr /\
  asm_steps lo o2pc prog m asr = AsmOK fin /\
  sym_steps prog env m ssr = SymOK sfin /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 final fin sfin /\
  fin.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) ==>
  ?j as' ss'. asm_steps lo o2pc prog j cs = AsmOK as' /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = cs.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    sym_steps prog env j ss = SymOK ss' /\
    sym_frame_inv prog env ctx cplan fn ret srest labs0 final as' ss'
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_ok_compose
QED

(* Pair the concrete entry witnesses with the symbolic prefix and call. *)
Theorem sym_invoke_selected_entry_pair:
  !p env ctx cp fn ret srest labs0 ps cs ss mid nl iops prepared dfg rops
   arranged base r lo o2pc inst nm arg_ops args saved rest ret_lbl post cas.
  lo = SND (compute_label_offsets p) /\ o2pc = build_offset_to_pc p /\
  asm_static_wf p /\ fn_shape_ok fn /\ ssa_form fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  compute_operands inst = arg_ops /\
  EVERY (\op. ~is_label_operand op) arg_ops /\
  (!op. MEM op arg_ops /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan INVOKE arg_ops nl ps = (iops,prepared) /\
  reorder_plan dfg arg_ops prepared = (rops,arranged) /\
  LENGTH arg_ops <= 16 /\ LENGTH arg_ops <= LENGTH prepared.ps_stack /\
  generated_plan_state_wf_marked base ps /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) arg_ops /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  dfg = dfg_build_function fn /\
  MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 ps cs ss /\
  asm_block_at p cs.as_pc (execute_plan cp.cp_initial_fmp (iops ++ rops)) /\
  asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) cs = AsmOK mid /\
  arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
  mid.as_stack = REVERSE args ++ saved ++ rest /\ LENGTH args = LENGTH arg_ops /\
  asm_block_at p mid.as_pc (execute_plan cp.cp_initial_fmp
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
  MEM (AsmLabel nm) p /\ asm_steps lo o2pc p 3 mid = AsmOK cas ==>
  ?sms scas saved_sym.
    sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc p (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3)
      cs = AsmOK cas /\
    sym_steps p env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3)
      ss = SymOK scas /\
    asm_sym_rel p env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) p
Proof
  rpt strip_tac >> qpat_x_assum `lo = _` SUBST_ALL_TAC >>
  rename1 `sym_frame_inv p env ctx cplan fn ret srest labs0 ps cs ss` >>
  drule sym_invoke_canonical_lockstep >>
  disch_then (qspecl_then [`cs.as_code`, `env`] assume_tac) >>
  `sym_frame_inv_own (SND (compute_label_offsets p)) p env cs.as_code
     ctx cplan fn ret srest labs0 ps cs ss` by
    simp[sym_invoke_frame_own_canonical] >>
  drule_all (REWRITE_RULE [boolTheory.COND_CLAUSES] (Q.SPEC `F` sym_invoke_selected_entry_pair_own)) >>
  simp[sym_steps_mode_def, sym_invoke_frame_own_canonical,
       asm_sym_rel_own_canonical] >> metis_tac[]
QED

Theorem sym_invoke_selected_entry_facts:
  !unit ctx fn inst nm arg_ops ps nl iops prepared dfg rops arranged
   p pc fmp ops post.
  ctx = unit.cu_context /\ unit_shape_ok unit /\ MEM fn ctx.ctx_functions /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label nm :: arg_ops /\ codegen_ready_fn fn /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
     IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
  ops = iops ++ rops ++ post /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  asm_block_at p pc (execute_plan fmp ops) ==>
  compute_operands inst = arg_ops /\
  EVERY (\op. ~is_label_operand op) arg_ops /\ ssa_form fn /\
  (!op. MEM op arg_ops /\ is_var_operand op ==>
     MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  LENGTH arg_ops <= LENGTH prepared.ps_stack /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (iops ++ rops) /\
  asm_block_at p pc (execute_plan fmp (iops ++ rops))
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_selected_entry_facts
QED

(* Source invariants needed only on a successful internal return. *)
Theorem sym_invoke_return_source_facts:
  !Inv ctx cp fn inst nm arg_ops base ps nl iops prepared dfg rops arranged
   vs rvs rv vs'.
  codegen_context_obligations Inv ctx cp /\ codegen_ready_fn fn /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  generated_plan_state_wf_marked base ps /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
  reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
  LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <= LENGTH prepared.ps_stack /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  bind_outputs inst.inst_outputs rv.iret_values
    (adopt_return_fmp rv (merge_callee_state vs rvs)) = SOME vs' ==>
  ordered_spill_regions cp.cp_regions /\ ctx_wf ctx /\ ssa_form fn /\
  fn_directly_calls ctx fn.fn_name nm /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) arranged.ps_stack /\
  (!op. op IN FDOM arranged.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\x. ~retpc_var fn x) inst.inst_outputs /\
  LENGTH rv.iret_values = LENGTH inst.inst_outputs
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_source_facts
QED

(* The spill/stack argument is independent of the concrete relation. *)
Theorem sym_invoke_return_kinds_from_callee_core:
  !cp r fn ctx callee arranged ret srest sms scas ssr
   inst vals saved_ops saved_sym ret_lbl called.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\ fn_directly_calls ctx fn.fn_name callee /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_kinds_ok cp fn ret srest arranged sms /\
  scas.sym_mem_labels = sms.sym_mem_labels /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
  (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cp b) /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
  ssr.sym_stack = MAP Val (REVERSE vals) ++ (saved_sym ++ srest) /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := saved_ops) inst.inst_outputs) = (ret_lbl,called) ==>
  sym_kinds_ok cp fn ret srest called ssr
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_kinds_from_callee_core
QED

(* Rebuild the caller's symbolic frame at the callee's internal return. *)
Theorem sym_invoke_return_frame_from_callee:
  !cp r fn ctx callee arranged p env ret srest labs0 mid sms scas ssr asr
   inst vals saved_ops saved_sym ret_lbl called.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\ fn_directly_calls ctx fn.fn_name callee /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv p env ctx cp fn ret srest labs0 arranged mid sms /\
  scas.sym_mem_labels = sms.sym_mem_labels /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
  (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_sym_rel p env asr ssr /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
  ssr.sym_stack = MAP Val (REVERSE vals) ++ (saved_sym ++ srest) /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := saved_ops) inst.inst_outputs) = (ret_lbl,called) ==>
  sym_frame_inv p env ctx cp fn ret srest labs0 called asr ssr
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_from_callee
QED

(* Source-to-paired-entry boundary, retaining the concrete return witnesses. *)
Theorem sym_invoke_enter_callee_paired:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs
   rpolicy env ret srest labs0 ss.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc sms scas saved_sym.
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    sym_steps prog env (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    asm_sym_rel prog env cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog /\
    (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
    (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
      ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n cas = AsmRevert as') \/
        (a = ExHalt_abort /\ asm_steps lo o2pc prog n cas = AsmFault as')) /\
        venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n scas)) /\
    (!rv vs'. run_blocks fuel ctx callee cvs = IntRet rv vs' ==>
      ?n as' ss'. asm_steps lo o2pc prog n cas = AsmOK as' /\
        as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3 /\
        as'.as_stack = REVERSE rv.iret_values ++ (saved ++ rest) /\
        fn_return_state_rel ctx cp callee vs' cas as' /\
        sym_steps prog env n scas = SymOK ss' /\ asm_sym_rel prog env as' ss' /\
        ss'.sym_stack = MAP Val (REVERSE rv.iret_values) ++ (saved_sym ++ srest) /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
        (!b. b IN FDOM ss'.sym_mem_labels ==> context_spill_byte cp b))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameDeepInvokeTheory.invoke_enter_callee_marked >> strip_tac >>
  `ops = iops ++ rops ++
    ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)` by
    simp[APPEND_ASSOC] >>
  drule_all sym_invoke_selected_entry_facts >> strip_tac >>
  rename1 `generate_context_plan ctx = SOME cplan` >>
  `fn_shape_ok callee` by
    (gvs[unit_shape_ok_def, EVERY_MEM] >> metis_tac[MEM_EL]) >>
  `EL j cplan.cp_regions = EL j cplan.cp_regions` by simp[] >>
  drule_all sym_invoke_callee_code_label >> strip_tac >>
  `MEM (AsmLabel nm) prog` by metis_tac[] >>
  `emit_input_plan INVOKE arg_ops nl ps = (iops,prepared) /\
   reorder_plan dfg arg_ops prepared = (rops,arranged) /\
   LENGTH arg_ops <= 16 /\ LENGTH args = LENGTH arg_ops /\
   arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
   EVERY (\op. op <> dead_stack_marker /\
     !at. operand_equiv dfg op at ==> at <> dead_stack_marker) arg_ops` by
    metis_tac[] >>
  drule_all sym_invoke_selected_entry_pair >> strip_tac >>
  `scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  drule_all sym_invoke_callee_sim >> strip_tac >>
  qexistsl [`j`, `iops`, `prepared`, `rops`, `arranged`, `ret_lbl`, `ret_off`,
    `post`, `mid`, `saved`, `cas`, `pc`, `sms`, `scas`, `saved_sym`] >>
  simp[]
QED

(* Source-level halting outcome: select one paired call, then compose. *)
Theorem sym_invoke_source_halt:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Halt vs' ==>
  ?n as'. asm_steps lo o2pc prog n st = AsmHalt as' /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_halt >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!v. run_blocks _ _ _ _ = Halt v ==> _` drule >> strip_tac >>
  drule_all sym_invoke_halt_compose >> simp[]
QED

Theorem sym_invoke_source_abort:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss a vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = Abort a vs' ==>
  ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n st = AsmRevert as') \/
           (a = ExHalt_abort /\ asm_steps lo o2pc prog n st = AsmFault as')) /\
    venom_asm_terminal_rel vs' as' /\ sym_terminal (sym_steps prog env n ss)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_abort >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!a v. run_blocks _ _ _ _ = Abort a v ==> _` drule >>
  disch_then (qx_choose_then `n` (qx_choose_then `fin`
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all sym_invoke_abort_compose >> simp[]
QED

Theorem sym_invoke_source_ok:
  !fuel Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops rpolicy env ret srest labs0 ss vs'.
  ctx = unit.cu_context /\
  lo = SND (compute_label_offsets prog) /\ o2pc = build_offset_to_pc prog /\
  generate_context_plan ctx = SOME cp /\ codegen_assembly rpolicy unit = SOME prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
    inst.inst_outputs) ps.ps_stack /\
  (!op. op IN FDOM ps.ps_spilled ==>
    EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  asm_static_wf prog /\ code_end_offset_ok Inv ctx /\ sym_unit_static_ok unit /\
  (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\ sym_fn_sim_at fuel /\
  sym_frame_inv prog env ctx cp fn ret srest labs0 ps st ss /\
  step_inst fuel ctx inst vs = OK vs' ==>
  ?n as' ss'. asm_steps lo o2pc prog n st = AsmOK as' /\
    fn_frame_inv ctx cp lo fn ra rest mem0 final vs' as' /\
    as'.as_pc = st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    sym_steps prog env n ss = SymOK ss' /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 final as' ss'
Proof
  rpt gen_tac >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_source_ok >> strip_tac >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    sym_invoke_enter_callee_paired >>
  disch_then (drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_context_obligations _ _ _`)) >>
  disch_then (drule_at (Pat `codegen_assembly _ _ = _`)) >>
  disch_then (drule_at (Pat `setup_callee _ _ _ = _`)) >>
  disch_then (drule_at (Pat `generated_plan_state_wf_marked _ _`)) >>
  disch_then (drule_at (Pat `sym_fn_sim_at _`)) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!rv v. run_blocks _ _ _ _ = IntRet rv v ==> _` drule >> strip_tac >>
  drule_all fnFrameBoundaryInvokeTheory.invoke_plan_decompose >> strip_tac >>
  rename1 `codegen_context_obligations Inv ctx cplan` >>
  rename1 `asm_steps lo o2pc prog n cas = AsmOK asr` >>
  `fn_return_state_rel ctx cplan callee rvs mid asr` by
    (qpat_x_assum `fn_return_state_rel _ _ _ _ _ asr` mp_tac >>
     simp[fn_return_state_rel_def]) >>
  qpat_x_assum `ctx = _` kall_tac >>
  qpat_x_assum `lo = _` (fn loeq =>
    qpat_x_assum `o2pc = _` (fn pceq =>
      gvs[] >> assume_tac loeq >> assume_tac pceq)) >>
  rename1 `asm_sym_rel prog env asr ssr` >>
  drule_all sym_invoke_return_source_facts >> strip_tac >>
  `ssr.sym_stack = MAP Val (REVERSE ret'.iret_values) ++ (saved_sym ++ srest)` by
    simp[APPEND_ASSOC] >>
  `!b. context_spill_byte cplan b /\
       ~closure_spill_byte ctx cplan (EL j ctx.ctx_functions).fn_name b ==>
       FLOOKUP ssr.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b` by simp[] >>
  drule_at (Pat `fresh_label _ _ = _`) sym_invoke_return_frame_from_callee >>
  disch_then drule_all >> strip_tac >>
  `asm_block_at prog asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))` by
    (qpat_x_assum `asr.as_pc = _` SUBST1_TAC >>
     drule fnFrameBoundaryInvokeTheory.invoke_return_block >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) (pops ++ opts)` by
    simp[EVERY_APPEND] >>
  drule_at (Pat `sym_frame_inv _ _ _ _ _ _ _ _ called _ _`)
    (sym_invoke_return_frame_numeric
      |> Q.INST [`final` |-> `release_dead_spills nl swapped`]
      |> PURE_REWRITE_RULE [REFL_CLAUSE, AND_CLAUSES]) >>
  disch_then drule_all >> strip_tac >>
  `fin.as_pc = st.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp
    (iops ++ rops ++ [SOPushLabel ret_lbl;
      SOPushLabel (EL j ctx.ctx_functions).fn_name; SOEmit "JUMP";
      SOLabel ret_lbl] ++ pops ++ opts))` by
    (fs[execute_plan_def, exec_stack_op_def] >> decide_tac) >>
  drule_at (Pat `fin.as_pc = _`) sym_invoke_ok_compose >>
  disch_then drule_all >> metis_tac[arithmeticTheory.ADD_COMM]
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
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_ok >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_halt >> simp[]) >>
  rpt gen_tac >> strip_tac >> drule_all sym_invoke_source_abort >> simp[]
QED

(* Return restoration at supplied label offsets and fixed own-code bytes. *)
Theorem sym_invoke_return_frame_transport_own:
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 arranged mid sms /\
  fn_directly_calls ctx fn.fn_name callee /\
  (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan callee b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP sms.sym_mem_labels b) /\
  asm_sym_rel_own lo p env own asr ssr /\ sym_kinds_ok cplan fn ret srest called ssr ==>
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 called asr ssr
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_transport_own
QED

Theorem sym_invoke_cleanup_frame_rebuild_own:
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 old cs ss /\
  asm_sym_rel_own lo p env own fin sfin /\ sym_kinds_ok cplan fn ret srest final sfin /\
  (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
    FLOOKUP sfin.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b) ==>
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 final fin sfin
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_cleanup_frame_rebuild_own
QED

Theorem sym_invoke_return_frame_from_callee_own:
  !lo own cp r fn ctx callee arranged p env ret srest labs0 mid sms scas ssr asr
   inst vals saved_ops saved_sym ret_lbl called.
  ordered_spill_regions cp.cp_regions /\ MEM r cp.cp_regions /\
  r.sr_fn_name = fn.fn_name /\ fn_directly_calls ctx fn.fn_name callee /\
  ~TC (fn_directly_calls ctx) fn.fn_name fn.fn_name /\
  spill_alloc_layout_wf arranged.ps_alloc arranged.ps_spilled /\
  r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
  arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 arranged mid sms /\
  scas.sym_mem_labels = sms.sym_mem_labels /\
  (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp callee b ==>
    FLOOKUP ssr.sym_mem_labels b = FLOOKUP scas.sym_mem_labels b) /\
  (!b. b IN FDOM ssr.sym_mem_labels ==> context_spill_byte cp b) /\
  asm_sym_rel_own lo p env own asr ssr /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  LENGTH vals = LENGTH inst.inst_outputs /\
  LIST_REL (op_kind_ok fn ret) (REVERSE saved_ops) saved_sym /\
  ssr.sym_stack = MAP Val (REVERSE vals) ++ (saved_sym ++ srest) /\
  fresh_label "return_label"
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := saved_ops) inst.inst_outputs) = (ret_lbl,called) ==>
  sym_frame_inv_own lo p env own ctx cp fn ret srest labs0 called asr ssr
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_from_callee_own
QED

Theorem sym_invoke_return_label_pair_own:
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
     sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
     ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
       asm_sym_rel_own lo p env own cs' ss') /\
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 called asr ssr /\
  asm_block_at p asr.as_pc [AsmLabel lbl] ==>
  ?cs ss.
    asm_steps lo (build_offset_to_pc p) p 1 asr = AsmOK cs /\
    sym_steps_mode allow_own p env own 1 ssr = SymOK ss /\
    sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 called cs ss /\
    cs.as_pc = asr.as_pc + 1 /\ ss.sym_mem_labels = ssr.sym_mem_labels
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_label_pair_own
QED

Theorem sym_invoke_return_suffix_frame_own:
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
     sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
     ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
       asm_sym_rel_own lo p env own cs' ss') /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 called asr ssr /\
  asm_block_at p asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) ==>
  ?fin sfin.
    asm_steps lo (build_offset_to_pc p) p
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
    sym_steps_mode allow_own p env own
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 final fin sfin
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_suffix_frame_own
QED

(* The numeric supplier selects fin; the symbolic suffix reconstructs its
   matching frame without reproving the concrete return theorem. *)
Theorem sym_invoke_return_frame_numeric_own:
  (!n cs ss ss'. asm_sym_rel_own lo p env own cs ss /\
     sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
     ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\
       asm_sym_rel_own lo p env own cs' ss') /\
  (if outs = [] then ([],called)
   else if ~halting \/ LENGTH outs > 1 then
     popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) outs)) called
   else ([],called)) = (pops,popped) /\
  (if outs = [] \/ FILTER (\out. MEM out nl) outs = [] then ([],popped)
   else optimistic_swap_plan dfg inst nl term popped) = (opts,swapped) /\
  final = release_dead_spills nl swapped /\
  spill_alloc_layout_wf called.ps_alloc called.ps_spilled /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (pops ++ opts) /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 called asr ssr /\
  asm_block_at p asr.as_pc
    (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) /\
  asm_steps lo (build_offset_to_pc p) p
    (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) asr = AsmOK fin /\
  fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
  fin.as_pc = asr.as_pc +
    LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts))) ==>
  ?sfin.
    sym_steps_mode allow_own p env own
      (1 + LENGTH (execute_plan cplan.cp_initial_fmp (pops ++ opts))) ssr = SymOK sfin /\
    sym_frame_inv_own lo p env own ctx cplan fn ret srest labs0 final fin sfin /\
    fn_frame_inv ctx cplan lo fn ra rest mem0 final vs' fin /\
    fin.as_pc = asr.as_pc +
      LENGTH (execute_plan cplan.cp_initial_fmp (SOLabel ret_lbl :: (pops ++ opts)))
Proof
  ACCEPT_TAC symFrameInvokeSupportTheory.sym_invoke_return_frame_numeric_own
QED

Theorem sym_invoke_enter_callee_prefix_own:
  !allow_own own Inv unit cp prog ctx lo o2pc liveness dfg cfg fn inst nl halting term label
   base ps vs st ops final r ra rest mem0 nm arg_ops callee args cvs
   env ret srest labs0 ss.
  (!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
    sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
      asm_sym_rel_own lo prog env own cs' ss') /\
  ctx = unit.cu_context /\ o2pc = build_offset_to_pc prog /\
  unit_shape_ok unit /\ codegen_context_obligations Inv ctx cp /\
  reachability_closed Inv ctx /\ MEM fn ctx.ctx_functions /\
  MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
  Inv ctx fn inst vs /\ active_inst fn inst vs /\
  inst.inst_opcode = INVOKE /\ inst.inst_operands = Label nm :: arg_ops /\
  (!f inst callee_name args callee.
     MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
     MEM inst (fn_insts f) /\ inst.inst_opcode = INVOKE /\
     inst.inst_operands = Label callee_name :: args /\
     lookup_function callee_name ctx.ctx_functions = SOME callee ==>
     fn_has_retpc callee) /\
  (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
     ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
       FLOOKUP o2pc off = SOME pc /\
       asm_block_at prog pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
  opaque_use_ok fn /\ MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= final.ps_alloc.sa_spill_base /\
  final.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
  MEM inst (fn_insts fn) /\ LENGTH (compute_operands inst) <= 16 /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
    EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
    ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
      FLOOKUP o2pc off = SOME (st.as_pc + i)) /\
  (!op. MEM op (compute_operands inst) ==>
    eval_operand op (frame_view fn ra vs) = operand_val (frame_view fn ra vs) lo op) /\
  (!op at. MEM op (compute_operands inst) /\
    (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/ MEM at (compute_operands inst)) /\
    operand_equiv dfg op at ==>
    operand_val (frame_view fn ra vs) lo op = operand_val (frame_view fn ra vs) lo at) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword(:256)
    | SORestore off => off < dimword(:256) | _ => T) ops /\
  fn_frame_inv ctx cp lo fn ra rest mem0 ps vs st /\
  generate_inst_plan liveness dfg cfg fn inst nl halting term label ps = SOME (ops,final) /\
  asm_block_at prog st.as_pc (execute_plan cp.cp_initial_fmp ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops vs = SOME args /\ setup_callee callee args vs = SOME cvs /\
  dfg = dfg_build_function fn /\ fn_shape_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  generate_context_plan ctx = SOME cp /\
  sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps st ss ==>
  ?j iops prepared rops arranged ret_lbl ret_off post mid saved cas pc sms scas saved_sym.
    callee.fn_name = nm /\ compute_operands inst = arg_ops /\
    LENGTH args = LENGTH arg_ops /\
    j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
    MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
    fn_entry_inv Inv ctx callee cvs /\
    asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan) /\
    LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_has_retpc callee /\
    fn_entry_state_rel cp callee cvs cas (n2w ret_off) (saved ++ rest) /\
    FLOOKUP o2pc (w2n ((n2w ret_off):bytes32)) =
      SOME (st.as_pc + LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) /\
    emit_input_plan INVOKE (compute_operands inst) nl ps = (iops,prepared) /\
    reorder_plan dfg (compute_operands inst) prepared = (rops,arranged) /\
    ops = iops ++ rops ++
      [SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops))) st = AsmOK mid /\
    asm_block_at prog mid.as_pc (execute_plan cp.cp_initial_fmp
      ([SOPushLabel ret_lbl; SOPushLabel nm; SOEmit "JUMP"; SOLabel ret_lbl] ++ post)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 arranged vs mid /\
    plan_state_residual_wf_marked base (compute_operands inst)
      (LENGTH (compute_operands inst)) arranged /\
    arranged.ps_stack = stack_pop (LENGTH arg_ops) arranged.ps_stack ++ arg_ops /\
    mid.as_stack = REVERSE args ++ saved ++ rest /\
    LENGTH saved = LENGTH (stack_pop (LENGTH arg_ops) arranged.ps_stack) /\
    r.sr_spill_base <= arranged.ps_alloc.sa_spill_base /\
    arranged.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    asm_steps lo o2pc prog 3 mid = AsmOK cas /\
    cas = mid with <| as_stack := n2w ret_off :: mid.as_stack; as_pc := pc |> /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 arranged mid sms /\
    asm_steps lo o2pc prog (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) st = AsmOK cas /\
    sym_steps_mode allow_own prog env own (LENGTH (execute_plan cp.cp_initial_fmp (iops ++ rops)) + 3) ss = SymOK scas /\
    asm_sym_rel_own lo prog env own cas scas /\
    scas.sym_stack = [Lab ret_lbl 0] ++ MAP Val (REVERSE args) ++ saved_sym ++ srest /\
    LIST_REL (op_kind_ok fn ret)
      (REVERSE (stack_pop (LENGTH arg_ops) arranged.ps_stack)) saved_sym /\
    scas.sym_mem_labels = sms.sym_mem_labels /\
    (!b. b IN FDOM scas.sym_mem_labels ==> context_spill_byte cp b) /\
    MEM (AsmLabel ret_lbl) prog
Proof
  ACCEPT_TAC symFrameInvokePrefixOwnTheory.sym_invoke_enter_callee_prefix_own
QED
