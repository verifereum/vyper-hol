(* Own-code stack framing and initial-source emission adapters.
   Shared kernels and canonical APIs remain in symEmitSim. *)
Theory symEmitFrameOwn
Ancestors symEmitSim

Theorem asm_sym_rel_localize_stack_own:
  asm_sym_rel_own lo p env own cs ss /\ ss.sym_stack = top ++ stail /\
  cs.as_stack = ws ++ wtail /\ LENGTH top = LENGTH ws ==>
  asm_sym_rel_own lo p env own (cs with as_stack := ws)
    (ss with sym_stack := top) /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail
Proof
  rewrite_tac[GSYM asmSymBridgeTheory.asm_sym_rel_core_own] >>
  MATCH_ACCEPT_TAC asm_sym_rel_localize_stack_core
QED

Theorem asm_sym_rel_restore_stack_own:
  asm_sym_rel_own lo p env own cs ss /\
  LIST_REL (\sv w. sval_conc lo sv = SOME w) stail wtail ==>
  asm_sym_rel_own lo p env own (cs with as_stack := cs.as_stack ++ wtail)
    (ss with sym_stack := ss.sym_stack ++ stail)
Proof
  rewrite_tac[GSYM asmSymBridgeTheory.asm_sym_rel_core_own] >>
  MATCH_ACCEPT_TAC asm_sym_rel_restore_stack_core
QED

Theorem sym_initial_fmp_source_emit_mode_conditional:
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  R cs ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  inst.inst_opcode = INITIAL_FMP /\ inst.inst_outputs = [x] /\
  ssa_form fn /\ MEM inst (fn_insts fn) /\
  qs = ps with ps_stack := stack_push (Var x) ps.ps_stack /\
  asm_block_at p ss.sym_base.as_pc [AsmPush (encode_num_bytes initial_fmp)] /\
  asm_steps lo (build_offset_to_pc p) p 1 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n cs ss cs' ss'. R cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' /\
    asm_steps lo (build_offset_to_pc p) p n cs = AsmOK cs' ==> R cs' ss'` by
    (rpt strip_tac >> irule sym_emit_run_endpoint_mode_conditional >> metis_tac[]) >>
  drule_all (Q.INST [`slo` |-> `lo`] sym_initial_fmp_source_emit_core) >> simp[]
QED

Theorem sym_assert_source_emit_mode_conditional:
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  step_inst fuel ctx inst vs = OK vs' /\ opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  R cs ss /\ LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel lo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ inst.inst_operands /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) lo op) /\
  qs = ps with ps_stack := stack_pop 1 ps.ps_stack /\
  (inst.inst_opcode = ASSERT ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmOp "ISZERO"; AsmPushLabel "revert"; AsmOp "JUMPI"]) /\
  (inst.inst_opcode = ASSERT_UNREACHABLE ==>
    asm_block_at p ss.sym_base.as_pc
      [AsmPushLabel lbl; AsmOp "JUMPI"; AsmOp "INVALID"; AsmLabel lbl] /\
    INDEX_OF (AsmLabel lbl) p = SOME (ss.sym_base.as_pc + 3)) /\
  asm_steps slo (build_offset_to_pc p) p 3 cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 3 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!n cs ss cs' ss'. R cs ss /\
    sym_steps_mode allow_own p env own n ss = SymOK ss' /\
    asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' ==> R cs' ss'` by
    (rpt strip_tac >> irule sym_emit_run_endpoint_mode_conditional >> metis_tac[]) >>
  drule_all (Q.INST [`vlo` |-> `lo`] sym_assert_source_emit_endpoint_core) >> simp[]
QED
