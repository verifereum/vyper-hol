(* CODECOPY adapters. Shared kernels used by canonical corollaries stay
   in symEmitSim; this theory only supplies the subject replay interface. *)
Theory symEmitCodecopyOwn
Ancestors symEmitSim codegenSymRel asmSymBridge asmSymSem asmSem
  asmSplice strongPrefixSim symInstKinds list finite_map symEmitDataReplay

Theorem asm_sym_codecopy_values_core:
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
  eval_operands [dst; src; sz] vs = SOME (TAKE 3 cs.as_stack) ==>
  eval_operand dst vs = SOME dw /\ eval_operand sz vs = SOME nw /\
  IS_SOME (eval_operand src vs)
Proof
  strip_tac >>
  gvs[LIST_REL_CONS1, asmSymBridgeTheory.sval_conc_def,
      venomStateTheory.eval_operands_def, AllCaseEqs()]
QED

Theorem sym_codecopy_prepared_safe_mode:
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; sz] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  fn_shape_ok fn /\ MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel vlo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ [sz; src; dst] /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  sym_data_label p env "code_end" /\
  (MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label p env "runtime_begin") /\
  (!x w off. src = Var x /\ code_end_var fn x /\
    eval_operand src vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2) ==>
  ?dw sw nw tail. ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
    ((?l d. sw = Lab l d /\ sym_data_label p env l /\ sym_delta_ok d) \/
     (allow_own /\ ?w. sw = Val w)) /\
    (!b. b IN FDOM ss.sym_mem_labels ==>
      ~in_mem_range (w2n dw) (w2n nw) b)
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.sym_codecopy_prepared_safe_core
QED

Theorem sym_codecopy_data_replay_mode_conditional:
  (!cs ss. R cs ss ==> ss.sym_base.as_pc = cs.as_pc) /\
  (!n cs ss ss'. R cs ss /\ sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
    ?cs'. asm_steps slo (build_offset_to_pc p) p n cs = AsmOK cs' /\ R cs' ss') /\
  R cs ss /\ asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
  asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
  ss.sym_stack = Val dst :: Lab l d :: Val sz :: tail /\
  sym_data_label p env l /\ sym_delta_ok d /\
  (!b. b IN FDOM ss.sym_mem_labels ==>
    ~in_mem_range (w2n dst) (w2n sz) b) ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail
Proof
  strip_tac >>
  `ss.sym_base.as_pc = cs.as_pc` by metis_tac[] >>
  mp_tac (Q.SPECL [`allow_own`, `own`] sym_codecopy_data_replay_selected |>
    Q.INST [`lo` |-> `slo`]) >>
  simp[sym_step_codecopy_data_mode] >>
  impl_tac
  >- (rpt strip_tac >> drule_all sym_emit_run_endpoint_mode_conditional >> simp[]) >>
  simp[]
QED

Theorem sym_codecopy_source_emit_mode_conditional:
  (!cs ss. R cs ss ==>
    LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack) /\
  (!cs ss cs' dw l d nw tail. R cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Lab l d :: Val nw :: tail /\
    sym_data_label p env l /\ sym_delta_ok d /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  (!cs ss cs' dw sw nw tail. allow_own /\ R cs ss /\
    asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
    asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' /\
    ss.sym_stack = Val dw :: Val sw :: Val nw :: tail /\
    (!b. b IN FDOM ss.sym_mem_labels ==> ~in_mem_range (w2n dw) (w2n nw) b) ==>
    ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
      ss'.sym_mem_labels = ss.sym_mem_labels /\ ss'.sym_stack = tail) /\
  inst.inst_opcode = CODECOPY /\ inst.inst_operands = [dst; src; sz] /\
  opaque_use_ok fn /\
  (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\ fn_shape_ok fn /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  R cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  venom_asm_rel vlo ps (frame_view fn ra vs with vs_memory := m) cs /\
  ps.ps_stack = residual ++ [sz; src; dst] /\
  EVERY (\op. op <> dead_stack_marker) inst.inst_operands /\
  (!op. MEM op inst.inst_operands ==>
    eval_operand op (frame_view fn ra vs with vs_memory := m) =
    operand_val (frame_view fn ra vs with vs_memory := m) vlo op) /\
  context_source_memory_writes_disjoint cplan inst vs /\
  sym_data_label p env "code_end" /\
  (MEM (Label "runtime_begin") inst.inst_operands ==>
    sym_data_label p env "runtime_begin") /\
  (!x w off. src = Var x /\ code_end_var fn x /\
    eval_operand src vs = SOME w /\ FLOOKUP slo "code_end" = SOME off ==>
    w2n (w - n2w off) < dimword (:256) DIV 2) /\
  qs = ps with ps_stack := stack_pop 3 ps.ps_stack /\
  asm_block_at p cs.as_pc [AsmOp "CODECOPY"] /\
  asm_step slo (build_offset_to_pc p) (AsmOp "CODECOPY") cs = AsmOK cs' ==>
  ?ss'. sym_steps_mode allow_own p env own 1 ss = SymOK ss' /\ R cs' ss' /\
    ss'.sym_mem_labels = ss.sym_mem_labels /\
    sym_kinds_ok cplan fn ret srest qs ss'
Proof
  MATCH_ACCEPT_TAC symEmitSimTheory.sym_codecopy_source_emit_core
QED
