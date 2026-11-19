(* CODECOPY adapters. Shared kernels used by canonical corollaries stay
   in symEmitSim; this theory only supplies the subject replay interface. *)
Theory symEmitCodecopyOwn
Ancestors symEmitSim codegenSymRel asmSymBridge asmSymSem asmSem
  asmSplice strongPrefixSim symInstKinds list finite_map symEmitDataReplay
  symEmitCodecopyDecode

Theorem asm_sym_codecopy_values_core:
  LIST_REL (\sv w. sval_conc slo sv = SOME w) ss.sym_stack cs.as_stack /\
  ss.sym_stack = Val dw :: sw :: Val nw :: tail /\
  eval_operands [dst; src; sz] vs = SOME (TAKE 3 cs.as_stack) ==>
  eval_operand dst vs = SOME dw /\ eval_operand sz vs = SOME nw /\
  IS_SOME (eval_operand src vs)
Proof
  strip_tac >>
  drule_all asm_sym_codecopy_decode >> simp[]
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
