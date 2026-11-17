(* Source-kind boundary for a forwarded-revert's prepared stack. *)
Theory symControlForwardStackOwn
Ancestors
  symControlTerminalSafetyOwn codegenSymRel codegenSymOwnRel asmSymBridge
  asmSymSem frameRel contextCodegenRel codegenRel venomInst stackPlanGen stackPlanTypes

Theorem sym_revert_operand_kind_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = REVERT /\ MEM op inst.inst_operands /\ ~is_label_operand op /\
  op_kind_ok fn ret op sv ==> ?w. sv = Val w
Proof
  strip_tac >>
  `op <> dead_stack_marker` by
    (strip_tac >> gvs[dead_stack_marker_def, is_label_operand_def]) >>
  drule ordinary_noncopy_operand_word_kind_mode >> simp[] >>
  disch_then irule >> conj_tac
  >- (qexists `allow_own` >> simp[]) >>
  qexistsl [`inst`, `op`, `ret`] >> simp[]
QED

Theorem sym_revert_source_stack_words_mode:
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  opaque_use_ok fn /\ (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
  inst.inst_opcode = REVERT /\ inst.inst_operands = [dop;zop] /\
  EVERY (\op. ~is_label_operand op) inst.inst_operands /\
  LIST_REL (op_kind_ok fn ret) (REVERSE (tail ++ [zop;dop])) top ==>
  ?d z ts. top = Val d :: Val z :: ts
Proof
  strip_tac >>
  gvs[listTheory.REVERSE_APPEND, listTheory.LIST_REL_CONS1] >>
  rename1 `op_kind_ok fn ret dop sd` >>
  rename1 `op_kind_ok fn ret zop szv` >>
  `(?w. sd = Val w) /\ (?w. szv = Val w)` by
    (conj_tac >> irule sym_revert_operand_kind_mode >> metis_tac[listTheory.MEM]) >>
  gvs[]
QED

Theorem sym_revert_stack_concretization_heads:
  LIST_REL (\sv w. sval_conc lo sv = SOME w)
    (Val d :: Val z :: xs) (dst :: sz :: ys) ==> d = dst /\ z = sz
Proof
  simp[sval_conc_def]
QED
