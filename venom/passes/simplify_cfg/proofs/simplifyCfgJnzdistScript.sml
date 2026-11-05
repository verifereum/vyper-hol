Theory simplifyCfgJnzdist
Ancestors
  simplifyCfgStruct simplifyCfgDefs venomWf venomInst

Theorem simplify_cfg_iter_with_labels_jnz_distinct:
  !n fn. wf_function fn /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f) ==>
  !inst. MEM inst (fn_insts (FST (simplify_cfg_iter_with_labels n fn))) /\
    inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels fn` >>
  rename1 `simplify_cfg_round_with_labels fn = (fn', lm)` >>
  `fn' = simplify_cfg_round fn` by simp[simplify_cfg_round_def] >>
  `wf_function fn'` by metis_tac[simplify_cfg_round_wf] >>
  `!inst. MEM inst (fn_insts fn') /\ inst.inst_opcode = JNZ ==>
    ?c t f. inst.inst_operands = [c; Label t; Label f] /\ t <> f` by
    metis_tac[simplify_cfg_round_jnz_distinct] >>
  qpat_x_assum `fn' = simplify_cfg_round fn` kall_tac >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  simp[] >>
  Cases_on `fn'.fn_blocks = fn.fn_blocks`
  >- simp[] >>
  simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n fn'` >>
  first_x_assum (qspec_then `fn'` mp_tac) >> simp[]
QED
