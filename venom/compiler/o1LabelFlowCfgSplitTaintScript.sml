Theory o1LabelFlowCfgSplitTaint
Ancestors
  o1LabelFlowLateCfgNorm symFrameBoundary cfgNormBase cfgNormDefs
  cfgNormSupplySim codegenSymRel venomInst unitShapeDefs list pair

(* Export operand provenance directly: the existing PHI-pair witness is local
   to cfgNormBase, whereas clients need the actual operand membership. *)
Theorem cfg_forward_source_phi_operand:
  !insts lbl pred v.
  MEM v (phi_vars_needing_forward lbl pred insts) ==>
  ?i. MEM i insts /\ i.inst_opcode = PHI /\ MEM (Var v) i.inst_operands
Proof
  Induct_on `insts` >> rpt gen_tac >>
  simp[Once phi_vars_needing_forward_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[MEM_MAP, MEM_FILTER, EXISTS_PROD] >>
  metis_tac[phi_pairs_mem_var]
QED

Theorem cfg_split_replacement_source:
  build_split_block_supply s pred target = (split,repls,t) /\
  MEM (v,w) repls ==>
  MEM v (phi_vars_needing_forward pred.bb_label pred target.bb_instructions)
Proof
  Cases_on `fresh_ir_label s` >>
  Cases_on `build_forwarding_assigns_supply r
    (nub (phi_vars_needing_forward pred.bb_label pred target.bb_instructions))` >>
  rename1 `build_forwarding_assigns_supply _ _ = (rs,tail)` >>
  PairCases_on `tail` >>
  Cases_on `fresh_inst_id tail1` >>
  simp[build_split_block_supply_def] >> strip_tac >> gvs[] >>
  drule supply_forward_replacement_sources >>
  strip_tac >>
  `MEM v (MAP FST repls)` by (simp[MEM_MAP] >> metis_tac[FST]) >>
  gvs[]
QED

Theorem cfg_split_forward_source_not_code_end:
  build_split_block_supply s pred target = (split,repls,t) /\
  MEM target fn.fn_blocks /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM (v,w) repls ==>
  ~code_end_var fn v
Proof
  strip_tac >> drule_all cfg_split_replacement_source >>
  disch_then (strip_assume_tac o MATCH_MP cfg_forward_source_phi_operand) >>
  irule phi_input_not_code_end >>
  conj_tac >- (qexists_tac `ctx` >> simp[]) >>
  qexists_tac `i` >> simp[] >>
  metis_tac[fn_insts_def, MEM_fn_insts_blocks]
QED

Theorem cfg_split_code_end_var_forward:
  !fn x. code_end_var fn x ==>
  !s pred target split repls t out.
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) ==>
  code_end_var out x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts out)` by
    (irule cfg_split_retains_ordinary >>
     simp[is_terminator_def] >> metis_tac[]) >>
  metis_tac[code_end_var_rules]
QED

Theorem cfg_split_code_end_var_reverse:
  !out x. code_end_var out x ==>
  !fn s pred target split repls t ctx.
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions ==>
  code_end_var fn x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `MEM inst (fn_insts fn) \/
   ?v w. MEM (v,w) repls /\ inst.inst_opcode = ASSIGN /\
         inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]` by
    (irule cfg_split_ordinary_origin >>
     simp[is_terminator_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[code_end_var_rules, cfg_split_forward_source_not_code_end]
QED

Theorem cfg_split_code_end_var_iff:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions ==>
  (code_end_var out x <=> code_end_var fn x)
Proof
  metis_tac[cfg_split_code_end_var_forward, cfg_split_code_end_var_reverse]
QED
