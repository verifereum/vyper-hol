Theory o1LabelFlowOwnCfgNorm
Ancestors
  o1LabelFlowCfgSplitPreservation o1LabelFlowCfgSplitTaint
  o1LabelFlowLateCfgNorm o1LabelFlowCfgIteration
  o1ContractCfgNormStep o1ContractCfgNorm cfgNormSupplySim cfgNormSupplyProofs
  cfgNormDefs codegenSymRel venomInst irSupply unitShapeDefs list pair

Theorem cfg_split_forward_source_code_end_excluded:
  build_split_block_supply s pred target = (split,repls,t) /\
  MEM target fn.fn_blocks /\
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
  MEM (v,w) repls ==> ~code_end_var fn v
Proof
  strip_tac >> drule_all cfg_split_replacement_source >>
  disch_then (strip_assume_tac o MATCH_MP cfg_forward_source_phi_operand) >>
  `MEM i (fn_insts fn)` by metis_tac[fn_insts_def, MEM_fn_insts_blocks] >>
  strip_tac >> first_x_assum (qspecl_then [`i`, `v`] mp_tac) >> simp[]
QED

Theorem cfg_split_code_end_reflect_uses:
  !out x. code_end_var out x ==>
  !fn s pred target split repls t.
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  code_end_var fn x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (`MEM inst (fn_insts fn) \/
       ?v w. MEM (v,w) repls /\ inst.inst_opcode = ASSIGN /\
             inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]` by
        (irule cfg_split_ordinary_origin >>
         simp[is_terminator_def] >> metis_tac[]) >>
      gvs[] >> metis_tac[code_end_var_rules]) >>
  rename1 `inst.inst_operands = [Var y]` >>
  `code_end_var fn y` by (first_x_assum irule >> metis_tac[]) >>
  `MEM inst (fn_insts fn) \/
   ?v w. MEM (v,w) repls /\ inst.inst_opcode = ASSIGN /\
         inst.inst_operands = [Var v] /\ inst.inst_outputs = [w]` by
    (irule cfg_split_ordinary_origin >>
     simp[is_terminator_def] >> metis_tac[]) >>
  gvs[] >- metis_tac[code_end_var_rules] >>
  metis_tac[cfg_split_forward_source_code_end_excluded]
QED

Theorem cfg_split_image_code_end_uses:
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
  MEM i (fn_insts fn) /\
  supply_inst_image pred target split repls i j /\
  (!v x. MEM (v,x) repls ==> ~code_end_var fn x) /\
  MEM (Var x) j.inst_operands /\ code_end_var fn x ==>
  (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var x]) \/
  (j.inst_opcode = CODECOPY /\
   ?dst sz. j.inst_operands = [dst; Var x; sz] /\
            dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >>
  `MEM (Var x) i.inst_operands` by
    (Cases_on `i.inst_opcode = PHI`
     >- metis_tac[supply_inst_image_phi_vars] >>
     metis_tac[supply_inst_image_nonphi_vars]) >>
  `((i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\
     ?dst sz. i.inst_operands = [dst; Var x; sz] /\
              dst <> Var x /\ sz <> Var x))` by metis_tac[] >>
  `j = i` by
    (irule supply_inst_image_unchanged >>
     simp[is_terminator_def] >> metis_tac[]) >>
  gvs[]
QED

Theorem cfg_split_code_end_uses:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts out) /\ MEM (Var x) i.inst_operands /\
    code_end_var out x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all cfg_split_code_end_reflect_uses >> strip_tac >>
  `!v x. MEM (v,x) repls ==> ~code_end_var fn x` by
    metis_tac[cfg_split_replacement_not_code_end] >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_source >> strip_tac >>
      gvs[] >> simp[] >> rpt strip_tac >> gvs[]) >>
  irule cfg_split_image_code_end_uses >> metis_tac[]
QED

Theorem cfg_norm_round_code_end_uses:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  wf_function fn' /\ ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s' /\
  (!i x. MEM i (fn_insts fn') /\ MEM (Var x) i.inst_operands /\
    code_end_var fn' x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[] >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s'` by
    metis_tac[insert_split_supply_ir_covered] >>
  simp[] >> drule insert_split_supply_labels >> strip_tac >>
  drule_at (Pat `insert_split_supply _ _ _ _ = _`)
    cfg_split_code_end_uses >> simp[]
QED

Theorem cfg_norm_iter_code_end_uses:
  !n s fn fn' s'.
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  (!i x. MEM i (fn_insts fn) /\ MEM (Var x) i.inst_operands /\
    code_end_var fn x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  wf_function fn' /\ ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s' /\
  (!i x. MEM i (fn_insts fn') /\ MEM (Var x) i.inst_operands /\
    code_end_var fn' x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  drule_all cfg_norm_round_code_end_uses >> strip_tac >>
  qpat_x_assum `cfg_norm_iter_supply (SUC n) s fn = _` mp_tac >>
  simp[Once cfg_norm_iter_supply_def] >>
  Cases_on `changed` >> simp[] >> strip_tac
  >- ((first_x_assum irule >> simp[] >> (metis_tac[]))) >>
  gvs[]
QED

Theorem cfg_norm_row_code_end_uses:
  fn_pass_step rp (CFP_Simple VP_CFGNormalization) observed s f out /\
  wf_function f /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  (!i x. MEM i (fn_insts out.fpo_function) /\ MEM (Var x) i.inst_operands /\
    code_end_var out.fpo_function x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst; Var x; sz] /\ dst <> Var x /\ sz <> Var x))
Proof
  strip_tac >> drule cfg_norm_pass_step_replay >> strip_tac >>
  gvs[cfg_norm_function_supply_def] >>
  drule_at (Pat `cfg_norm_iter_supply _ _ _ = _`)
    cfg_norm_iter_code_end_uses >> simp[]
QED
