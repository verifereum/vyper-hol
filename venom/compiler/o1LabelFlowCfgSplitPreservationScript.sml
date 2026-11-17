Theory o1LabelFlowCfgSplitPreservation
Ancestors
  o1LabelFlowCfgSplitTaint o1LabelFlowLateCfgNorm cfgNormSupplySim
  codegenSymRel venomInst irSupply list

Theorem code_end_var_ir_var:
  !fn x. code_end_var fn x ==> MEM x (irSupply$fn_ir_vars fn)
Proof
  Induct_on `code_end_var` >> metis_tac[supply_inst_output_ir_var]
QED

Theorem cfg_split_replacement_not_code_end:
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  build_split_block_supply s pred target = (split,repls,t) /\
  MEM (v,x) repls ==> ~code_end_var fn x
Proof
  metis_tac[supply_split_replacement_not_old, code_end_var_ir_var]
QED

Theorem cfg_split_image_use:
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions /\
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
              dst <> Var x /\ sz <> Var x))` by
    metis_tac[label_flow_ok_def] >>
  `j = i` by
    (irule supply_inst_image_unchanged >>
     simp[is_terminator_def] >> metis_tac[]) >>
  gvs[]
QED

Theorem cfg_split_label_flow_ok:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  MEM pred fn.fn_blocks /\ MEM target fn.fn_blocks /\
  build_split_block_supply s pred target = (split,repls,t) /\
  insert_split_supply s fn pred target = (out,t) /\
  label_flow_ok ctx /\ MEM fn ctx.ctx_functions ==>
  label_flow_ok (ctx with ctx_functions := [out])
Proof
  strip_tac >>
  `!x. code_end_var out x <=> code_end_var fn x` by
    metis_tac[cfg_split_code_end_var_iff] >>
  `!v x. MEM (v,x) repls ==> ~code_end_var fn x` by
    metis_tac[cfg_split_replacement_not_code_end] >>
  simp[label_flow_ok_def] >> qx_gen_tac `j` >> strip_tac >>
  drule_all insert_split_supply_inst_image >> strip_tac
  >- (drule_all supply_split_inst_source >> strip_tac >>
      gvs[] >> simp[] >> rpt strip_tac >> gvs[]) >>
  `j.inst_opcode = old.inst_opcode` by
    metis_tac[supply_inst_image_metadata] >>
  conj_tac >- metis_tac[label_flow_ok_def] >>
  conj_tac
  >- (rpt strip_tac >> irule cfg_split_image_use >>
      metis_tac[]) >>
  strip_tac >>
  `old.inst_opcode = CODECOPY` by metis_tac[] >>
  `j = old` by
    (irule supply_inst_image_unchanged >>
     simp[is_terminator_def] >> metis_tac[]) >>
  gvs[] >> metis_tac[label_flow_ok_def]
QED
