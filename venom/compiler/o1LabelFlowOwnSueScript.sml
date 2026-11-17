Theory o1LabelFlowOwnSue
Ancestors
  o1LabelFlowSueNegative o1ContractSue singleUseExpansionSupplySim list

Theorem sue_projection_code_end_uses:
  (!j. MEM j (fn_insts g) ==>
    (j.inst_opcode = ASSIGN /\ ?w. j.inst_outputs = [w] /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = [project w]) \/
    (?i. MEM i (fn_insts f) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      (!w. MEM w i.inst_outputs ==> project w = Var w) /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = i.inst_operands)) /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst;Var x;sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  !j v. MEM j (fn_insts g) /\ MEM (Var v) j.inst_operands /\
    code_end_var g v ==>
    (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var v]) \/
    (j.inst_opcode = CODECOPY /\ ?dst sz.
      j.inst_operands = [dst;Var v;sz] /\ dst <> Var v /\ sz <> Var v)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?x. project v = Var x /\ code_end_var f x` by
    (drule sue_projection_code_end_var >> disch_then irule >> simp[]) >>
  qpat_x_assum `!j. MEM j (fn_insts g) ==> _` drule >> strip_tac
  >- (drule_all sue_projection_singleton_use >> simp[]) >>
  `MEM (Var x) i.inst_operands` by
    (qpat_x_assum `MAP _ _ = _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists_tac `Var v` >> simp[]) >>
  irule sue_projection_allowed_use >> conj_tac >- simp[] >>
  qexistsl_tac [`i.inst_operands`,`project`,`x`] >> simp[] >> metis_tac[]
QED

Theorem sue_row_code_end_uses:
  fn_pass_step rp (CFP_Simple VP_SingleUseExpansion) observed s f out /\
  (!i x. MEM i (fn_insts f) /\ MEM (Var x) i.inst_operands /\
    code_end_var f x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst;Var x;sz] /\ dst <> Var x /\ sz <> Var x)) ==>
  !i x. MEM i (fn_insts out.fpo_function) /\ MEM (Var x) i.inst_operands /\
    code_end_var out.fpo_function x ==>
    (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
    (i.inst_opcode = CODECOPY /\ ?dst sz.
      i.inst_operands = [dst;Var x;sz] /\ dst <> Var x /\ sz <> Var x)
Proof
  strip_tac >> drule sue_pass_step_replay >> strip_tac >>
  drule_all sue_expand_function_supply_projection >> strip_tac >>
  rpt gen_tac >> strip_tac >> irule sue_projection_code_end_uses >>
  simp[] >> qexistsl_tac [`f`,`out.fpo_function`,`project`] >> simp[]
  >> (gvs[])
QED
