Theory o1LabelFlowSueNegative
Ancestors
  o1LabelFlowLateSue singleUseExpansionSupplySim codegenSymRel list

Theorem sue_projection_code_end_var:
  !g v. code_end_var g v ==>
  !f project.
  (!j. MEM j (fn_insts g) ==>
    (j.inst_opcode = ASSIGN /\ ?w. j.inst_outputs = [w] /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = [project w]) \/
    (?i. MEM i (fn_insts f) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      (!w. MEM w i.inst_outputs ==> project w = Var w) /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = i.inst_operands)) ==>
  ?x. project v = Var x /\ code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac
  >- (first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
      metis_tac[code_end_var_rules]) >>
  qpat_x_assum `!f project. _` drule_all >> strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts g) ==> _` drule >>
  simp[] >> strip_tac >> gvs[] >>
  metis_tac[code_end_var_rules]
QED

Theorem sue_projection_allowed_use:
  MEM (Var v) ops /\ project v = Var x /\
  MAP (\op. case op of Var w => project w | other => other) ops = old /\
  ((opc = ASSIGN /\ old = [Var x]) \/
   (opc = CODECOPY /\ ?dst sz. old = [dst;Var x;sz] /\
      dst <> Var x /\ sz <> Var x)) ==>
  (opc = ASSIGN /\ ops = [Var v]) \/
  (opc = CODECOPY /\ ?dst sz. ops = [dst;Var v;sz] /\
      dst <> Var v /\ sz <> Var v)
Proof
  strip_tac >> gvs[MAP_EQ_CONS] >>
  conj_tac >> strip_tac >> gvs[]
QED

Theorem sue_projection_singleton_use:
  MEM (Var v) ops /\
  MAP (\op. case op of Var w => project w | other => other) ops = [op] ==>
  ops = [Var v]
Proof
  strip_tac >> gvs[MAP_EQ_CONS]
QED

Theorem sue_projection_negative_flow:
  (!j. MEM j (fn_insts g) ==>
    (j.inst_opcode = ASSIGN /\ ?w. j.inst_outputs = [w] /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = [project w]) \/
    (?i. MEM i (fn_insts f) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      (!w. MEM w i.inst_outputs ==> project w = Var w) /\
      MAP (\op. case op of Var x => project x | other => other)
        j.inst_operands = i.inst_operands)) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  !j. MEM j (fn_insts g) ==>
    j.inst_opcode <> CODESIZE /\
    (!v. MEM (Var v) j.inst_operands /\ code_end_var g v ==>
      (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var v]) \/
      (j.inst_opcode = CODECOPY /\ ?dst sz.
        j.inst_operands = [dst;Var v;sz] /\ dst <> Var v /\ sz <> Var v))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `!v. code_end_var g v ==> ?x. project v = Var x /\ code_end_var f x` by
    (rpt strip_tac >> drule sue_projection_code_end_var >>
     disch_then irule >> simp[]) >>
  qpat_x_assum `!j. MEM j (fn_insts g) ==> _` drule >> strip_tac
  >- (simp[] >> rpt strip_tac >>
      drule_all sue_projection_singleton_use >> simp[]) >>
  `i.inst_opcode <> CODESIZE /\
   (!x. MEM (Var x) i.inst_operands /\ code_end_var f x ==>
     (i.inst_opcode = ASSIGN /\ i.inst_operands = [Var x]) \/
     (i.inst_opcode = CODECOPY /\ ?dst sz.
       i.inst_operands = [dst;Var x;sz] /\ dst <> Var x /\ sz <> Var x))` by
    (gvs[label_flow_ok_def] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >>
  `?x. project v = Var x /\ code_end_var f x` by metis_tac[] >>
  `MEM (Var x) i.inst_operands` by
    (qpat_x_assum `MAP _ _ = _` (SUBST1_TAC o SYM) >>
     simp[MEM_MAP] >> qexists_tac `Var v` >> simp[]) >>
  irule sue_projection_allowed_use >> conj_tac >- simp[] >>
  qexistsl_tac [`i.inst_operands`,`project`,`x`] >> simp[] >> metis_tac[]
QED

Theorem sue_expand_function_supply_negative_flow:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s f /\
  sue_expand_function_supply s f = (g,t) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  !j. MEM j (fn_insts g) ==>
    j.inst_opcode <> CODESIZE /\
    (!v. MEM (Var v) j.inst_operands /\ code_end_var g v ==>
      (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var v]) \/
      (j.inst_opcode = CODECOPY /\ ?dst sz.
        j.inst_operands = [dst;Var v;sz] /\ dst <> Var v /\ sz <> Var v))
Proof
  strip_tac >> drule_all sue_expand_function_supply_projection >> strip_tac >>
  gen_tac >> strip_tac >> irule sue_projection_negative_flow >>
  reverse conj_tac >- simp[] >> qexistsl_tac [`ctx`,`f`,`project`] >> simp[]
QED
