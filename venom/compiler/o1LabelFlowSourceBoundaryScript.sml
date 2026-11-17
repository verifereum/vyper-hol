Theory o1LabelFlowSourceBoundary
Ancestors
  codegenSymRel

Theorem code_end_var_has_label_seed:
  !f x. code_end_var f x ==>
    ?i. MEM i (fn_insts f) /\ MEM (Label "code_end") i.inst_operands
Proof
  Induct_on `code_end_var` >> rpt strip_tac >> metis_tac[listTheory.MEM]
QED

Theorem code_end_var_absent:
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) ==>
  !x. ~code_end_var f x
Proof
  metis_tac[code_end_var_has_label_seed]
QED

Theorem label_flow_ok_seed_free:
  (!f i. MEM f ctx.ctx_functions /\ MEM i (fn_insts f) ==>
     ~MEM (Label "code_end") i.inst_operands) ==>
  (label_flow_ok ctx <=>
   !f i. MEM f ctx.ctx_functions /\ MEM i (fn_insts f) ==>
     i.inst_opcode <> CODESIZE /\
     (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]))
Proof
  strip_tac >>
  `!f x. MEM f ctx.ctx_functions ==> ~code_end_var f x` by
    metis_tac[code_end_var_absent] >>
  simp[label_flow_ok_def]
QED

Theorem label_flow_ok_seed_free_function:
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) ==>
  (label_flow_ok (ctx with ctx_functions := [f]) <=>
   !i. MEM i (fn_insts f) ==>
     i.inst_opcode <> CODESIZE /\
     (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz]))
Proof
  strip_tac >>
  qspec_then `ctx with ctx_functions := [f]` mp_tac
    (GEN_ALL label_flow_ok_seed_free) >>
  simp[]
QED

Theorem label_flow_seed_free_extract:
  label_flow_ok ctx /\ MEM f ctx.ctx_functions /\
  (!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) ==>
  !i. MEM i (fn_insts f) ==>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
     ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])
Proof
  strip_tac >>
  `!x. ~code_end_var f x` by metis_tac[code_end_var_absent] >>
  gvs[label_flow_ok_def] >> metis_tac[]
QED

Theorem variable_map_runtime_copy_reflect:
  MAP (\op. case op of Var u => Var (orig u) | _ => op) ops =
    [dst; Label "runtime_begin"; sz] ==>
  ?d s. ops = [d; Label "runtime_begin"; s]
Proof
  namedCases_on `ops` ["", "a rest"] >- simp[] >>
  namedCases_on `rest` ["", "b rest2"] >- simp[] >>
  namedCases_on `rest2` ["", "c rest3"] >- simp[] >>
  Cases_on `rest3` >- (Cases_on `b` >> simp[]) >> simp[]
QED

Theorem seed_free_flow_origin_transport:
  (!i. MEM i (fn_insts f) ==>
    i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])) /\
  (!j. MEM j (fn_insts g) ==>
    MEM j.inst_opcode [PHI; ASSIGN; NOP] \/
    ?i. MEM i (fn_insts f) /\ j.inst_opcode = i.inst_opcode /\
      MAP (\op. case op of Var u => Var (orig u) | _ => op)
        j.inst_operands = i.inst_operands) ==>
  !j. MEM j (fn_insts g) ==>
    j.inst_opcode <> CODESIZE /\
    (j.inst_opcode = CODECOPY ==>
      ?dst sz. j.inst_operands = [dst; Label "runtime_begin"; sz])
Proof
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  metis_tac[variable_map_runtime_copy_reflect]
QED
