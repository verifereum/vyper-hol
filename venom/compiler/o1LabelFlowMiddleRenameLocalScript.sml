Theory o1LabelFlowMiddleRenameLocal
Ancestors
  makeSsaDefs makeSsaCurrentAllocation o1MakeSsaReaching
  venomInst list pair

Theorem rename_current_code_end_seed:
  d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
  push_current_name s rs x = (rt,t,n) ==>
  rename_current_inst s rs d =
    (rt,t,d with <| inst_operands :=
       rename_current_operands rs [op; Label "code_end"];
       inst_outputs := [n] |>)
Proof
  strip_tac >>
  simp[rename_current_inst_def, rename_current_outputs_def]
QED

Theorem rename_current_code_end_use:
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  push_current_name s rs x = (rt,t,n) /\
  rename_current_outputs t rt j.inst_outputs = (ru,u,outs) ==>
  rename_current_inst t rt j =
    (ru,u,j with <| inst_operands :=
      rename_current_operands rt [dst] ++ [Var n] ++
      rename_current_operands rt [sz]; inst_outputs := outs |>)
Proof
  strip_tac >> drule current_push_latest >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `dst` >> Cases_on `sz` >>
  simp[rename_current_inst_def, rename_current_operands_def]
QED

Theorem rename_current_adjacent_code_end:
  d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  rename_current_block_insts s rs (d::j::post) = (rt,t,ys) ==>
  ?d' j' post' n a b c.
    ys = d'::j'::post' /\
    d'.inst_opcode = ADD /\ d'.inst_outputs = [n] /\
    d'.inst_operands = [a; Label "code_end"] /\
    j'.inst_opcode = CODECOPY /\ j'.inst_operands = [b; Var n; c]
Proof
  strip_tac >>
  qpat_x_assum `rename_current_block_insts _ _ _ = _` mp_tac >>
  simp[rename_current_block_insts_def, rename_current_inst_def,
       rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule current_push_latest >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `op` >> Cases_on `dst` >> Cases_on `sz` >>
  gvs[rename_current_operands_def]
QED

Theorem rename_current_block_code_end_pair:
  d.inst_opcode = ADD /\
  d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  rename_current_block_insts s rs (pre ++ d::j::post) = (rt,t,ys) ==>
  ?pre' d' j' post' n a b c.
    ys = pre' ++ d'::j'::post' /\ LENGTH pre' = LENGTH pre /\
    d'.inst_opcode = ADD /\ d'.inst_outputs = [n] /\
    d'.inst_operands = [a; Label "code_end"] /\
    j'.inst_opcode = CODECOPY /\ j'.inst_operands = [b; Var n; c]
Proof
  simp[rename_current_block_insts_append] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all rename_current_adjacent_code_end >> strip_tac >> gvs[] >>
  qpat_assum `rename_current_block_insts _ _ pre = _`
    (mp_tac o MATCH_MP o1MakeSsaCfgTheory.rename_current_block_insts_length) >>
  strip_tac >> qexistsl [`ns`, `d'`, `j'`, `post'`, `n`, `a`, `b`, `c`] >>
  simp[]
QED

(* Arbitrary stacks need not be injective.  Exclude both the pushed
   variable and aliases to the new spelling when protecting an operand. *)
Theorem rename_current_code_end_use_nonalias:
  j.inst_opcode = CODECOPY /\ j.inst_operands = [dst; Var x; sz] /\
  push_current_name s rs x = (rt,t,n) /\
  rename_current_inst t rt j = (ru,u,j') /\
  (!v. dst = Var v ==> v <> x /\ latest_current_name rs v <> n) /\
  (!v. sz = Var v ==> v <> x /\ latest_current_name rs v <> n) ==>
  ?b c. j'.inst_operands = [b; Var n; c] /\
        b <> Var n /\ c <> Var n
Proof
  strip_tac >> drule current_push_latest >> strip_tac >>
  qpat_x_assum `rename_current_inst _ _ _ = _` mp_tac >>
  simp[rename_current_inst_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  Cases_on `dst` >> Cases_on `sz` >>
  gvs[rename_current_operands_def]
QED
