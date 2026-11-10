Theory symPlannerReorder
Ancestors
  list stackModel symPlannerBase symPlannerMoves reorderSim deepResidualBudget
  unitShapeDefs venomWf dfgDefs

Theorem LIST_REL_stack_poke_exchange[local]:
  LIST_REL R (REVERSE stk) top /\ a < LENGTH stk /\ b < LENGTH stk /\
  (!sv. R (stack_peek a stk) sv <=> R (stack_peek b stk) sv) ==>
  LIST_REL R (REVERSE (stack_poke b (stack_peek a stk)
    (stack_poke a (stack_peek b stk) stk))) top
Proof
  rw[LIST_REL_EL_EQN, EL_REVERSE, stack_poke_def, EL_LUPDATE, stack_peek_def] >>
  gvs[stack_peek_def] >> metis_tac[]
QED

Theorem sym_kinds_ok_poke_exchange:
  sym_kinds_ok cplan fn ret srest ps ss /\
  a < LENGTH ps.ps_stack /\ b < LENGTH ps.ps_stack /\
  stack_peek a ps.ps_stack = op /\
  operand_equiv dfg op (stack_peek b ps.ps_stack) /\
  dfg = dfg_build_function fn /\ ssa_form fn /\ fn_shape_ok fn ==>
  sym_kinds_ok cplan fn ret srest
    (ps with ps_stack := stack_poke b op
      (stack_poke a (stack_peek b ps.ps_stack) ps.ps_stack)) ss
Proof
  rw[codegenSymRelTheory.sym_kinds_ok_def] >> qexists `top` >>
  simp[LIST_REL_stack_poke_exchange, op_kind_ok_operand_equiv]
QED
