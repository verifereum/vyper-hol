(* Exact operand-continuation equations for the supply-aware SUE transform. *)
Theory venomSingleUseEval
Ancestors singleUseExpansionDefs list pair arithmetic

Definition sue_operand_use_count_def:
  sue_operand_use_count dfg op =
    case op of Var v => LENGTH (dfg_get_uses dfg v) | Lit w => 0 | Label l => 0
End

Definition sue_finish_operand_def:
  sue_finish_operand op needs (remaining:num) (uses:num) (assigns,ops,supply) =
    if ~needs then (assigns,op::ops,supply)
    else case op of
      Var v =>
        if uses = 1 /\ remaining = 0 then (assigns,op::ops,supply)
        else (case sue_alloc_assign_supply supply op of (inst,new_op,supply') =>
          (inst::assigns,new_op::ops,supply'))
    | Label l => (assigns,op::ops,supply)
    | Lit w =>
        (case sue_alloc_assign_supply supply op of (inst,new_op,supply') =>
          (inst::assigns,new_op::ops,supply'))
End

Definition sue_prepend_assignment_def:
  sue_prepend_assignment assigns ops (inst,new_op,supply) =
    (inst::assigns,new_op::ops,supply)
End

Theorem sue_finish_operand_direct:
  sue_finish_operand op needs remaining uses (assigns,ops,supply) =
    if ~needs \/
        (case op of Var v => uses = 1 /\ remaining = 0
                  | Lit w => F | Label l => T) then
      (assigns,op::ops,supply)
    else sue_prepend_assignment assigns ops (sue_alloc_assign_supply supply op)
Proof
  Cases_on `sue_alloc_assign_supply supply op` >>
  rename1 `sue_alloc_assign_supply supply op = (fresh,tail)` >>
  Cases_on `tail` >> Cases_on `op` >> Cases_on `needs` >>
  simp[sue_finish_operand_def, sue_prepend_assignment_def]
QED

Theorem sue_expand_ops_supply_step:
  sue_expand_ops_supply dfg inst supply (op::rest) idx =
    sue_finish_operand op (sue_needs_assign dfg inst idx)
      (sue_count_remaining op rest) (sue_operand_use_count dfg op)
      (sue_expand_ops_supply dfg inst supply rest (idx + 1))
Proof
  Cases_on `sue_expand_ops_supply dfg inst supply rest (idx + 1)` >>
  rename1 `sue_expand_ops_supply dfg inst supply rest (idx + 1) = (assigns,tail)` >>
  Cases_on `tail` >> Cases_on `op` >>
  simp[Once sue_expand_ops_supply_def, sue_finish_operand_def,
       sue_operand_use_count_def]
QED

Theorem sue_expand_insts_supply_cons_result:
  sue_expand_inst_supply dfg supply inst = (out,supply1) /\
  sue_expand_insts_supply dfg supply1 rest = (outs,supply2) ==>
  sue_expand_insts_supply dfg supply (inst::rest) = (out ++ outs,supply2)
Proof
  strip_tac >> simp[Once sue_expand_insts_supply_def]
QED

Theorem sue_expand_blocks_supply_cons_result:
  sue_expand_block_supply dfg supply bb = (bb',supply1) /\
  sue_expand_blocks_supply dfg supply1 rest = (bbs',supply2) ==>
  sue_expand_blocks_supply dfg supply (bb::rest) = (bb'::bbs',supply2)
Proof
  strip_tac >> simp[Once sue_expand_blocks_supply_def]
QED

Theorem sue_expand_block_supply_result:
  sue_expand_insts_supply dfg supply bb.bb_instructions = (insts,supply1) ==>
  sue_expand_block_supply dfg supply bb =
    (bb with bb_instructions := insts,supply1)
Proof
  strip_tac >> simp[Once sue_expand_block_supply_def]
QED
