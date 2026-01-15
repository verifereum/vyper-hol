(*
 * Single Use Expansion Pass
 *
 * Port of venom/passes/single_use_expansion.py.
 *)

Theory singleUseExpansion
Ancestors
  list
  irOps dfgAnalysis compilerState

Definition count_operand_def:
  count_operand op [] = 0 /\
  count_operand op (x::xs) =
    (if x = op then 1 else 0) + count_operand op xs
End

Definition update_operand_at_def:
  update_operand_at ops idx new_op = LUPDATE new_op idx ops
End

Definition should_skip_opcode_def:
  should_skip_opcode op <=>
    op IN {ASSIGN; OFFSET; PHI; PARAM}
End

Definition is_lit_or_var_def:
  is_lit_or_var op <=>
    case op of
      Lit _ => T
    | Var _ => T
    | _ => F
End

Definition expand_operands_def:
  expand_operands st dfg inst idx [] = ([], inst, st) /\
  expand_operands st dfg inst idx (op::ops) =
    let (new_insts, inst', st') = expand_operands st dfg inst (idx + 1) ops in
    if inst.inst_opcode = LOG /\ idx = 0 then
      (new_insts, inst', st')
    else if ~is_lit_or_var op then
      (new_insts, inst', st')
    else
      (case op of
         Var v =>
           let uses = dfg_get_uses dfg v in
           if LENGTH uses = 1 /\ count_operand (Var v) inst'.inst_operands = 1 then
             (new_insts, inst', st')
           else
             let (var, st1) = fresh_var st' in
             let (iid, st2) = fresh_inst_id st1 in
             let assign_inst = mk_inst iid ASSIGN [op] [var] in
             let inst'' =
               inst' with inst_operands :=
                 update_operand_at inst'.inst_operands idx (Var var) in
             (assign_inst :: new_insts, inst'', st2)
       | Lit _ =>
           let (var, st1) = fresh_var st' in
           let (iid, st2) = fresh_inst_id st1 in
           let assign_inst = mk_inst iid ASSIGN [op] [var] in
           let inst'' =
             inst' with inst_operands :=
               update_operand_at inst'.inst_operands idx (Var var) in
           (assign_inst :: new_insts, inst'', st2)
       | _ => (new_insts, inst', st'))
End

Definition single_use_expand_inst_def:
  single_use_expand_inst st dfg inst =
    if should_skip_opcode inst.inst_opcode then ([], inst, st)
    else
      let (new_insts, inst', st') =
        expand_operands st dfg inst 0 inst.inst_operands in
      (new_insts, inst', st')
End

Definition single_use_expand_insts_def:
  single_use_expand_insts st dfg [] = ([], st) /\
  single_use_expand_insts st dfg (inst::rest) =
    let (prefix, inst', st1) = single_use_expand_inst st dfg inst in
    let (rest', st2) = single_use_expand_insts st1 dfg rest in
    (prefix ++ (inst' :: rest'), st2)
End

Definition single_use_expand_block_def:
  single_use_expand_block st dfg bb =
    let (insts', st') = single_use_expand_insts st dfg bb.bb_instructions in
    (bb with bb_instructions := insts', st')
End

Definition single_use_expand_function_def:
  single_use_expand_function fn =
    let dfg = dfg_analyze fn in
    let st0 = init_state_for_function fn in
    let (bbs', _) =
      FOLDL
        (λacc bb.
           let (bbs, st) = acc in
           let (bb', st') = single_use_expand_block st dfg bb in
           (bbs ++ [bb'], st'))
        ([], st0) fn.fn_blocks in
    fn with fn_blocks := bbs'
End

Definition single_use_expand_context_def:
  single_use_expand_context ctx =
    ctx with ctx_functions := MAP single_use_expand_function ctx.ctx_functions
End

val _ = export_theory();
