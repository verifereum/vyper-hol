(*
 * Common Subexpression Elimination Pass
 *
 * Port of venom/passes/common_subexpression_elimination.py.
 *)

Theory commonSubexpressionElim
Ancestors
  list
  irOps
  cfgAnalysis dfgAnalysis livenessAnalysis
  availableExpressionAnalysis

Definition uninteresting_opcodes_def:
  uninteresting_opcodes =
    [CALLDATASIZE; GASLIMIT; ADDRESS; CODESIZE; ASSIGN; PHI; PARAM; SOURCE; NOP;
     RETURNDATASIZE; GAS; GASPRICE; ORIGIN; COINBASE; TIMESTAMP; NUMBER;
     PREVRANDAO; CHAINID; BASEFEE; BLOBBASEFEE; MSIZE]
End

Definition no_substitute_opcodes_def:
  no_substitute_opcodes = OFFSET :: uninteresting_opcodes
End

Definition small_expression_def:
  small_expression = (1:num)
End

Definition opcode_in_list_def:
  opcode_in_list op ops <=> MEM op ops
End

Definition cse_find_replaceable_inst_def:
  cse_find_replaceable_inst fn ae inst acc =
    if opcode_in_list inst.inst_opcode no_substitute_opcodes then acc
    else if expr_is_nonidempotent inst.inst_opcode then acc
    else if inst_num_outputs inst > 1 then acc
    else
      case available_expr_get_expression ae inst.inst_id of
        NONE => acc
      | SOME (e, src_id) =>
          let depth = available_expr_depth ae e in
          if depth > small_expression then (inst.inst_id, src_id) :: acc
          else
            let from_same = available_expr_get_from_same_bb fn ae inst.inst_id e in
            case from_same of
              [] => acc
            | (i::_) => (inst.inst_id, i) :: acc
End

Definition cse_find_replaceable_def:
  cse_find_replaceable fn ae =
    FOLDL
      (λacc bb. FOLDL (λacc2 inst. cse_find_replaceable_inst fn ae inst acc2)
                       acc bb.bb_instructions)
      [] fn.fn_blocks
End

Definition cse_replace_inst_def:
  cse_replace_inst fn orig_id src_id =
    case (lookup_inst_in_function orig_id fn, lookup_inst_in_function src_id fn) of
      (SOME orig, SOME src) =>
        if has_outputs orig then
          case inst_output src of
            NONE => fn
          | SOME v =>
              let new_inst =
                orig with <| inst_opcode := ASSIGN;
                             inst_operands := [Var v] |> in
              update_inst_in_function orig_id new_inst fn
        else
          update_inst_in_function orig_id (inst_make_nop orig) fn
    | _ => fn
End

Definition cse_replace_def:
  cse_replace fn repls =
    FOLDL (λacc (orig,src). cse_replace_inst acc orig src) fn repls
End

Definition cse_iter_def:
  cse_iter 0 fn = fn /\
  cse_iter (SUC fuel) fn =
    let cfg = cfg_analyze fn in
    let dfg = dfg_analyze fn in
    let ae = available_expr_analyze fn cfg dfg in
    let repls = cse_find_replaceable fn ae in
    if repls = [] then fn
    else cse_iter fuel (cse_replace fn repls)
End

Definition cse_function_def:
  cse_function fn =
    let n = LENGTH (fn_instructions_list fn) in
    let fuel = (n + 1) * (n + 1) in
    cse_iter fuel fn
End

Definition cse_context_def:
  cse_context ctx =
    ctx with ctx_functions := MAP cse_function ctx.ctx_functions
End

val _ = export_theory();
