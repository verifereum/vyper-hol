(*
 * Branch Optimization Pass — Output Checker
 *
 * A checker for the output of branch_opt: check_branch_opt_fn fn fn' holds
 * when fn' differs from fn only in its blocks, and every block of fn' is the
 * matching block of fn, or that block with one of the pass's two rewrites
 * of its final JNZ:
 *
 *   1. jnz v a b  ~>  jnz x b a,
 *      where v = iszero x comes earlier in the same block and neither v nor
 *      x is assigned between it and the jnz.
 *   2. jnz c a b  ~>  t = iszero c; jnz t b a,
 *      where t is not a variable of fn.
 *
 * The check is local to each block: it needs no dataflow graph, liveness
 * or SSA. branchOptCheckProofs proves that a checked fn' runs like fn.
 *
 * TOP-LEVEL:
 *   bo_iszero_src          — the operand x of the iszero that defines v
 *   check_branch_opt_block — one block of fn' against its source block
 *   check_branch_opt_fn    — fn' against fn, block by block
 *)
Theory branchOptCheck
Ancestors
  venomInst irSupply

(* Scans a block's instructions, last first, for the one that assigns v.
   Returns x when it is v = iszero x (x not v itself) and nothing between it
   and the end of the list assigns x. *)
Definition bo_iszero_src_def:
  bo_iszero_src v [] = NONE /\
  bo_iszero_src v (inst::rest) =
    if MEM v inst.inst_outputs then
      (if inst.inst_opcode = ISZERO /\ inst.inst_outputs = [v] then
         case inst.inst_operands of
           [Var x] => if x = v then NONE else SOME (Var x)
         | [Lit w] => SOME (Lit w)
         | _ => NONE
       else NONE)
    else
      case bo_iszero_src v rest of
        NONE => NONE
      | SOME x => if MEM x (MAP Var inst.inst_outputs) then NONE else SOME x
End

(* vars: the variables of the source function, which the temporary of
   rewrite 2 must avoid. *)
Definition check_branch_opt_block_def:
  check_branch_opt_block vars bb bb' <=>
    bb' = bb \/
    bb'.bb_label = bb.bb_label /\
    case (REVERSE bb.bb_instructions, REVERSE bb'.bb_instructions) of
      (t::pre, t'::rest') =>
        t.inst_opcode = JNZ /\
        (case t.inst_operands of
           [c; Label a; Label b] =>
             (rest' = pre /\
              case c of
                Var v =>
                  (case bo_iszero_src v pre of
                     SOME x => t' = t with inst_operands := [x; Label b; Label a]
                   | NONE => F)
              | _ => F) \/
             (case rest' of
                iz::pre' =>
                  pre' = pre /\ iz.inst_opcode = ISZERO /\ iz.inst_operands = [c] /\
                  (case iz.inst_outputs of
                     [tmp] => ~MEM tmp vars /\
                              t' = t with inst_operands := [Var tmp; Label b; Label a]
                   | _ => F)
              | [] => F)
         | _ => F)
    | _ => F
End

Definition check_branch_opt_fn_def:
  check_branch_opt_fn fn fn' <=>
    fn' = fn with fn_blocks := fn'.fn_blocks /\
    LIST_REL (check_branch_opt_block (fn_ir_vars fn)) fn.fn_blocks fn'.fn_blocks
End
