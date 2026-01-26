(*
 * Algebraic Optimization (Venom IR)
 *
 * Local algebraic rewrites plus limited operand rewrites (iszero-chain
 * simplification) and offset lowering.
 *)

Theory algebraicOptTransform
Ancestors
  list string words finite_map
  venomState venomInst

(* ==========================================================================
   Operand Helpers
   ========================================================================== *)

Definition is_lit_def:
  is_lit op =
    case op of
      Lit _ => T
    | _ => F
End

Definition is_label_def:
  is_label op =
    case op of
      Label _ => T
    | _ => F
End

Definition lit_eq_def:
  lit_eq op w =
    case op of
      Lit v => (v = w)
    | _ => F
End

Definition lit_is_zero_def:
  lit_is_zero op = lit_eq op (0w:bytes32)
End

Definition lit_is_one_def:
  lit_is_one op = lit_eq op (1w:bytes32)
End

Definition lit_is_ones_def:
  lit_is_ones op = lit_eq op (~(0w:bytes32))
End

(* ==========================================================================
   Instruction Builders
   ========================================================================== *)

Definition mk_assign_def:
  mk_assign inst op =
    inst with <| inst_opcode := ASSIGN; inst_operands := [op] |>
End

Definition mk_const_def:
  mk_const inst w = mk_assign inst (Lit w)
End

Definition mk_not_def:
  mk_not inst op =
    inst with <| inst_opcode := NOT; inst_operands := [op] |>
End

Definition fresh_var_def:
  fresh_var (id:num) = STRCAT "alg_tmp_" (toString id)
End

(* ==========================================================================
   Constants and Predicates
   ========================================================================== *)

Definition max_uint256_def:
  max_uint256 = (~(0w:bytes32))
End

Definition min_uint256_def:
  min_uint256 = (0w:bytes32)
End

Definition min_int256_def:
  min_int256 = word_lsl (1w:bytes32) 255
End

Definition max_int256_def:
  max_int256 = word_1comp min_int256
End

Definition is_commutative_def:
  is_commutative op <=>
    MEM op [ADD; MUL; AND; OR; XOR; EQ]
End

Definition flip_commutative_def:
  flip_commutative inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_commutative inst.inst_opcode /\ is_lit op1 /\ ~is_lit op2 then
          inst with inst_operands := [op2; op1]
        else inst
    | _ => inst
End

Definition is_pow2_num_def:
  is_pow2_num n <=> n <> 0 /\ ?k. n = 2 EXP k
End

Definition log2_num_def:
  log2_num n = (@k. n = 2 EXP k)
End

Definition is_pow2_lit_def:
  is_pow2_lit op <=>
    case op of
      Lit w => is_pow2_num (w2n w)
    | _ => F
End

Definition log2_lit_def:
  log2_lit op =
    case op of
      Lit w => log2_num (w2n w)
    | _ => 0
End

Definition is_comparator_def:
  is_comparator op <=>
    MEM op [GT; LT; SGT; SLT]
End

Definition is_gt_op_def:
  is_gt_op GT = T /\
  is_gt_op SGT = T /\
  is_gt_op _ = F
End

Definition is_signed_cmp_def:
  is_signed_cmp SGT = T /\
  is_signed_cmp SLT = T /\
  is_signed_cmp _ = F
End

Definition flip_comparator_def:
  flip_comparator GT = LT /\
  flip_comparator LT = GT /\
  flip_comparator SGT = SLT /\
  flip_comparator SLT = SGT /\
  flip_comparator op = op
End

(* ==========================================================================
   Small Rewrite Helpers (return list of instructions)
   ========================================================================== *)

Definition rewrite_add_def:
  rewrite_add inst =
    case inst.inst_operands of
      [op1; op2] =>
        if is_lit op1 /\ is_label op2 then [inst with inst_opcode := OFFSET]
        else if lit_is_zero op1 then [mk_assign inst op2]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_sub_def:
  rewrite_sub inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else if lit_is_ones op2 then [mk_not inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_xor_def:
  rewrite_xor inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else if lit_is_zero op1 then [mk_assign inst op2]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else if lit_is_ones op1 then [mk_not inst op2]
        else if lit_is_ones op2 then [mk_not inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_and_def:
  rewrite_and inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_ones op1 then [mk_assign inst op2]
        else if lit_is_ones op2 then [mk_assign inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_or_def:
  rewrite_or is_truthy inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_ones op1 \/ lit_is_ones op2 then
          [mk_const inst max_uint256]
        else if is_truthy /\ ((is_lit op1 /\ ~lit_is_zero op1) \/
                              (is_lit op2 /\ ~lit_is_zero op2)) then
          [mk_const inst (1w:bytes32)]
        else if lit_is_zero op1 then [mk_assign inst op2]
        else if lit_is_zero op2 then [mk_assign inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_mul_def:
  rewrite_mul inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op1 then [mk_assign inst op2]
        else if lit_is_one op2 then [mk_assign inst op1]
        else if is_pow2_lit op1 then
          let n = log2_lit op1 in
          [inst with <| inst_opcode := SHL; inst_operands := [Lit (n2w n); op2] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_div_def:
  rewrite_div inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op2 then [mk_assign inst op1]
        else if is_pow2_lit op2 then
          let n = log2_lit op2 in
          [inst with <| inst_opcode := SHR; inst_operands := [Lit (n2w n); op1] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_sdiv_def:
  rewrite_sdiv inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op2 then [mk_assign inst op1]
        else [inst]
    | _ => [inst]
End

Definition rewrite_mod_def:
  rewrite_mod inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op2 then [mk_const inst (0w:bytes32)]
        else if is_pow2_lit op2 then
          let n = w2n (case op2 of Lit w => w | _ => 0w) in
          [inst with <| inst_opcode := AND;
                         inst_operands := [Lit (n2w (n - 1)); op1] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_smod_def:
  rewrite_smod inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 \/ lit_is_zero op2 then
          [mk_const inst (0w:bytes32)]
        else if lit_is_one op2 then [mk_const inst (0w:bytes32)]
        else [inst]
    | _ => [inst]
End

Definition rewrite_exp_def:
  rewrite_exp inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 then [mk_const inst (1w:bytes32)]
        else if lit_is_one op2 then [mk_const inst (1w:bytes32)]
        else if lit_is_zero op2 then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op1] |>]
        else if lit_is_one op1 then [mk_assign inst op2]
        else [inst]
    | _ => [inst]
End

Definition rewrite_shift_def:
  rewrite_shift inst =
    case inst.inst_operands of
      [op1; op2] =>
        if lit_is_zero op1 then [mk_assign inst op2] else [inst]
    | _ => [inst]
End

Definition rewrite_eq_def:
  rewrite_eq prefer_iszero inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (1w:bytes32)]
        else if lit_is_zero op1 then
          [inst with <| inst_opcode := ISZERO; inst_operands := [op2] |>]
        else if lit_is_ones op1 then
          let tmp = mk_inst (inst.inst_id + 1) NOT [op2] [fresh_var inst.inst_id] in
          [tmp; inst with <| inst_opcode := ISZERO;
                              inst_operands := [Var (fresh_var inst.inst_id)] |>]
        else if prefer_iszero then
          let tmp = mk_inst (inst.inst_id + 1) XOR [op1; op2] [fresh_var inst.inst_id] in
          [tmp; inst with <| inst_opcode := ISZERO;
                              inst_operands := [Var (fresh_var inst.inst_id)] |>]
        else [inst]
    | _ => [inst]
End

Definition rewrite_cmp_def:
  rewrite_cmp prefer_iszero cmp_flip inst =
    case inst.inst_operands of
      [op1; op2] =>
        if op1 = op2 then [mk_const inst (0w:bytes32)]
        else
          let signed = is_signed_cmp inst.inst_opcode in
          let lo = if signed then min_int256 else min_uint256 in
          let hi = if signed then max_int256 else max_uint256 in
          let is_gt = is_gt_op inst.inst_opcode in
          let almost_always = if is_gt then lo else hi in
          let never = if is_gt then hi else lo in
          let almost_never = if is_gt then word_sub hi (1w:bytes32)
                             else word_add lo (1w:bytes32) in
            if lit_eq op1 never then [mk_const inst (0w:bytes32)]
            else if lit_eq op1 almost_never then
              [inst with <| inst_opcode := EQ;
                             inst_operands := [op2; Lit never] |>]
            else if prefer_iszero /\ lit_eq op1 almost_always then
              let tmp = mk_inst (inst.inst_id + 1) EQ [op1; op2]
                              [fresh_var inst.inst_id] in
              [tmp; inst with <| inst_opcode := ISZERO;
                                  inst_operands := [Var (fresh_var inst.inst_id)] |>]
            else if inst.inst_opcode = GT /\ lit_is_zero op1 then
              let tmp = mk_inst (inst.inst_id + 1) ISZERO [op2]
                              [fresh_var inst.inst_id] in
              [tmp; inst with <| inst_opcode := ISZERO;
                                  inst_operands := [Var (fresh_var inst.inst_id)] |>]
            else if cmp_flip /\ is_lit op1 then
              let new_op = flip_comparator inst.inst_opcode in
              let adj = if is_gt then word_add (case op1 of Lit w => w | _ => 0w) (1w:bytes32)
                        else word_sub (case op1 of Lit w => w | _ => 0w) (1w:bytes32) in
              [inst with <| inst_opcode := new_op;
                             inst_operands := [Lit adj; op2] |>]
            else [inst]
    | _ => [inst]
End

(* ==========================================================================
   Combined Instruction Transform (parameterized by analysis)
   ========================================================================== *)

Definition transform_inst_list_def:
  transform_inst_list prefer_iszero is_truthy cmp_flip inst =
    let inst1 = flip_commutative inst in
    case inst1.inst_opcode of
      ADD => rewrite_add inst1
    | SUB => rewrite_sub inst1
    | XOR => rewrite_xor inst1
    | AND => rewrite_and inst1
    | OR => rewrite_or is_truthy inst1
    | MUL => rewrite_mul inst1
    | Div => rewrite_div inst1
    | SDIV => rewrite_sdiv inst1
    | Mod => rewrite_mod inst1
    | SMOD => rewrite_smod inst1
    | venomInst$EXP => rewrite_exp inst1
    | SHL => rewrite_shift inst1
    | SHR => rewrite_shift inst1
    | SAR => rewrite_shift inst1
    | EQ => rewrite_eq prefer_iszero inst1
    | GT => rewrite_cmp prefer_iszero cmp_flip inst1
    | LT => rewrite_cmp prefer_iszero cmp_flip inst1
    | SGT => rewrite_cmp prefer_iszero cmp_flip inst1
    | SLT => rewrite_cmp prefer_iszero cmp_flip inst1
    | _ => [inst1]
End

(* ==========================================================================
   Block / Function / Context Transforms
   ========================================================================== *)

Definition transform_block_def:
  transform_block prefer_iszero is_truthy cmp_flip bb =
    bb with bb_instructions :=
      FLAT (MAP (transform_inst_list prefer_iszero is_truthy cmp_flip) bb.bb_instructions)
End

Definition transform_function_def:
  transform_function prefer_iszero is_truthy cmp_flip fn =
    fn with fn_blocks :=
      MAP (transform_block prefer_iszero is_truthy cmp_flip) fn.fn_blocks
End

(* ==========================================================================
   Iszero-chain Operand Rewriting (Abstract)
   ========================================================================== *)

Definition subst_operand_def:
  subst_operand sigma op =
    case op of
      Var v =>
        (case FLOOKUP sigma v of
           SOME v' => Var v'
         | NONE => op)
    | _ => op
End

Definition subst_operands_def:
  subst_operands sigma ops = MAP (subst_operand sigma) ops
End

Definition subst_inst_def:
  subst_inst sigma inst =
    inst with inst_operands := subst_operands sigma inst.inst_operands
End

Definition subst_block_def:
  subst_block sigma bb =
    bb with bb_instructions := MAP (subst_inst sigma) bb.bb_instructions
End

Definition subst_function_def:
  subst_function sigma fn =
    fn with fn_blocks := MAP (subst_block sigma) fn.fn_blocks
End

Definition iszero_var_def:
  iszero_var fn v <=>
    ?bb inst.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      inst.inst_opcode = ISZERO /\
      inst.inst_outputs = [v]
End

Definition iszero_subst_def:
  iszero_subst fn sigma <=>
    !v v'. FLOOKUP sigma v = SOME v' ==> iszero_var fn v
End

Definition rewrite_iszero_chains_def:
  rewrite_iszero_chains fn fn' <=>
    ?sigma.
      iszero_subst fn sigma /\
      fn' = subst_function sigma fn
End

Definition algebraic_opt_transform_def:
  algebraic_opt_transform fn fn' <=>
    ?prefer_iszero is_truthy cmp_flip fn1.
      fn1 = transform_function prefer_iszero is_truthy cmp_flip fn /\
      rewrite_iszero_chains fn1 fn'
End

Definition algebraic_opt_context_def:
  algebraic_opt_context ctx ctx' <=>
    MAP (\f. f.fn_name) ctx'.ctx_functions =
    MAP (\f. f.fn_name) ctx.ctx_functions /\
    (!fn.
       MEM fn ctx.ctx_functions ==>
       ?fn'. MEM fn' ctx'.ctx_functions /\
             fn'.fn_name = fn.fn_name /\
             algebraic_opt_transform fn fn')
End
