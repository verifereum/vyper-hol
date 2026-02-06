(*
 * Algebraic Optimization (Venom IR)
 *
 * Local algebraic rewrites plus limited operand rewrites (iszero-chain
 * simplification) and offset lowering.
 *)

Theory algebraicOptTransform
Ancestors
  list string words finite_map alist
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
   Analysis Hints (per-instruction)
   ========================================================================== *)

Datatype:
  opt_hint = <|
    prefer_iszero: bool;
    is_truthy: bool;
    cmp_flip: bool
  |>
End

Datatype:
  opt_analysis = <|
    hints: (num # opt_hint) list;
    subst: (string # operand) list
  |>
End

Definition default_hint_def:
  default_hint = <|
    prefer_iszero := F;
    is_truthy := F;
    cmp_flip := F
  |>
End

Definition hint_lookup_def:
  hint_lookup hints id =
    case ALOOKUP hints id of
      SOME h => h
    | NONE => default_hint
End

Definition opt_analysis_init_def:
  opt_analysis_init = <|
    hints := [];
    subst := []
  |>
End

(* ==========================================================================
   Analysis (Fixpoint over Hints/Substitution)
   ========================================================================== *)

Definition all_insts_def:
  all_insts fn = FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)
End

Definition inst_uses_var_def:
  inst_uses_var v inst = MEM (Var v) inst.inst_operands
End

Definition uses_of_var_def:
  uses_of_var fn v = FILTER (inst_uses_var v) (all_insts fn)
End

Definition uses_all_truthy_def:
  uses_all_truthy fn v <=>
    EVERY (\i. MEM i.inst_opcode [ISZERO; JNZ; ASSERT; ASSERT_UNREACHABLE])
          (uses_of_var fn v)
End

Definition uses_prefer_iszero_def:
  uses_prefer_iszero fn v <=>
    EVERY (\i. MEM i.inst_opcode [ISZERO; ASSERT]) (uses_of_var fn v)
End

Definition cmp_flip_hint_def:
  cmp_flip_hint fn inst =
    if ~is_comparator inst.inst_opcode then F
    else
      case inst.inst_operands of
        [op1; op2] =>
          if ~is_lit op1 then F
          else
            (case inst_output inst of
               NONE => F
             | SOME v =>
                 (case uses_of_var fn v of
                    [after] =>
                      if MEM after.inst_opcode [ISZERO; ASSERT] then
                        if after.inst_opcode = ISZERO then
                          (case inst_output after of
                             NONE => F
                           | SOME v2 =>
                               (case uses_of_var fn v2 of
                                  [use2] =>
                                    if use2.inst_opcode = ASSERT then F else T
                                | _ => F))
                        else T
                      else F
                  | _ => F))
      | _ => F
End

Definition compute_hint_def:
  compute_hint fn inst =
    case inst_output inst of
      NONE => default_hint
    | SOME v =>
        <| prefer_iszero := uses_prefer_iszero fn v;
           is_truthy := uses_all_truthy fn v;
           cmp_flip := cmp_flip_hint fn inst |>
End

Definition compute_hints_def:
  compute_hints fn =
    MAP (\inst. (inst.inst_id, compute_hint fn inst)) (all_insts fn)
End

Definition compute_iszero_subst_def:
  compute_iszero_subst fn = ([]:(string # operand) list)
End

Definition analysis_step_def:
  analysis_step fn st =
    st with <| hints := compute_hints fn;
               subst := compute_iszero_subst fn |>
End

Definition analysis_iter_def:
  analysis_iter fn 0 st = st /\
  analysis_iter fn (SUC n) st =
    let st' = analysis_step fn st in
      if st' = st then st else analysis_iter fn n st'
End

Definition analysis_fixpoint_def:
  analysis_fixpoint fn =
    analysis_iter fn (SUC (LENGTH (all_insts fn))) opt_analysis_init
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

(* Hint-guided transforms (per instruction id) *)

Definition transform_inst_list_hints_def:
  transform_inst_list_hints hints inst =
    let h = hint_lookup hints inst.inst_id in
      transform_inst_list h.prefer_iszero h.is_truthy h.cmp_flip inst
End

Definition transform_block_hints_def:
  transform_block_hints hints bb =
    bb with bb_instructions :=
      FLAT (MAP (transform_inst_list_hints hints) bb.bb_instructions)
End

Definition transform_function_hints_def:
  transform_function_hints hints fn =
    fn with fn_blocks :=
      MAP (transform_block_hints hints) fn.fn_blocks
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

(* Operand substitution (alist from var name to operand) *)

Definition subst_operand_op_def:
  subst_operand_op sigma op =
    case op of
      Var v =>
        (case ALOOKUP sigma v of
           SOME op' => op'
         | NONE => op)
    | _ => op
End

Definition subst_operands_op_def:
  subst_operands_op sigma ops = MAP (subst_operand_op sigma) ops
End

Definition subst_inst_op_def:
  subst_inst_op sigma inst =
    inst with inst_operands := subst_operands_op sigma inst.inst_operands
End

Definition subst_block_op_def:
  subst_block_op sigma bb =
    bb with bb_instructions := MAP (subst_inst_op sigma) bb.bb_instructions
End

Definition subst_function_op_def:
  subst_function_op sigma fn =
    fn with fn_blocks := MAP (subst_block_op sigma) fn.fn_blocks
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

Definition iszero_subst_op_def:
  iszero_subst_op fn sigma <=>
    !v op. ALOOKUP sigma v = SOME op ==> iszero_var fn v
End

Definition rewrite_iszero_chains_op_def:
  rewrite_iszero_chains_op fn fn' <=>
    ?sigma.
      iszero_subst_op fn sigma /\
      fn' = subst_function_op sigma fn
End

Definition algebraic_opt_pass_def:
  algebraic_opt_pass fn =
    let st = analysis_fixpoint fn in
      subst_function_op st.subst (transform_function_hints st.hints fn)
End

Definition algebraic_opt_transform_def:
  algebraic_opt_transform fn fn' <=> fn' = algebraic_opt_pass fn
End

Definition algebraic_opt_transform_hints_def:
  algebraic_opt_transform_hints hints sigma fn fn' <=>
    ?fn1.
      fn1 = transform_function_hints hints fn /\
      iszero_subst_op fn1 sigma /\
      fn' = subst_function_op sigma fn1
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
