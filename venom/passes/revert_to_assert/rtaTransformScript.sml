(*
 * Revert-to-Assert Transformation Definitions
 *
 * This theory defines the revert-to-assert transformation.
 * The pass converts conditional branches to revert blocks into assertions:
 *   - jnz cond @revert @else  =>  %t = iszero cond; assert %t; jmp @else
 *   - jnz cond @then @revert  =>  assert cond; jmp @then
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - is_revert_block        : Check if block is just "revert 0 0"
 *   - is_zero_revert_inst    : Check if instruction is "revert 0 0"
 *   - rewrite_jnz_then       : Rewrite jnz where then-branch is revert
 *   - rewrite_jnz_else       : Rewrite jnz where else-branch is revert
 *   - transform_block        : Transform a block's terminator if applicable
 *   - transform_function     : Transform an entire function
 *
 * HELPER DEFINITIONS:
 *   - mk_iszero_inst         : Create an ISZERO instruction
 *   - mk_assert_inst         : Create an ASSERT instruction
 *   - mk_jmp_inst            : Create a JMP instruction
 *
 * ============================================================================
 *)

Theory rtaTransform
Ancestors
  list finite_map pred_set ASCIInumbers
  venomState venomInst venomSem

(* ==========================================================================
   Revert Block Detection
   ========================================================================== *)

(* Check if an instruction is "revert 0 0" *)
Definition is_zero_revert_inst_def:
  is_zero_revert_inst inst <=>
    inst.inst_opcode = REVERT /\
    inst.inst_operands = [Lit 0w; Lit 0w]
End

(* Check if a block is a revert block (single "revert 0 0" instruction) *)
Definition is_revert_block_def:
  is_revert_block bb <=>
    case bb.bb_instructions of
      [inst] => is_zero_revert_inst inst
    | _ => F
End

(* ==========================================================================
   JNZ Pattern Detection
   ========================================================================== *)

(* Check if instruction is a JNZ *)
Definition is_jnz_inst_def:
  is_jnz_inst inst <=> inst.inst_opcode = JNZ
End

(* Get the terminator of a block *)
Definition get_terminator_def:
  get_terminator bb =
    if NULL bb.bb_instructions then NONE
    else SOME (LAST bb.bb_instructions)
End

(* Get JNZ operands: (cond, then_label, else_label) *)
Definition get_jnz_operands_def:
  get_jnz_operands inst =
    case inst.inst_operands of
      [cond_op; Label then_lbl; Label else_lbl] =>
        SOME (cond_op, then_lbl, else_lbl)
    | _ => NONE
End

(* ==========================================================================
   Instruction Constructors
   ========================================================================== *)

(* Create an ISZERO instruction *)
Definition mk_iszero_inst_def:
  mk_iszero_inst id input output =
    <| inst_id := id;
       inst_opcode := ISZERO;
       inst_operands := [input];
       inst_outputs := [output] |>
End

(* Create an ASSERT instruction *)
Definition mk_assert_inst_def:
  mk_assert_inst id cond_op =
    <| inst_id := id;
       inst_opcode := ASSERT;
       inst_operands := [cond_op];
       inst_outputs := [] |>
End

(* Create a JMP instruction *)
Definition mk_jmp_inst_def:
  mk_jmp_inst id target =
    <| inst_id := id;
       inst_opcode := JMP;
       inst_operands := [Label target];
       inst_outputs := [] |>
End

(* ==========================================================================
   Block Transformation
   ========================================================================== *)

(* Rewrite a block when its JNZ then-branch goes to revert:
   jnz cond @revert @else => iszero cond -> t; assert t; jmp @else

   Takes: the block, new variable name for iszero result, fresh instruction IDs *)
Definition rewrite_jnz_then_revert_def:
  rewrite_jnz_then_revert bb new_var id1 id2 id3 =
    case get_terminator bb of
      NONE => NONE
    | SOME term =>
        case get_jnz_operands term of
          NONE => NONE
        | SOME (cond_op, then_lbl, else_lbl) =>
            let iszero_inst = mk_iszero_inst id1 cond_op new_var in
            let assert_inst = mk_assert_inst id2 (Var new_var) in
            let jmp_inst = mk_jmp_inst id3 else_lbl in
            let new_insts = FRONT bb.bb_instructions ++
                            [iszero_inst; assert_inst; jmp_inst] in
            SOME (bb with bb_instructions := new_insts)
End

(* Rewrite a block when its JNZ else-branch goes to revert:
   jnz cond @then @revert => assert cond; jmp @then *)
Definition rewrite_jnz_else_revert_def:
  rewrite_jnz_else_revert bb id1 id2 =
    case get_terminator bb of
      NONE => NONE
    | SOME term =>
        case get_jnz_operands term of
          NONE => NONE
        | SOME (cond_op, then_lbl, else_lbl) =>
            let assert_inst = mk_assert_inst id1 cond_op in
            let jmp_inst = mk_jmp_inst id2 then_lbl in
            let new_insts = FRONT bb.bb_instructions ++
                            [assert_inst; jmp_inst] in
            SOME (bb with bb_instructions := new_insts)
End

(* ==========================================================================
   CFG Analysis Helpers
   ========================================================================== *)

(* Find a block by label *)
Definition find_block_def:
  find_block lbl [] = NONE /\
  find_block lbl (bb::bbs) =
    if bb.bb_label = lbl then SOME bb
    else find_block lbl bbs
End

(* Check if a label refers to a revert block in the function *)
Definition is_revert_label_def:
  is_revert_label lbl blocks =
    case find_block lbl blocks of
      NONE => F
    | SOME bb => is_revert_block bb
End

(* ==========================================================================
   Function-Level Transformation
   ========================================================================== *)

(* Transform a single block given the list of all blocks and ID state.
   Returns (transformed_block, next_id) *)
Definition transform_block_def:
  transform_block blocks next_id bb =
    case get_terminator bb of
      NONE => (bb, next_id)
    | SOME term =>
        if ~is_jnz_inst term then (bb, next_id)
        else
          case get_jnz_operands term of
            NONE => (bb, next_id)
          | SOME (cond_op, then_lbl, else_lbl) =>
              (* Check if then-branch is revert block *)
              if is_revert_label then_lbl blocks then
                let new_var = "rta_" ++ num_to_dec_string next_id in
                case rewrite_jnz_then_revert bb new_var next_id (next_id + 1) (next_id + 2) of
                  NONE => (bb, next_id)
                | SOME bb' => (bb', next_id + 3)
              (* Check if else-branch is revert block *)
              else if is_revert_label else_lbl blocks then
                case rewrite_jnz_else_revert bb next_id (next_id + 1) of
                  NONE => (bb, next_id)
                | SOME bb' => (bb', next_id + 2)
              else (bb, next_id)
End

(* Transform all blocks, threading the ID state *)
Definition transform_blocks_def:
  transform_blocks blocks next_id [] = ([], next_id) /\
  transform_blocks blocks next_id (bb::bbs) =
    let (bb', next_id') = transform_block blocks next_id bb in
    let (bbs', next_id'') = transform_blocks blocks next_id' bbs in
    (bb'::bbs', next_id'')
End

(* TOP-LEVEL: Transform a function *)
Definition transform_function_def:
  transform_function fn =
    let (blocks', _) = transform_blocks fn.fn_blocks 0 fn.fn_blocks in
    fn with fn_blocks := blocks'
End

(* TOP-LEVEL: Transform a context (all functions) *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Basic Properties
   ========================================================================== *)

(* Transform preserves block labels *)
Theorem transform_block_label:
  !blocks next_id bb bb' next_id'.
    transform_block blocks next_id bb = (bb', next_id') ==>
    bb'.bb_label = bb.bb_label
Proof
  rw[transform_block_def] >>
  gvs[AllCaseEqs()] >>
  fs[rewrite_jnz_then_revert_def, rewrite_jnz_else_revert_def] >>
  gvs[AllCaseEqs()]
QED

(* Transform preserves function name *)
Theorem transform_function_name:
  !fn. (transform_function fn).fn_name = fn.fn_name
Proof
  rw[transform_function_def] >>
  Cases_on `transform_blocks fn.fn_blocks 0 fn.fn_blocks` >> simp[]
QED

(* Lookup block is preserved under find_block (same as lookup_block) *)
Theorem find_block_eq_lookup:
  !lbl blocks. find_block lbl blocks = lookup_block lbl blocks
Proof
  Induct_on `blocks` >> simp[find_block_def, lookup_block_def]
QED
