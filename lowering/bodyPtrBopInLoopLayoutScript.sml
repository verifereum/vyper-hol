Theory bodyPtrBopInLoopLayout
Ancestors exprLowering context compileEnv emitHelper list

Theorem membership_loop_layout:
  !needle arr len stride skip imm loc is_in sa
    entry cond body found incr exit result idx done product offset addr elem
    matched next neg delta opc old_bb entry_bb cond_bb body_bb found_bb incr_bb.
    delta = (if 0 < skip then 1 else 0) /\
    opc = (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
      LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD) /\
    entry = fresh_label_output "in_entry" sa.cs_next_label /\
    cond = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    body = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    found = fresh_label_output "in_found" (sa.cs_next_label+3) /\
    incr = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
    exit = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
    result = "%" ++ toString sa.cs_next_var /\
    idx = "%" ++ toString (sa.cs_next_var+1) /\
    done = "%" ++ toString (sa.cs_next_var+2) /\
    product = "%" ++ toString (sa.cs_next_var+3) /\
    offset = (if 0 < skip then "%" ++ toString (sa.cs_next_var+4) else product) /\
    addr = "%" ++ toString (sa.cs_next_var+4+delta) /\
    elem = "%" ++ toString (sa.cs_next_var+5+delta) /\
    matched = "%" ++ toString (sa.cs_next_var+6+delta) /\
    next = "%" ++ toString (sa.cs_next_var+7+delta) /\
    neg = "%" ++ toString (sa.cs_next_var+8+delta) /\
    old_bb = <|bb_label := sa.cs_current_bb; bb_instructions :=
      sa.cs_current_insts ++ [mk_inst sa.cs_next_id JMP [Label entry] []]|> /\
    entry_bb = <|bb_label := entry; bb_instructions :=
      [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
       mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result];
       mk_inst (sa.cs_next_id+3) JMP [Label cond] []]|> /\
    cond_bb = <|bb_label := cond; bb_instructions :=
      [mk_inst (sa.cs_next_id+4) EQ [Var idx;len] [done];
       mk_inst (sa.cs_next_id+5) JNZ [Var done;Label exit;Label body] []]|> /\
    body_bb = <|bb_label := body; bb_instructions :=
      [mk_inst (sa.cs_next_id+6) MUL [Var idx;Lit (n2w stride)] [product]] ++
      (if 0 < skip then
        [mk_inst (sa.cs_next_id+7) ADD [Lit (n2w skip);Var product] [offset]]
       else []) ++
      [mk_inst (sa.cs_next_id+7+delta) ADD [arr;Var offset] [addr];
       mk_inst (sa.cs_next_id+8+delta) opc [Var addr] [elem];
       mk_inst (sa.cs_next_id+9+delta) EQ [Var elem;needle] [matched];
       mk_inst (sa.cs_next_id+10+delta) JNZ
         [Var matched;Label found;Label incr] []]|> /\
    found_bb = <|bb_label := found; bb_instructions :=
      [mk_inst (sa.cs_next_id+11+delta) ASSIGN [Lit 1w] [result];
       mk_inst (sa.cs_next_id+12+delta) JMP [Label exit] []]|> /\
    incr_bb = <|bb_label := incr; bb_instructions :=
      [mk_inst (sa.cs_next_id+13+delta) ADD [Var idx;Lit 1w] [next];
       mk_inst (sa.cs_next_id+14+delta) ASSIGN [Var next] [idx];
       mk_inst (sa.cs_next_id+15+delta) JMP [Label cond] []]|> ==>
    compile_array_membership_loop needle arr len stride skip
      (compile_ptr_load F imm loc) is_in sa =
    ((if is_in then Var result else Var neg), sa with <|
      cs_next_label := sa.cs_next_label+6;
      cs_next_var := sa.cs_next_var+8+delta+(if is_in then 0 else 1);
      cs_next_id := sa.cs_next_id+16+delta+(if is_in then 0 else 1);
      cs_blocks := [incr_bb;found_bb;body_bb;cond_bb;entry_bb;old_bb] ++ sa.cs_blocks;
      cs_current_bb := exit;
      cs_current_insts := (if is_in then [] else
        [mk_inst (sa.cs_next_id+16+delta) ISZERO [Var result] [neg]]) |>)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `loc` >> Cases_on `0 < skip` >> Cases_on `is_in` >>
  simp[] >>
  simp[Once compile_array_membership_loop_def, compile_ptr_load_def,
       compile_imm_load_word_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_label_def] >>
  CONV_TAC (LAND_CONV (RAND_CONV
    (SIMP_CONV (srw_ss())
      [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >>
  simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [new_block_def]))) >>
  simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss())
    [emit_inst_def, fresh_id_def, emit_def, comp_bind_def, comp_return_def]))) >>
  simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (RAND_CONV (SIMP_CONV (srw_ss()) [emit_inst_def, emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def, new_block_def]))) >> simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC] >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
    [emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
     comp_return_def, fresh_var_def, fresh_id_def, emit_def])) >>
  simp[APPEND_ASSOC, arithmeticTheory.ADD_ASSOC]
QED
