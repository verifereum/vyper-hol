Theory bodyPtrBopInBoundedLayout
Ancestors bodyPtrBopInLoopContract exprLowering context compileEnv emitHelper
  fragExec rich_list list venomExecSemantics venomInst ptrDiscipline

val membership_loop_unfold_ths =
  [Once compile_array_membership_loop_def, comp_bind_def,
   comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_label_def,
   emit_inst_def, emit_op_def, fresh_id_def, emit_def, new_block_def];

(* The loop's layout for any loader that emits load_code and leaves its result in elem. *)
Theorem membership_loop_layout_load[local]:
  !needle arr len stride skip loader width load_code cap is_in sa
    entry cond body found incr exit result idx inv valid done product offset addr elem
    matched next neg delta old_bb entry_bb cond_bb body_bb found_bb incr_bb.
    (!cs. cs.cs_next_var = sa.cs_next_var+7+delta /\
          cs.cs_next_id = sa.cs_next_id+11+delta ==>
          loader (Var addr) cs =
          (Var elem, cs with <|cs_next_var := sa.cs_next_var+7+delta+width;
             cs_next_id := sa.cs_next_id+11+delta+width;
             cs_current_insts := cs.cs_current_insts ++ load_code|>)) /\
    delta = (if 0 < skip then 1 else 0) /\
    entry = fresh_label_output "in_entry" sa.cs_next_label /\
    cond = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    body = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    found = fresh_label_output "in_found" (sa.cs_next_label+3) /\
    incr = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
    exit = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
    result = "%" ++ toString sa.cs_next_var /\
    idx = "%" ++ toString (sa.cs_next_var+1) /\
    inv = "%" ++ toString (sa.cs_next_var+2) /\
    valid = "%" ++ toString (sa.cs_next_var+3) /\
    done = "%" ++ toString (sa.cs_next_var+4) /\
    product = "%" ++ toString (sa.cs_next_var+5) /\
    offset = (if 0 < skip then "%" ++ toString (sa.cs_next_var+6) else product) /\
    addr = "%" ++ toString (sa.cs_next_var+6+delta) /\
    elem = "%" ++ toString (sa.cs_next_var+6+delta+width) /\
    matched = "%" ++ toString (sa.cs_next_var+7+delta+width) /\
    next = "%" ++ toString (sa.cs_next_var+8+delta+width) /\
    neg = "%" ++ toString (sa.cs_next_var+9+delta+width) /\
    old_bb = <|bb_label := sa.cs_current_bb; bb_instructions :=
      sa.cs_current_insts ++ [mk_inst sa.cs_next_id JMP [Label entry] []]|> /\
    entry_bb = <|bb_label := entry; bb_instructions :=
      [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
       mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result];
       mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)] [inv];
       mk_inst (sa.cs_next_id+4) ISZERO [Var inv] [valid];
       mk_inst (sa.cs_next_id+5) ASSERT [Var valid] [];
       mk_inst (sa.cs_next_id+6) JMP [Label cond] []]|> /\
    cond_bb = <|bb_label := cond; bb_instructions :=
      [mk_inst (sa.cs_next_id+7) EQ [Var idx;len] [done];
       mk_inst (sa.cs_next_id+8) JNZ [Var done;Label exit;Label body] []]|> /\
    body_bb = <|bb_label := body; bb_instructions :=
      [mk_inst (sa.cs_next_id+9) MUL [Var idx;Lit (n2w stride)] [product]] ++
      (if 0 < skip then
        [mk_inst (sa.cs_next_id+10) ADD [Lit (n2w skip);Var product] [offset]]
       else []) ++
      [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [addr]] ++ load_code ++
      [mk_inst (sa.cs_next_id+11+delta+width) EQ [Var elem;needle] [matched];
       mk_inst (sa.cs_next_id+12+delta+width) JNZ
         [Var matched;Label found;Label incr] []]|> /\
    found_bb = <|bb_label := found; bb_instructions :=
      [mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Lit 1w] [result];
       mk_inst (sa.cs_next_id+14+delta+width) JMP [Label exit] []]|> /\
    incr_bb = <|bb_label := incr; bb_instructions :=
      [mk_inst (sa.cs_next_id+15+delta+width) ADD [Var idx;Lit 1w] [next];
       mk_inst (sa.cs_next_id+16+delta+width) ASSIGN [Var next] [idx];
       mk_inst (sa.cs_next_id+17+delta+width) JMP [Label cond] []]|> ==>
    compile_array_membership_loop needle arr len stride skip
      loader (SOME cap) is_in sa =
    ((if is_in then Var result else Var neg), sa with <|
      cs_next_label := sa.cs_next_label+6;
      cs_next_var := sa.cs_next_var+9+delta+width+(if is_in then 0 else 1);
      cs_next_id := sa.cs_next_id+18+delta+width+(if is_in then 0 else 1);
      cs_blocks := [incr_bb;found_bb;body_bb;cond_bb;entry_bb;old_bb] ++ sa.cs_blocks;
      cs_current_bb := exit;
      cs_current_insts := (if is_in then [] else
        [mk_inst (sa.cs_next_id+18+delta+width) ISZERO [Var result] [neg]]) |>)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `0 < skip` >> Cases_on `is_in` >> gvs[]
  >- (simp membership_loop_unfold_ths >> rewrite_tac[GSYM APPEND_ASSOC, APPEND])
  >- (simp membership_loop_unfold_ths >> rewrite_tac[GSYM APPEND_ASSOC, APPEND])
  >- (simp membership_loop_unfold_ths >> rewrite_tac[GSYM APPEND_ASSOC, APPEND])
  >- (simp membership_loop_unfold_ths >> rewrite_tac[GSYM APPEND_ASSOC, APPEND])
QED

(* The two bound-check temporaries shift names by two, instructions by three. *)
Theorem membership_bounded_loop_layout:
  !needle arr len stride skip is_ctor imm loc cap is_in sa
    entry cond body found incr exit result idx inv valid done product offset addr elem
    matched next neg delta width opc staged load_code old_bb entry_bb cond_bb body_bb found_bb incr_bb.
    delta = (if 0 < skip then 1 else 0) /\
    width = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) /\
    opc = (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
      LocTransient => TLOAD | LocCalldata => CALLDATALOAD |
      LocCode => if is_ctor then ILOAD else DLOAD) /\
    staged = "%" ++ toString (sa.cs_next_var+7+delta) /\
    load_code = (if is_ctor /\ loc = LocCode /\ IS_SOME imm then
      [mk_inst (sa.cs_next_id+11+delta) ADD [Var addr;THE imm] [staged];
       mk_inst (sa.cs_next_id+12+delta) ILOAD [Var staged] [elem]]
      else [mk_inst (sa.cs_next_id+11+delta) opc [Var addr] [elem]]) /\
    entry = fresh_label_output "in_entry" sa.cs_next_label /\
    cond = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    body = fresh_label_output "in_body" (sa.cs_next_label+2) /\
    found = fresh_label_output "in_found" (sa.cs_next_label+3) /\
    incr = fresh_label_output "in_incr" (sa.cs_next_label+4) /\
    exit = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
    result = "%" ++ toString sa.cs_next_var /\
    idx = "%" ++ toString (sa.cs_next_var+1) /\
    inv = "%" ++ toString (sa.cs_next_var+2) /\
    valid = "%" ++ toString (sa.cs_next_var+3) /\
    done = "%" ++ toString (sa.cs_next_var+4) /\
    product = "%" ++ toString (sa.cs_next_var+5) /\
    offset = (if 0 < skip then "%" ++ toString (sa.cs_next_var+6) else product) /\
    addr = "%" ++ toString (sa.cs_next_var+6+delta) /\
    elem = "%" ++ toString (sa.cs_next_var+6+delta+width) /\
    matched = "%" ++ toString (sa.cs_next_var+7+delta+width) /\
    next = "%" ++ toString (sa.cs_next_var+8+delta+width) /\
    neg = "%" ++ toString (sa.cs_next_var+9+delta+width) /\
    old_bb = <|bb_label := sa.cs_current_bb; bb_instructions :=
      sa.cs_current_insts ++ [mk_inst sa.cs_next_id JMP [Label entry] []]|> /\
    entry_bb = <|bb_label := entry; bb_instructions :=
      [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [idx];
       mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w] [result];
       mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)] [inv];
       mk_inst (sa.cs_next_id+4) ISZERO [Var inv] [valid];
       mk_inst (sa.cs_next_id+5) ASSERT [Var valid] [];
       mk_inst (sa.cs_next_id+6) JMP [Label cond] []]|> /\
    cond_bb = <|bb_label := cond; bb_instructions :=
      [mk_inst (sa.cs_next_id+7) EQ [Var idx;len] [done];
       mk_inst (sa.cs_next_id+8) JNZ [Var done;Label exit;Label body] []]|> /\
    body_bb = <|bb_label := body; bb_instructions :=
      [mk_inst (sa.cs_next_id+9) MUL [Var idx;Lit (n2w stride)] [product]] ++
      (if 0 < skip then
        [mk_inst (sa.cs_next_id+10) ADD [Lit (n2w skip);Var product] [offset]]
       else []) ++
      [mk_inst (sa.cs_next_id+10+delta) ADD [arr;Var offset] [addr]] ++ load_code ++
      [mk_inst (sa.cs_next_id+11+delta+width) EQ [Var elem;needle] [matched];
       mk_inst (sa.cs_next_id+12+delta+width) JNZ
         [Var matched;Label found;Label incr] []]|> /\
    found_bb = <|bb_label := found; bb_instructions :=
      [mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Lit 1w] [result];
       mk_inst (sa.cs_next_id+14+delta+width) JMP [Label exit] []]|> /\
    incr_bb = <|bb_label := incr; bb_instructions :=
      [mk_inst (sa.cs_next_id+15+delta+width) ADD [Var idx;Lit 1w] [next];
       mk_inst (sa.cs_next_id+16+delta+width) ASSIGN [Var next] [idx];
       mk_inst (sa.cs_next_id+17+delta+width) JMP [Label cond] []]|> ==>
    compile_array_membership_loop needle arr len stride skip
      (compile_ptr_load is_ctor imm loc) (SOME cap) is_in sa =
    ((if is_in then Var result else Var neg), sa with <|
      cs_next_label := sa.cs_next_label+6;
      cs_next_var := sa.cs_next_var+9+delta+width+(if is_in then 0 else 1);
      cs_next_id := sa.cs_next_id+18+delta+width+(if is_in then 0 else 1);
      cs_blocks := [incr_bb;found_bb;body_bb;cond_bb;entry_bb;old_bb] ++ sa.cs_blocks;
      cs_current_bb := exit;
      cs_current_insts := (if is_in then [] else
        [mk_inst (sa.cs_next_id+18+delta+width) ISZERO [Var result] [neg]]) |>)
Proof
  rpt gen_tac >> strip_tac >>
  `!cs. cs.cs_next_var = sa.cs_next_var+7+delta /\
        cs.cs_next_id = sa.cs_next_id+11+delta ==>
        compile_ptr_load is_ctor imm loc (Var addr) cs =
        (Var elem, cs with <|cs_next_var := sa.cs_next_var+7+delta+width;
           cs_next_id := sa.cs_next_id+11+delta+width;
           cs_current_insts := cs.cs_current_insts ++ load_code|>)` by
    (rpt strip_tac >> gvs[] >> Cases_on `loc` >>
     simp[compile_ptr_load_def, compile_imm_load_word_def, emit_op_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >>
     Cases_on `is_ctor` >> Cases_on `imm` >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_id_def,
          fresh_var_def, emit_def] >>
     rewrite_tac[GSYM APPEND_ASSOC, APPEND]) >>
  drule_all membership_loop_layout_load >> simp[]
QED

(* The operand is explicit so both bounded and unbounded frontiers use one interface. *)
Definition membership_element_load_contract_def:
  membership_element_load_contract D ctx fn PG sa compare_pc elem
      (ws:bytes32 list) G0 tn0 s0 <=>
    !i G tn s. i < LENGTH ws /\
      membership_loop_frame sa G0 tn0 s0 G tn s /\
      membership_loop_registers sa i 0w G tn s /\
      s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
      s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
      ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        membership_loop_frame sa G0 tn0 s0 G' tn' t /\
        membership_loop_registers sa i 0w G' tn' t /\
        t.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
        t.vs_inst_idx = compare_pc /\ ~t.vs_halted /\
        eval_operand elem t = SOME (EL i ws) /\
        op_prov G' elem = NONE /\ op_taint tn' elem = {}
End

Theorem membership_bounded_loop_extends:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) ==>
  cs_extends sa sb
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  simp[cs_extends_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_length_header_layout:
  compile_ptr_load F imm loc arr sa = (len,sb) /\
  opc = (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
    LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD) ==>
  len = Var ("%" ++ toString sa.cs_next_var) /\
  sb = sa with <|
    cs_next_var := sa.cs_next_var+1;
    cs_next_id := sa.cs_next_id+1;
    cs_current_insts := sa.cs_current_insts ++
      [mk_inst sa.cs_next_id opc [arr] ["%" ++ toString sa.cs_next_var]] |>
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, compile_imm_load_word_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_inst_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem membership_length_header_extends:
  compile_ptr_load F imm loc arr sa = (len,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule (SRULE [] (GEN_ALL membership_length_header_layout)) >>
  strip_tac >> gvs[] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]
QED

Theorem membership_length_header_code:
  compile_ptr_load F imm loc arr sa = (len,sb) /\ fn_has_code sa sb fn ==>
  len = Var ("%" ++ toString sa.cs_next_var) /\
  ?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id
        (case loc of LocMemory => MLOAD | LocStorage => SLOAD |
         LocTransient => TLOAD | LocCalldata => CALLDATALOAD | LocCode => DLOAD)
        [arr] ["%" ++ toString sa.cs_next_var])
Proof
  strip_tac >> drule (SRULE [] (GEN_ALL membership_length_header_layout)) >>
  strip_tac >> gvs[] >> fs[fn_has_code_def, IS_PREFIX_APPEND] >>
  fs[venomInstTheory.get_instruction_def, APPEND_ASSOC, EL_APPEND_EQN]
QED

Theorem membership_bounded_loop_exit:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) ==>
  sb.cs_current_bb = fresh_label_output "in_exit" (sa.cs_next_label+5) /\
  LENGTH sb.cs_current_insts = (if is_in then 0 else 1) /\
  op = Var ("%" ++ toString
    (sa.cs_next_var + (if is_in then 0 else 9 + (if 0 < skip then 1 else 0) +
      (if ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1))))
Proof
  simp[SRULE [] membership_bounded_loop_layout] >> strip_tac >> gvs[] >>
  Cases_on `is_in` >> simp[]
QED

Theorem membership_bounded_closed_nonphi:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  (lbl = fresh_label_output "in_entry" sa.cs_next_label \/
   lbl = fresh_label_output "in_cond" (sa.cs_next_label+1) \/
   lbl = fresh_label_output "in_body" (sa.cs_next_label+2) \/
   lbl = fresh_label_output "in_found" (sa.cs_next_label+3) \/
   lbl = fresh_label_output "in_incr" (sa.cs_next_label+4)) /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem membership_bounded_notin_exit_ghost:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sb.cs_current_bb ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def] >>
  Cases_on `bb.bb_instructions` >> gvs[] >>
  irule typedCopyArrayPtrTheory.entry_ghost_no_phi >> qexists_tac `bb` >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def, venomInstTheory.mk_inst_def]
QED

Theorem membership_bounded_condition_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?bb. lookup_block (fresh_label_output "in_cond" (sa.cs_next_label+1))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+7) EQ
         [Var ("%" ++ toString (sa.cs_next_var+1));len]
         ["%" ++ toString (sa.cs_next_var+4)];
       mk_inst (sa.cs_next_id+8) JNZ
         [Var ("%" ++ toString (sa.cs_next_var+4));
          Label (fresh_label_output "in_exit" (sa.cs_next_label+5));
          Label (fresh_label_output "in_body" (sa.cs_next_label+2))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_bounded_compare_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_body" (sa.cs_next_label+2))
         fn.fn_blocks = SOME bb /\
    DROP (2+delta+width) bb.bb_instructions =
      [mk_inst (sa.cs_next_id+11+delta+width) EQ
         [Var ("%" ++ toString (sa.cs_next_var+6+delta+width));needle]
         ["%" ++ toString (sa.cs_next_var+7+delta+width)];
       mk_inst (sa.cs_next_id+12+delta+width) JNZ
         [Var ("%" ++ toString (sa.cs_next_var+7+delta+width));
          Label (fresh_label_output "in_found" (sa.cs_next_label+3));
          Label (fresh_label_output "in_incr" (sa.cs_next_label+4))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `0 < skip` >>
  Cases_on `ctor /\ loc = LocCode /\ IS_SOME imm` >> simp[]
QED

Theorem membership_bounded_increment_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_incr" (sa.cs_next_label+4))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+15+delta+width) ADD
         [Var ("%" ++ toString (sa.cs_next_var+1));Lit 1w]
         ["%" ++ toString (sa.cs_next_var+8+delta+width)];
       mk_inst (sa.cs_next_id+16+delta+width) ASSIGN
         [Var ("%" ++ toString (sa.cs_next_var+8+delta+width))]
         ["%" ++ toString (sa.cs_next_var+1)];
       mk_inst (sa.cs_next_id+17+delta+width) JMP
         [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_bounded_notin_exit_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) F sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst (sa.cs_next_id+18+delta+width) ISZERO
         [Var ("%" ++ toString sa.cs_next_var)]
         ["%" ++ toString (sa.cs_next_var+9+delta+width)]]
      bb.bb_instructions
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_bounded_found_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\
  delta = (if 0 < skip then 1 else 0) /\
  width = (if ctor /\ loc = LocCode /\ IS_SOME imm then 2 else 1) ==>
  ?bb. lookup_block (fresh_label_output "in_found" (sa.cs_next_label+3))
         fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      [mk_inst (sa.cs_next_id+13+delta+width) ASSIGN [Lit 1w]
         ["%" ++ toString sa.cs_next_var];
       mk_inst (sa.cs_next_id+14+delta+width) JMP
         [Label (fresh_label_output "in_exit" (sa.cs_next_label+5))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem membership_element_load_contract_empty[simp]:
  membership_element_load_contract D ctx fn PG sa pc elem [] G tn s
Proof
  simp[membership_element_load_contract_def]
QED

Theorem membership_bounded_entry_lookup:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load ctor imm loc) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn ==>
  ?old_bb entry_bb.
    lookup_block sa.cs_current_bb fn.fn_blocks = SOME old_bb /\
    get_instruction old_bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id JMP
        [Label (fresh_label_output "in_entry" sa.cs_next_label)] []) /\
    lookup_block (fresh_label_output "in_entry" sa.cs_next_label)
      fn.fn_blocks = SOME entry_bb /\
    entry_bb.bb_instructions =
      [mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w]
         ["%" ++ toString (sa.cs_next_var+1)];
       mk_inst (sa.cs_next_id+2) ASSIGN [Lit 0w]
         ["%" ++ toString sa.cs_next_var];
       mk_inst (sa.cs_next_id+3) GT [len;Lit (n2w cap)]
         ["%" ++ toString (sa.cs_next_var+2)];
       mk_inst (sa.cs_next_id+4) ISZERO
         [Var ("%" ++ toString (sa.cs_next_var+2))]
         ["%" ++ toString (sa.cs_next_var+3)];
       mk_inst (sa.cs_next_id+5) ASSERT
         [Var ("%" ++ toString (sa.cs_next_var+3))] [];
       mk_inst (sa.cs_next_id+6) JMP
         [Label (fresh_label_output "in_cond" (sa.cs_next_label+1))] []]
Proof
  strip_tac >> gvs[SRULE [] membership_bounded_loop_layout] >>
  fs[fn_has_code_def, emitted_blocks_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[get_instruction_def, EL_APPEND_EQN] >>
  goal_assum (drule_at Any) >> simp[]
QED
