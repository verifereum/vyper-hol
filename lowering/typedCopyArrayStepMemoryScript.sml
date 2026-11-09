(* Memory-safe execution of the typed-copy array increment and backedge. *)
Theory typedCopyArrayStepMemory
Ancestors
  typedCopyLoopPathMemory typedMemoryCopy
  stmtForRangeMemoryParts fragGasSeqMem fragGasPathMem fragExecMem
  exprLoweringProps venomExecSemantics venomInst venomState instMemFrontier
  words list rich_list finite_map arithmetic memSafeRun

Theorem typed_copy_backedge_path_mem[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = pre ++
    [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
     mk_inst (id+1) ASSIGN [Var tmp] [ctr];
     mk_inst (id+2) JMP [Label header] []] /\
  s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\
  lookup_var ctr s = SOME (n2w k) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to header (update_var ctr (n2w (k+1))
      (update_var tmp (n2w (k+1)) s))))
Proof
  strip_tac >>
  qabbrev_tac `code = [mk_inst id ADD [Var ctr; Lit 1w] [tmp];
    mk_inst (id+1) ASSIGN [Var tmp] [ctr]]` >>
  qabbrev_tac `u = update_var ctr (n2w (k+1))
    (update_var tmp (n2w (k+1)) s)` >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s` by
    simp[Abbr `code`, Abbr `u`, run_inst_seq_def, run_inst_seq_mem_ok_def,
      step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      word_add_n2w, inst_dload_in_section_def, below_frontier_no_ranges,
      mk_inst_def] >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH pre + 2))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def, DROP_LENGTH_APPEND]) >>
  `gas_path_mem ctx func (u with vs_inst_idx := LENGTH pre + 2) 0
    (OK (jump_to header (u with vs_inst_idx := LENGTH pre + 2)))` by
    (irule for_range_jump_at_zero_path_mem >>
     conj_tac >- simp[Abbr `u`, update_var_def] >>
     qexistsl_tac [`bb`, `mk_inst (id+2) JMP [Label header] []`] >>
     simp[Abbr `u`, update_var_def, get_instruction_def, EL_APPEND_EQN,
       mk_inst_def, is_terminator_def, below_frontier_no_ranges,
       inst_dload_in_section_def, step_inst_base_opcode_eqs]) >>
  `jump_to header (u with vs_inst_idx := LENGTH pre + 2) = jump_to header u` by
    simp[jump_to_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

Theorem typed_copy_array_addresses_run[local]:
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so; doff; sp; dp]) /\
  (!x. MEM x [so; doff; sp; dp] ==> ~not_fresh_at sa x) /\
  lookup_var ctr s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw ==>
  let code =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]];
      u = update_var dp (dw + n2w (k * ds))
        (update_var sp (sw + n2w (k * ss))
          (update_var doff (n2w (k * ds)) (update_var so (n2w (k * ss)) s))) in
  run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
  typed_copy_state_frame sa off len s u /\
  u.vs_memory = s.vs_memory /\
  lookup_var ctr u = SOME (n2w k) /\
  eval_operand (Var sp) u = SOME (sw + n2w (k * ss)) /\
  eval_operand (Var dp) u = SOME (dw + n2w (k * ds))
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> so /\ x <> doff /\ x <> sp /\ x <> dp` by
    (gvs[] >> metis_tac[]) >>
  Cases_on `src` >> Cases_on `dst` >>
  gvs[eval_operand_def, ALL_DISTINCT, MEM, lookup_var_def] >>
  simp[LET_THM] >>
  (conj_tac >-
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, exec_pure2_def,
      eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      word_mul_n2w]) >>
  (conj_tac >-
    simp[run_inst_seq_mem_ok_def, run_inst_seq_def,
      step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE,
      word_mul_n2w, inst_dload_in_section_def, below_frontier_no_ranges,
      mk_inst_def]) >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality]
QED

Theorem typed_copy_array_addresses_path_mem[local]:
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  (!x. src = Var x \/ dst = Var x ==> ~MEM x [so; doff; sp; dp]) /\
  (!x. MEM x [so; doff; sp; dp] ==> ~not_fresh_at sa x) /\
  lookup_var ctr s = SOME (n2w k) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_state_frame sa off len s t /\ t.vs_memory = s.vs_memory /\
    lookup_var ctr t = SOME (n2w k) /\
    eval_operand (Var sp) t = SOME (sw + n2w (k * ss)) /\
    eval_operand (Var dp) t = SOME (dw + n2w (k * ds)) /\
    t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + 4 /\ ~t.vs_halted
Proof
  strip_tac >>
  qabbrev_tac `code =
    [mk_inst id MUL [Var ctr; Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr; Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [src; Var so] [sp];
     mk_inst (id+3) ADD [dst; Var doff] [dp]]` >>
  qabbrev_tac `u = update_var dp (dw + n2w (k * ds))
    (update_var sp (sw + n2w (k * ss))
      (update_var doff (n2w (k * ds)) (update_var so (n2w (k * ss)) s)))` >>
  `run_inst_seq code s = OK u /\ run_inst_seq_mem_ok code s /\
   typed_copy_state_frame sa off len s u /\ u.vs_memory = s.vs_memory /\
   lookup_var ctr u = SOME (n2w k) /\
   eval_operand (Var sp) u = SOME (sw + n2w (k * ss)) /\
   eval_operand (Var dp) u = SOME (dw + n2w (k * ds))` by
    (unabbrev_all_tac >>
     mp_tac (SRULE [LET_THM] typed_copy_array_addresses_run) >>
     (impl_tac >- (gvs[ALL_DISTINCT, MEM] >> metis_tac[])) >> disch_then ACCEPT_TAC) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := s.vs_inst_idx + 4))` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_path_mem >>
     disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
     simp[Abbr `code`, mk_inst_def, is_terminator_def]) >>
  qexists_tac `u with vs_inst_idx := s.vs_inst_idx + 4` >>
  gvs[eval_operand_def, lookup_var_def, typed_copy_state_frame_def] >>
  simp[Abbr `u`, update_var_def]
QED

(* The header and increment change only compiler-fresh control variables. *)
Theorem typed_copy_control_pair_frame[local]:
  ~not_fresh_at sa x /\ ~not_fresh_at sa y ==>
  typed_copy_state_frame sa off len s
    (jump_to lbl (update_var y yw (update_var x xw s)))
Proof
  strip_tac >> irule typed_copy_state_frame_jump >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def,
    update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    venom_state_component_equality] >>
  metis_tac[]
QED

Theorem typed_copy_array_entry_path_mem[local]:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
  (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at a x) /\
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  k < N /\ N < dimword (:256) /\ ~s.vs_halted /\
  s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME test /\
  test.bb_instructions =
    [mk_inst hid LT [Var ctr; Lit (n2w N)] [lt];
     mk_inst (hid+1) ISZERO [Var lt] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_block body_lbl func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst aid MUL [Var ctr; Lit (n2w (type_memory_size stv))] [so];
     mk_inst (aid+1) MUL [Var ctr; Lit (n2w (type_memory_size dtv))] [doff];
     mk_inst (aid+2) ADD [src; Var so] [sp];
     mk_inst (aid+3) ADD [dst; Var doff] [dp]] bb.bb_instructions ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k u /\
    typed_copy_state_frame a off len s u /\ u.vs_memory = s.vs_memory /\
    eval_operand (Var sp) u = SOME (sw + n2w (k * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (k * type_memory_size dtv)) /\
    u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 4 /\ ~u.vs_halted
Proof
  strip_tac >>
  `lookup_var ctr s = SOME (n2w k) /\ k <= N /\
   eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw` by
    gvs[typed_copy_index_inv_def] >>
  drule_all typed_copy_loop_header_path_mem >>
  simp[] >> strip_tac >>
  qabbrev_tac `h = jump_to body_lbl
    (update_var done (bool_to_word F) (update_var lt (bool_to_word T) s))` >>
  `typed_copy_state_frame a off len s h` by
    (unabbrev_all_tac >> irule typed_copy_control_pair_frame >> gvs[MEM]) >>
  `lookup_var ctr h = SOME (n2w k) /\
   eval_operand src h = SOME sw /\ eval_operand dst h = SOME dw` by
    metis_tac[typed_copy_state_frame_counter, typed_copy_state_frame_operand] >>
  `?u. gas_path_mem ctx func h 0 (OK u) /\
    typed_copy_state_frame a off len h u /\ u.vs_memory = h.vs_memory /\
    lookup_var ctr u = SOME (n2w k) /\
    eval_operand (Var sp) u = SOME (sw + n2w (k * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (k * type_memory_size dtv)) /\
    u.vs_current_bb = h.vs_current_bb /\
    u.vs_inst_idx = h.vs_inst_idx + 4 /\ ~u.vs_halted` by
    (irule typed_copy_array_addresses_path_mem >>
     simp[Abbr `h`, jump_to_def, update_var_def] >>
     qexistsl_tac [`doff`, `dst`, `aid`, `so`, `src`] >>
     gvs[jump_to_def, update_var_def, MEM, ALL_DISTINCT] >>
     metis_tac[]) >>
  `typed_copy_state_frame a off len s u` by
    metis_tac[typed_copy_state_frame_trans] >>
  `u.vs_memory = s.vs_memory` by gvs[Abbr `h`, jump_to_def, update_var_def] >>
  `typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k u` by
    (irule typed_copy_index_inv_preserve >> goal_assum (drule_at Any) >>
     qexistsl_tac [`a`, `len`, `off`] >> simp[] >> metis_tac[]) >>
  qexists_tac `u` >> gvs[Abbr `h`, jump_to_def, update_var_def] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED

(* A child finishes at its own compiler endpoint, not necessarily body entry. *)
Theorem typed_copy_array_child_backedge_path_mem[local]:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k u /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  ~not_fresh_at sa ctr /\ ~not_fresh_at sa tmp /\ ctr <> tmp /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  k < N /\ (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  lookup_block end_lbl func.fn_blocks = SOME back /\
  back.bb_instructions = pre ++
    [mk_inst bid ADD [Var ctr; Lit 1w] [tmp];
     mk_inst (bid+1) ASSIGN [Var tmp] [ctr];
     mk_inst (bid+2) JMP [Label header] []] /\
  (?v. gas_path_mem ctx func u 0 (OK v) /\
    typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
      (type_memory_size dtv) u v /\
    val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) v.vs_memory /\
    v.vs_current_bb = end_lbl /\ v.vs_inst_idx = LENGTH pre /\ ~v.vs_halted) ==>
  ?t. gas_path_mem ctx func u 0 (OK t) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 (SUC k) t /\
    t.vs_current_bb = header /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = u.vs_alloca_next
Proof
  strip_tac >>
  `lookup_var ctr u = SOME (n2w k) /\
   eval_operand src u = SOME sw /\ eval_operand dst u = SOME dw` by
    gvs[typed_copy_index_inv_def] >>
  `lookup_var ctr v = SOME (n2w k)` by
    metis_tac[typed_copy_state_frame_counter] >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
    (type_memory_size dtv) u v` by
    metis_tac[typed_copy_state_frame_mono] >>
  qabbrev_tac `t = jump_to header (update_var ctr (n2w (k+1))
    (update_var tmp (n2w (k+1)) v))` >>
  `gas_path_mem ctx func v 0 (OK t)` by
    (unabbrev_all_tac >> irule typed_copy_backedge_path_mem >>
     metis_tac[]) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
    (type_memory_size dtv) v t` by
    (unabbrev_all_tac >> irule typed_copy_control_pair_frame >> simp[]) >>
  `typed_copy_state_frame sa (w2n dw + k * type_memory_size dtv)
    (type_memory_size dtv) u t` by
    metis_tac[typed_copy_state_frame_trans] >>
  `eval_operand src t = SOME sw /\ eval_operand dst t = SOME dw` by
    metis_tac[typed_copy_state_frame_operand] >>
  `lookup_var ctr t = SOME (n2w (SUC k)) /\
   t.vs_memory = v.vs_memory /\ t.vs_current_bb = header /\
   t.vs_inst_idx = 0 /\ ~t.vs_halted` by
    simp[Abbr `t`, jump_to_def, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE, ADD1] >>
  `typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 (SUC k) t` by
    (irule typed_copy_index_inv_step >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  (conj_tac >- metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  qpat_x_assum `typed_copy_state_frame sa _ _ u t` mp_tac >>
  simp[typed_copy_state_frame_def, venom_state_component_equality]
QED

Theorem typed_copy_array_step_path_mem:
  typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k s /\
  ci_mono sa a /\ not_fresh_at a ctr /\
  ~not_fresh_at sa ctr /\ ~not_fresh_at sa tmp /\ ctr <> tmp /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at a x) /\
  (!x. MEM x [lt; done; so; doff; sp; dp] ==> ~not_fresh_at a x) /\
  ALL_DISTINCT [ctr; so; doff; sp; dp] /\
  k < N /\ N < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = header /\ s.vs_inst_idx = 0 /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  lookup_block header func.fn_blocks = SOME test /\
  test.bb_instructions =
    [mk_inst hid LT [Var ctr; Lit (n2w N)] [lt];
     mk_inst (hid+1) ISZERO [Var lt] [done];
     mk_inst (hid+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  lookup_block body_lbl func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst aid MUL [Var ctr; Lit (n2w (type_memory_size stv))] [so];
     mk_inst (aid+1) MUL [Var ctr; Lit (n2w (type_memory_size dtv))] [doff];
     mk_inst (aid+2) ADD [src; Var so] [sp];
     mk_inst (aid+3) ADD [dst; Var doff] [dp]] bb.bb_instructions /\
  lookup_block end_lbl func.fn_blocks = SOME back /\
  back.bb_instructions = pre ++
    [mk_inst bid ADD [Var ctr; Lit 1w] [tmp];
     mk_inst (bid+1) ASSIGN [Var tmp] [ctr];
     mk_inst (bid+2) JMP [Label header] []] /\
  (!u. typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 k u /\
    eval_operand (Var sp) u = SOME (sw + n2w (k * type_memory_size stv)) /\
    eval_operand (Var dp) u = SOME (dw + n2w (k * type_memory_size dtv)) /\
    u.vs_current_bb = body_lbl /\ u.vs_inst_idx = 4 /\ ~u.vs_halted ==>
    ?v. gas_path_mem ctx func u 0 (OK v) /\
      typed_copy_state_frame a (w2n dw + k * type_memory_size dtv)
        (type_memory_size dtv) u v /\
      val_in_memory dtv (f k) (w2n dw + k * type_memory_size dtv) v.vs_memory /\
      v.vs_current_bb = end_lbl /\ v.vs_inst_idx = LENGTH pre /\ ~v.vs_halted) ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    typed_copy_index_inv sa ctr src dst sw dw f stv dtv N s0 (SUC k) t /\
    t.vs_current_bb = header /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME test` by simp[] >>
  drule_all typed_copy_array_entry_path_mem >>
  disch_then (qspecl_then [`0`, `0`, `ctx`] strip_assume_tac) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `typed_copy_state_frame a _ _ s u` mp_tac >>
     simp[typed_copy_state_frame_def, venom_state_component_equality]) >>
  qpat_x_assum `!u. _ ==> ?v. _` drule_all >> disch_tac >>
  drule_all typed_copy_array_child_backedge_path_mem >>
  strip_tac >> qexists_tac `t` >> simp[] >>
  metis_tac[gas_path_mem_then, ADD_CLAUSES]
QED
