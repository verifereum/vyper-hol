Theory placeMemoryArrayControl
Ancestors
  placeMemoryForwardPath placeMemoryDynarrayForward placeMemoryPrimitiveForward fragGasSeq fragGasMode
  fragGasPath exprLoweringProps venomInstProofs venomExecSemantics venomExecProofs venomInst venomState
  context compileEnv loweringStateRelDefs emitHelper emitHelperProps ASCIInumbers finite_map list rich_list arithmetic

(* A straight-line prefix followed by one concrete control transfer. *)
Theorem typed_memory_prefix_jump_forward:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = prefix ++ [term] /\
  s.vs_inst_idx + LENGTH prefix = k /\ 
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> GAS) prefix /\
  run_inst_seq prefix s = OK u /\
  is_terminator term.inst_opcode /\ term.inst_opcode <> INVOKE /\
  term.inst_opcode <> GAS /\
  step_inst_base term (u with vs_inst_idx := k) =
    OK (jump_to lbl (u with vs_inst_idx := k)) ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to lbl (u with vs_inst_idx := k)))
Proof
  strip_tac >>
  `isPREFIX prefix (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `FILTER (\i. i.inst_opcode = GAS) prefix = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> metis_tac[EVERY_MEM]) >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := k))` by
    (drule_all tuple_run_inst_seq_gas_path >> simp[gas_marked_path_def]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (conj_tac >> irule run_inst_seq_preserves_field >>
     qexists_tac `prefix` >> simp[] >> rpt strip_tac >>
     `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
       (qpat_x_assum `EVERY (\i. i.inst_opcode <> INVOKE /\ _) _`
          (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[]) >>
     `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
     drule_all venomInstProofsTheory.step_preserves_halted >>
     drule_all venomInstProofsTheory.step_preserves_control_flow >> simp[]) >>
  `gas_marked_path F ctx func (u with vs_inst_idx := k) 0
     (OK (jump_to lbl (u with vs_inst_idx := k)))` by
    (irule gas_marked_path_zero_jump >> simp[] >>
     qexists_tac `term` >>
     `DROP k bb.bb_instructions = [term]` by
       (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP (LENGTH prefix)`) >>
        pure_rewrite_tac[DROP_DROP_T] >>
        `LENGTH prefix + s.vs_inst_idx = k` by decide_tac >>
        simp[DROP_APPEND]) >>
     `k < LENGTH bb.bb_instructions` by
       (qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[LENGTH_DROP]) >>
     simp[get_instruction_def] >>
     qpat_x_assum `DROP k _ = _` (mp_tac o Q.AP_TERM `HD`) >> simp[HD_DROP]) >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

(* Shared by the dynamic length and fixed literal-bound condition blocks. *)
Theorem typed_memory_array_condition_forward:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      ((update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s)) with vs_inst_idx := 2)))
Proof
  strip_tac >>
  irule typed_memory_prefix_jump_forward >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var] >>
  `i < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  Cases_on `i < N` >> simp[bool_to_word_def, wordsTheory.w2n_n2w,
    arithmeticTheory.LESS_MOD, lookup_var_update_var]
QED

Theorem typed_memory_array_init_forward:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to hdr ((update_var counter 0w s) with
                     vs_inst_idx := s.vs_inst_idx + 1)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_forward >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, eval_operand_def]
QED

Theorem typed_memory_array_backedge_forward:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) /\ SUC i < dimword (:256) ==>
  gas_marked_path F ctx func s 0
    (OK (jump_to hdr
      ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s)) with
        vs_inst_idx := s.vs_inst_idx + 2)))
Proof
  strip_tac >> irule typed_memory_prefix_jump_forward >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, wordsTheory.word_add_n2w, ADD1]
QED

Theorem typed_memory_array_addresses_sequence:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) ==>
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode)
    (emitted_insts sa sb) /\
  EVERY (\j. j.inst_opcode <> GAS) (emitted_insts sa sb) /\
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with vs_vars := s.vs_vars) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s)
Proof
  strip_tac >>
  `!k w t. sa.cs_next_var <= k ==>
     eval_operand src (update_var (STRING #"%" (toString k)) w t) = eval_operand src t /\
     eval_operand dst (update_var (STRING #"%" (toString k)) w t) = eval_operand dst t /\
     eval_operand (Var counter) (update_var (STRING #"%" (toString k)) w t) = eval_operand (Var counter) t` by
    (rpt strip_tac >> irule typed_memory_fresh_operand >> qexists_tac `sa` >> simp[]) >>
  `counter <> STRING #"%" (toString sa.cs_next_var)` by
    (qpat_x_assum `not_fresh_at sa counter` mp_tac >>
     simp[not_fresh_at_def] >> disch_then (qspec_then `sa.cs_next_var` mp_tac) >> simp[]) >>
  qpat_x_assum `_ sa = ((sp,dp),sb)` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def, DROP_APPEND1, mk_inst_def,
       is_terminator_def, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_pure2_def, eval_operand_def, lookup_var_update_var,
       wordsTheory.word_mul_n2w] >>
  conj_tac >- simp[update_var_def] >>
  rpt strip_tac >>
  `!k. sa.cs_next_var <= k ==> x <> STRING #"%" (toString k)` by
    (qpat_x_assum `not_fresh_at sa x` mp_tac >> simp[not_fresh_at_def]) >>
  simp[]
QED

Theorem typed_memory_array_addresses_forward:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_array_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `gas_marked_path F ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`emitted_insts sa sb`, `sa`] >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

(* P carries the semantic invariant and the desired frame.  The callback is
   precisely the recursive segment b4--b5; it is not a continuation runner.
   The last premise is invariance under the explicit pure backedge updates. *)
Theorem typed_memory_array_body_forward:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      comp_return (sp,dp)
   od) sa = ((sp,dp),b4) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ SUC i < dimword (:256) /\
  fn_has_code sa b4 func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  DROP (LENGTH b5.cs_current_insts) bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  (!u. eval_operand sp u = SOME (sw + n2w (i * ss)) /\
       eval_operand dp u = SOME (dw + n2w (i * ds)) /\
       (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
       (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
       ~u.vs_halted /\ u.vs_current_bb = b4.cs_current_bb /\
       u.vs_inst_idx = LENGTH b4.cs_current_insts ==>
       ?v. gas_marked_path F ctx func u 0 (OK v) /\ P v /\
           lookup_var counter v = SOME (n2w i) /\ ~v.vs_halted /\
           v.vs_current_bb = b5.cs_current_bb /\
           v.vs_inst_idx = LENGTH b5.cs_current_insts) /\
  (!v. P v ==> P (jump_to hdr
     ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
       vs_inst_idx := v.vs_inst_idx + 2))) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\ P t /\
      lookup_var counter t = SOME (n2w (SUC i)) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  strip_tac >> drule_all typed_memory_array_addresses_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `!u. _ ==> ?v. _` drule_all >> strip_tac >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
   DROP v.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []]` by simp[] >>
  drule_all typed_memory_array_backedge_forward >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `jump_to hdr
    ((update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v)) with
      vs_inst_idx := v.vs_inst_idx + 2)` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
