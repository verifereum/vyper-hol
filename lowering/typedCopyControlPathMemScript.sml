(* Checked execution of typed-copy loop control. *)
Theory typedCopyControlPathMem
Ancestors
  typedCopyPrimitivePathMem placeMemoryArrayControl placeMemoryArrayForward
  bodyMemBiUint2StrBlocks exprSimBopRestWordLoopPath fragGasMode fragGasPathMem
  fragExecMem instMemFrontier venomInstProofs list rich_list arithmetic
  venomInst venomState venomExecSemantics venomExecProofs exprLoweringProps emitHelperProps
  context compileEnv emitHelper bodyDeclMemoryCounted placeMemoryCopyEffect

Theorem typed_copy_prefix_jump_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions = prefix ++ [term] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> GAS) prefix /\
  run_inst_seq_mem_ok prefix s /\ run_inst_seq prefix s = OK u /\
  ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
  (term.inst_opcode = JMP \/ term.inst_opcode = JNZ) /\
  step_inst_base term (u with vs_inst_idx := s.vs_inst_idx + LENGTH prefix) =
    OK (jump_to lbl (u with vs_inst_idx := s.vs_inst_idx + LENGTH prefix)) ==>
  gas_path_mem ctx func s 0 (OK (jump_to lbl u))
Proof
  strip_tac >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  (irule u2s_memory_block_path >> simp[] >>
   qexistsl_tac [`prefix`, `term`, `TAKE s.vs_inst_idx bb.bb_instructions`] >>
   simp[] >> conj_tac
   >- (once_rewrite_tac[ADD_COMM] >> simp[]) >>
   qspec_then `s.vs_inst_idx` (qspec_then `bb.bb_instructions` mp_tac) TAKE_DROP >>
   pure_asm_rewrite_tac[GSYM APPEND_ASSOC] >> simp[])
QED

Theorem typed_memory_array_init_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ASSIGN [Lit 0w] [counter]; mk_inst id2 JMP [Label hdr] []] ==>
  gas_path_mem ctx func s 0 (OK (jump_to hdr (update_var counter 0w s)))
Proof
  strip_tac >> irule typed_copy_prefix_jump_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, eval_operand_def, update_var_def,
       run_inst_seq_mem_ok_def] >>
  irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_memory_array_backedge_path_mem:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  lookup_var counter s = SOME (n2w i) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to hdr
      (update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) s))))
Proof
  strip_tac >> irule typed_copy_prefix_jump_mem >> simp[] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, eval_operand_def,
       lookup_var_update_var, wordsTheory.word_add_n2w, ADD1,
       run_inst_seq_mem_ok_def] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_memory_array_condition_path_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  eval_operand (Var counter) s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) ==>
  gas_path_mem ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      (update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s))))
Proof
  strip_tac >> irule typed_copy_prefix_jump_mem >> simp[] >>
  `i < dimword (:256)` by decide_tac >>
  gvs[eval_operand_def] >>
  simp[mk_inst_def, is_terminator_def, run_inst_seq_def,
       step_inst_base_opcode_eqs, exec_pure2_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var, wordsTheory.w2n_n2w,
       LESS_MOD, run_inst_seq_mem_ok_def] >>
  Cases_on `i < N` >>
  simp[bool_to_word_def, lookup_var_update_var] >>
  rpt conj_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_copy_array_addresses_mem_ok[local]:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem typed_memory_array_addresses_forward_mem:
  (do so <- emit_op MUL [Var counter; Lit (n2w ss)];
      doff <- emit_op MUL [Var counter; Lit (n2w ds)];
      sp <- emit_op ADD [src; so]; dp <- emit_op ADD [dst; doff];
      return (sp,dp)
   od) sa = ((sp,dp),sb) /\
  not_fresh_at sa counter /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  lookup_var counter s = SOME (n2w i) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_path_mem ctx func s 0 (OK u) /\
      eval_operand sp u = SOME (sw + n2w (i * ss)) /\
      eval_operand dp u = SOME (dw + n2w (i * ds)) /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all typed_memory_array_addresses_sequence >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule typed_copy_array_addresses_mem_ok >> goal_assum (drule_at Any)) >>
  `gas_path_mem ctx func s 0
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule (cj 1 body_decl_cursor_path) >> simp[] >>
     qexists_tac `sa` >> gvs[EVERY_MEM]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- (qpat_x_assum `_ = s` mp_tac >> simp[venom_state_component_equality]) >>
  metis_tac[lookup_var_def]
QED

Theorem typed_memory_array_condition_effect_mem:
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id1 LT [Var counter; length] [lt];
     mk_inst id2 ISZERO [Var lt] [done];
     mk_inst id3 JNZ [Var done; Label exit; Label blabel] []] /\
  lookup_var counter s = SOME (n2w i) /\
  eval_operand length s = SOME (n2w N) /\ i <= N /\ N < dimword (:256) /\
  counter <> lt /\ counter <> done /\
  (!x. not_fresh_at old x ==> x <> lt /\ x <> done) /\
  next.cs_current_bb = (if i < N then blabel else exit) /\
  next.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old next s t d n /\
      gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w i) /\ t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `gas_path_mem ctx func s 0
    (OK (jump_to (if i < N then blabel else exit)
      (update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s))))` by
    (irule typed_memory_array_condition_path_mem >>
     qpat_assum `bb.bb_instructions = _` (irule_at Any) >>
     rpt (goal_assum (drule_at Any)) >> simp[eval_operand_def]) >>
  drule gas_marked_path_from_mem >>
  disch_then (qspec_then `F` assume_tac) >>
  qexists_tac `jump_to (if i < N then blabel else exit)
      (update_var done (bool_to_word (~(i < N)))
         (update_var lt (bool_to_word (i < N)) s))` >>
  simp[] >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem typed_memory_array_backedge_effect_mem:
  typed_copy_effect ctx func bst b5 s v d n /\
  gas_path_mem ctx func s 0 (OK v) /\
  lookup_var counter s = SOME (n2w i) /\ not_fresh_at bst counter /\
  (!x. not_fresh_at old x ==>
       not_fresh_at bst x /\ x <> inc /\ x <> counter) /\
  lookup_block b5.cs_current_bb func.fn_blocks = SOME bb /\
  DROP (LENGTH b5.cs_current_insts) bb.bb_instructions =
    [mk_inst id1 ADD [Var counter; Lit 1w] [inc];
     mk_inst id2 ASSIGN [Var inc] [counter]; mk_inst id3 JMP [Label hdr] []] /\
  head.cs_current_bb = hdr /\ head.cs_current_insts = [] ==>
  ?t. typed_copy_effect ctx func old head s t d n /\
      gas_path_mem ctx func s 0 (OK t) /\
      lookup_var counter t = SOME (n2w (SUC i)) /\ t.vs_memory = v.vs_memory
Proof
  strip_tac >>
  `lookup_var counter v = SOME (n2w i)` by
    metis_tac[typed_copy_effect_lookup] >>
  drule typed_copy_effect_endpoint >> strip_tac >>
  `gas_path_mem ctx func v 0
    (OK (jump_to hdr
      (update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v))))` by
    (irule typed_memory_array_backedge_path_mem >> simp[] >> metis_tac[]) >>
  `gas_path_mem ctx func s 0
    (OK (jump_to hdr
      (update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v))))` by
    metis_tac[gas_path_mem_then, ADD_CLAUSES] >>
  drule gas_marked_path_from_mem >>
  disch_then (qspec_then `F` assume_tac) >>
  qexists_tac `jump_to hdr
      (update_var counter (n2w (SUC i)) (update_var inc (n2w (SUC i)) v))` >>
  simp[] >>
  gvs[typed_copy_effect_def, jump_to_def, update_var_def,
      venom_state_component_equality, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED
