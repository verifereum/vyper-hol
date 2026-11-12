(* Full ambient frame for counted loop addressing. *)
Theory typedCopyLoopControlFramePathPtr
Ancestors typedCopyLoopAddressClosedPtr typedCopyLoopHeaderPathPtr
  typedCopyLoopBackedgePathPtr annAssignPtrBytestring

Theorem typed_copy_loop_address_path_ptr_framed:
 !D ctx fn PG G tn s bb pre post ctr so doff sp dp sr dr id i ss ds a b S T.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
 [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
  mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
  mk_inst (id+2) ADD [Var sr;Var so] [sp];
  mk_inst (id+3) ADD [Var dr;Var doff] [dp]] ++ post /\
 s.vs_inst_idx = LENGTH pre /\
 lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
 lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
 ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
 ALL_DISTINCT [so;doff;sp;dp] /\
 (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
 i*ss+ss <= S /\ i*ds+ds <= T /\
 w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 sf.vs_current_bb = s.vs_current_bb /\ sf.vs_inst_idx = LENGTH pre + 4 /\
 ~sf.vs_halted /\ sf.vs_allocas = s.vs_allocas /\
 sf.vs_fmp = s.vs_fmp /\ sf.vs_requests = s.vs_requests /\
 tnf.t_imm = tn.t_imm /\
 lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
 lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
 ptr_covers Gf tnf sp sf ss /\ ptr_covers Gf tnf dp sf ds /\
 sf.vs_memory=s.vs_memory /\ tnf.t_mem=tn.t_mem /\
 tnf.t_stor=tn.t_stor /\ tnf.t_trans=tn.t_trans /\
 (!p. ~MEM p [so;doff;sp;dp] ==>
 lookup_var p sf=lookup_var p s /\ FLOOKUP Gf p=FLOOKUP G p /\
 op_taint tnf (Var p)=op_taint tn (Var p))
Proof
 typedCopyLoopAmbientLib.address_witnesses >>
 conj_tac >- suspend "path" >>
 conj_tac >-
   simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
     venomStateTheory.update_var_def, venomStateTheory.venom_state_component_equality] >>
 `s4.vs_current_bb = s.vs_current_bb /\ s4.vs_inst_idx = LENGTH pre + 4 /\
  ~s4.vs_halted /\ s4.vs_allocas = s.vs_allocas /\
  s4.vs_fmp = s.vs_fmp /\ s4.vs_requests = s.vs_requests /\
  tn4.t_imm = tn.t_imm` by
  simp[Abbr `s4`, Abbr `t4`, Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`,
   venomStateTheory.update_var_def, Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`,
   ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.imm_taint_def,
   venomInstTheory.mk_inst_def] >>
 simp[] >> suspend "resources"
QED

Resume typed_copy_loop_address_path_ptr_framed[path]:
 typedCopyLoopAmbientLib.address_path
   typedCopyLoopControlPathPtrTheory.typed_copy_control_arith_path_ptr
   annAssignPtrLengthTheory.annassign_copy_len_binop_path_ptr
   fragGasPathPtrTheory.gas_path_ptr_then
QED

Resume typed_copy_loop_address_path_ptr_framed[resources]:
 typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers_closed
QED

Finalise typed_copy_loop_address_path_ptr_framed

(* Exact endpoints of the other control paths already expose all updates. *)
Theorem typed_copy_header_path_ptr_framed:
 !D ctx fn PG G tn s bb id ctr len lt done i n body_lbl exit_lbl.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions =
 [mk_inst id LT [Var ctr; len] [lt];
  mk_inst (id+1) ISZERO [Var lt] [done];
  mk_inst (id+2) JNZ [Var done; Label exit_lbl; Label body_lbl] []] /\
 s.vs_inst_idx = 0 /\ lookup_var ctr s = SOME (n2w i) /\
 eval_operand len s = SOME (n2w n) /\
 op_taint tn (Var ctr) = {} /\ op_taint tn len = {} /\
 op_prov G (Var ctr) = NONE /\ op_prov G len = NONE /\
 i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 Gf = DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}) /\
 tnf = (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{})) /\
 sf = jump_to (if i < n then body_lbl else exit_lbl)
   (update_var done (bool_to_word (~(i < n)))
    (update_var lt (bool_to_word (i < n)) s) with vs_inst_idx := 2) /\
 sf.vs_current_bb = (if i < n then body_lbl else exit_lbl) /\
 sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
 lookup_var ctr sf = SOME (n2w i) /\
 sf.vs_memory = s.vs_memory /\ sf.vs_allocas = s.vs_allocas /\
 sf.vs_fmp = s.vs_fmp /\ sf.vs_requests = s.vs_requests /\
 tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
 tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. p <> lt /\ p <> done ==>
   lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
   op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s
Proof
 rpt gen_tac >> strip_tac >> drule_all typed_copy_header_path_ptr >>
 disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
 qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
 simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
   venomStateTheory.venom_state_component_equality]
QED

Theorem typed_copy_loop_backedge_path_ptr_framed:
 !D ctx fn PG G tn s bb pre id ctr tmp cond i.
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
 [mk_inst id ADD [Var ctr;Lit 1w] [tmp];
  mk_inst (id+1) ASSIGN [Var tmp] [ctr];
  mk_inst (id+2) JMP [Label cond] []] /\
 s.vs_inst_idx = LENGTH pre /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_var ctr s = SOME (n2w i) /\ ctr <> tmp /\
 FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf = jump_to cond (update_var ctr (n2w (i+1))
   (update_var tmp (n2w (i+1)) s)) /\
 Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
 tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) /\
 sf.vs_current_bb = cond /\ sf.vs_inst_idx = 0 /\ ~sf.vs_halted /\
 sf.vs_allocas = s.vs_allocas /\ sf.vs_fmp = s.vs_fmp /\
 sf.vs_requests = s.vs_requests /\ tnf.t_imm = tn.t_imm /\
 lookup_var ctr sf = SOME (n2w (i+1)) /\
 FLOOKUP Gf ctr = NONE /\ op_taint tnf (Var ctr) = {} /\
 sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
 (!p. p <> ctr /\ p <> tmp ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p) /\
  (!n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n)) /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s
Proof
 rpt gen_tac >> strip_tac >> drule_all typed_copy_loop_backedge_path_ptr >>
 disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
 qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
 simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
   venomStateTheory.venom_state_component_equality]
QED

Theorem typed_copy_loop_init_path_ptr_framed:
 !D ctx fn PG G tn s bb pre id ctr cond.
 ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
 bb.bb_instructions = pre ++
  [mk_inst id ASSIGN [Lit 0w] [ctr]; mk_inst (id+1) JMP [Label cond] []] /\
 s.vs_inst_idx = LENGTH pre ==>
 gas_path_ptr D 0 ctx fn PG G tn s 0
  (DRESTRICT G (COMPL {ctr})) (tn with t_var := tn.t_var |+ (ctr,{}))
  (OK (jump_to cond
    ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx))) /\
 ((jump_to cond ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx))
   with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
     vs_inst_idx := s.vs_inst_idx|>) = s
Proof
 rpt strip_tac
 >- (irule typedCopyLoopControlPathPtrTheory.typed_copy_loop_init_path_ptr >>
     metis_tac[]) >>
 simp[venomStateTheory.jump_to_def, venomStateTheory.update_var_def,
   venomStateTheory.venom_state_component_equality]
QED
