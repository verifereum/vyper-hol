(* Counted control slices for independently-strided typed array copies. *)
Theory bodyPtrTypedCopyArrayControl
Ancestors typedCopyLoopHeaderPtr typedCopyLoopBackedgePtr exprSimPtrProps
  forPtrControl forPtrAddress forPtrAdmin forPtrScalarStore annAssignPtrLength
  fragGasSeqPtr fragGasPathPtr venomExecSemantics venomInst venomState words finite_map arithmetic

(* A jump endpoint deliberately stops before any target PHIs. *)
Theorem typed_copy_counted_jump:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> GAS /\
  ptr_inst_ok D 0 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK (jump_to lbl s) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
     (OK (jump_to lbl s))` by
    (simp[gas_path_ptr_edge_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          ptrSafeRunTheory.ptr_safe_step_def] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn (jump_to lbl s) 0 G tn
     (OK (jump_to lbl s))` by simp[cj 1 gas_path_ptr_rules, jump_to_def] >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

Theorem typed_copy_arith_counted:
  (opc = LT \/ opc = MUL \/ opc = ISZERO) /\
  (opc = LT ==> ?v k. ops = [Var v; Lit k]) /\
  (!op. MEM op ops ==> op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  ~u.vs_halted /\ u.vs_requests = s.vs_requests /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out})) (tn with t_var := tn.t_var |+ (out,{}))
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule typed_copy_loop_test_check >> simp[] >> metis_tac[]) >>
  `(mk_inst id opc ops [out]).inst_opcode <> INVOKE /\
   (mk_inst id opc ops [out]).inst_opcode <> GAS /\
   ~is_terminator (mk_inst id opc ops [out]).inst_opcode` by
    gvs[mk_inst_def, is_terminator_def] >>
  drule_all gas_path_ptr_one_step >>
  disch_then (qspec_then `PG` assume_tac) >>
  `step_prov PG G (mk_inst id opc ops [out]) u = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc ops [out]) s u tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[]) >>
  gvs[mk_inst_def, is_terminator_def]
QED

Theorem typed_copy_loop_test_counted:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst id LT [Var ctr; Lit (n2w n)] [lt];
     mk_inst (id+1) ISZERO [Var lt] [done];
     mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []] /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
  i <= n /\ n < dimword(:256) /\ ctr <> lt /\ ctr <> done ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {lt})) (COMPL {done}))
    (tn with t_var := (tn.t_var |+ (lt,{})) |+ (done,{}))
    (OK (jump_to (if i < n then body_lbl else exit)
      (update_var done (bool_to_word (~(i < n)))
        (update_var lt (bool_to_word (i < n)) s))))
Proof
  strip_tac >>

  qmatch_goalsub_abbrev_tac `jump_to dest (update_var done w2 (update_var lt w1 s))` >>
  qabbrev_tac `s1 = (update_var lt w1 s) with vs_inst_idx := 1` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `t1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` by
    (`gas_path_ptr D 0 ctx fn PG G tn s 0
        (DRESTRICT G (COMPL {lt})) (tn with t_var := tn.t_var |+ (lt,{}))
        (OK ((update_var lt w1 s) with vs_inst_idx := SUC s.vs_inst_idx))`
       suffices_by simp[Abbr `s1`, Abbr `g1`, Abbr `t1`] >>
     irule typed_copy_arith_counted >> simp[update_var_def] >>
     qexistsl_tac [`id`, `LT`, `[Var ctr; Lit (n2w n)]`] >>
     simp[get_instruction_def] >> conj_tac
     >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def]) >>
     `i < dimword(:256)` by decide_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, w2n_n2w, LESS_MOD, update_var_def, Abbr `w1`]) >>
  qabbrev_tac `s2 = (update_var done w2 s1) with vs_inst_idx := 2` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {done})` >>
  qabbrev_tac `t2 = t1 with t_var := t1.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g2 t2 (OK s2)` by
    (`gas_path_ptr D 0 ctx fn PG g1 t1 s1 0
       (DRESTRICT g1 (COMPL {done})) (t1 with t_var := t1.t_var |+ (done,{}))
       (OK ((update_var done w2 s1) with vs_inst_idx := SUC s1.vs_inst_idx))`
      suffices_by simp[Abbr `s2`, Abbr `g2`, Abbr `t2`, Abbr `s1`] >>
     irule typed_copy_arith_counted >>
     simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `ISZERO`, `[Var lt]`] >>
     simp[get_instruction_def, Abbr `t1`, ptrDisciplineTheory.op_taint_def,
       FLOOKUP_UPDATE, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       eval_operand_def, lookup_var_def, update_var_def, Abbr `w1`, Abbr `w2`,
       bool_to_word_def] >> Cases_on `i<n` >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG g2 t2 s2 0 g2 t2 (OK (jump_to dest s2))` by
    (irule typed_copy_counted_jump >> simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexists_tac `mk_inst (id+2) JNZ [Var done; Label exit; Label body_lbl] []` >>
     simp[get_instruction_def, update_var_def,
       mk_inst_def, is_terminator_def] >> conj_tac
     >- (simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE, Abbr `w2`, Abbr `dest`,
          bool_to_word_def, jump_to_def] >> Cases_on `i<n` >> simp[]) >>
     irule (SRULE [mk_inst_def] typed_copy_loop_test_check) >>
     simp[Abbr `t2`, Abbr `t1`] >> conj_tac
     >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]) >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, Abbr `w2`, bool_to_word_def, jump_to_def] >>
     Cases_on `i<n` >> simp[]) >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all gas_path_ptr_then >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `t2`, Abbr `t1`, jump_to_def,
       update_var_def]
QED

Theorem typed_copy_loop_backedge_counted:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
  get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME (mk_inst id3 JMP [Label cond] []) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var ctr s = SOME w /\ FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}))
    (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{}))
    (OK (jump_to cond (update_var ctr (w+1w) (update_var tmp (w+1w) s))))
Proof
  strip_tac >> drule_all for_counter_increment_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 t1 (OK s1)` >>
  `gas_path_ptr D 0 ctx fn PG g1 t1 s1 0 g1 t1 (OK (jump_to cond s1))` by
    (irule typed_copy_counted_jump >>
     simp[Abbr `s1`, update_var_def] >>
     simp[mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs, eval_operand_def] >>
     simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, ptrDisciplineTheory.allocas_from_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       step_inst_non_invoke, step_inst_base_opcode_eqs, mk_inst_def,
       eval_operand_def, jump_to_def, ptrDisciplineTheory.op_taint_def]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >>
  simp[Abbr `s1`, Abbr `g1`, Abbr `t1`, jump_to_def]
QED

Theorem typed_copy_loop_address_counted:
  !D ctx fn PG sb si ctr so doff sp dp sr dr id i ss ds a b S T G tn s.
    lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
    lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
    ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
    ALL_DISTINCT [so;doff;sp;dp] /\
    (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
    i*ss < S /\ i*ss+ss <= S /\ i*ds < T /\ i*ds+ds <= T /\
    w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) /\
    si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
    si.cs_current_insts = sb.cs_current_insts ++
      [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
       mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
       mk_inst (id+2) ADD [Var sr;Var so] [sp];
       mk_inst (id+3) ADD [Var dr;Var doff] [dp]] /\
    fn_has_code sb si fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
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
  typedCopyLoopAmbientLib.address_resources typed_copy_loop_dynamic_offset_covers
QED

Resume typed_copy_loop_address_counted[path]:
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME (mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]) /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]) /\
   get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME (mk_inst (id+2) ADD [Var sr;Var so] [sp]) /\
   get_instruction bb (SUC (SUC (SUC s.vs_inst_idx))) = SOME (mk_inst (id+3) ADD [Var dr;Var doff] [dp])` by
    (first_assum (qspec_then `0` assume_tac) >>
     first_assum (qspec_then `1` assume_tac) >>
     first_assum (qspec_then `2` assume_tac) >>
     first_assum (qspec_then `3` assume_tac) >> gvs[arithmeticTheory.ADD1]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (simp[NoAsms, Abbr `g1`, Abbr `tn1`, Abbr `s1`] >>
     irule typed_copy_arith_counted >> simp[update_var_def] >>
     qexistsl_tac [`id`, `MUL`, `[Var ctr; Lit (n2w ss)]`] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, word_mul_n2w, update_var_def] >>
     conj_tac >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def]) >>
     gvs[mk_inst_def]) >>
  `gas_path_ptr D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)` by
    (simp[NoAsms, Abbr `g2`, Abbr `tn2`, Abbr `s2`] >>
     irule typed_copy_arith_counted >> simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`, `MUL`, `[Var ctr; Lit (n2w ds)]`] >>
     simp[Abbr `tn1`, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- (rpt strip_tac >> gvs[ptrDisciplineTheory.op_taint_def, FLOOKUP_UPDATE]) >>
     gvs[lookup_var_def, update_var_def, word_mul_n2w, mk_inst_def]) >>
  `op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {}` by
    gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)` by
    suspend "source_add" >>
  `gas_path_ptr D 0 ctx fn PG g3 tn3 s3 0 g4 tn4 (OK s4)` by
    suspend "destination_add" >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ g2 tn2 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all gas_path_ptr_then >> simp[]
QED

Resume typed_copy_loop_address_counted[source_add]:
  simp[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`] >>
  irule forPtrAdminTheory.copy_len_binop_zero_path_ptr >>
  simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
  simp[Abbr `tn2`, Abbr `tn1`, ptrDisciplineTheory.op_taint_def,
    FLOOKUP_UPDATE, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    eval_operand_def, lookup_var_def, update_var_def] >> gvs[lookup_var_def, mk_inst_def, ptrDisciplineTheory.op_taint_def]
QED

Resume typed_copy_loop_address_counted[destination_add]:
  simp[Abbr `g4`, Abbr `tn4`, Abbr `s4`, Abbr `t4`] >>
  irule forPtrAdminTheory.copy_len_binop_zero_path_ptr >>
  simp[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`, update_var_def] >>
  simp[Abbr `tn3`, typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
  simp[Abbr `tn2`, Abbr `tn1`, ptrDisciplineTheory.op_taint_def,
    FLOOKUP_UPDATE, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
    eval_operand_def, lookup_var_def, update_var_def] >> gvs[lookup_var_def, mk_inst_def, ptrDisciplineTheory.op_taint_def]
QED

Finalise typed_copy_loop_address_counted
