Theory widenedAssignPtrIndexControl
Ancestors
  forPtrControl bodyPtrSubscriptBoundsRun bodyPtrBopInLoopControl
  placeTypedCopyRecursivePath emitHelperProps emitHelper compileEnv
  exprLoweringProps loweringStateRelDefs freshWrites fragExec fragGasPathPtr venomState venomInst
  venomExecSemantics ptrDiscipline finite_map words list

Theorem widened_assign_index_increment_counted:
  emit_op ADD [Var counter; Lit 1w] sa = (inc,sb) /\
  emit_inst ASSIGN [inc] [counter] sb = ((),sc) /\
  not_fresh_at sa counter /\ lookup_var counter s = SOME (n2w k) /\
  FLOOKUP G counter = NONE /\ op_taint tn (Var counter) = {} /\
  fn_has_code sa sc fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    lookup_var counter t = SOME (n2w (k+1)) /\
    FLOOKUP G' counter = NONE /\ op_taint tn' (Var counter) = {} /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v /\ v <> counter ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `?tmp. inc = Var tmp /\
    sc.cs_blocks = sa.cs_blocks /\ sc.cs_current_bb = sa.cs_current_bb /\
    sc.cs_current_insts = sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ADD [Var counter; Lit 1w] [tmp];
       mk_inst sb.cs_next_id ASSIGN [Var tmp] [counter]] /\
    (!v. not_fresh_at sa v ==> v <> tmp)` by
    (gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id ADD [Var counter; Lit 1w] [tmp]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst sb.cs_next_id ASSIGN [Var tmp] [counter])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >> conj_tac
     >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     first_x_assum (qspec_then `1` mp_tac) >> simp[arithmeticTheory.ADD1]) >>
  drule_all for_counter_increment_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {counter})`,
    `tn with t_var := (tn.t_var |+ (tmp,{})) |+ (counter,{})`,
    `(update_var counter (n2w k + 1w) (update_var tmp (n2w k + 1w) s))
       with vs_inst_idx := SUC (SUC s.vs_inst_idx)`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, word_add_n2w] >>
  gvs[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
      fresh_var_def, fresh_id_def, emit_def, comp_return_def]
QED

(* The comparison is deliberately not specialized to a literal bound or to a
   successful bounds check: the same header handles the final iteration. *)
Theorem widened_assign_index_header_counted:
  emit_op LT [idx;len] sa = (Var lt,sb) /\
  emit_op ISZERO [Var lt] sb = (Var done,sc) /\
  emit_inst JNZ [Var done; Label exit; Label blabel] [] sc = ((),sd) /\
  eval_operand idx s = SOME a /\ eval_operand len s = SOME b /\
  op_taint tn idx = {} /\ op_taint tn len = {} /\
  op_prov G idx = NONE /\ op_prov G len = NONE /\
  fn_has_code sa sd fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_current_bb = (if w2n a < w2n b then blabel else exit) /\
    t.vs_inst_idx = 0 /\ t.vs_prev_bb = SOME s.vs_current_bb /\ ~t.vs_halted /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx;
                 vs_current_bb := t.vs_current_bb; vs_prev_bb := t.vs_prev_bb|> /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sa v ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `ci_mono sa sb /\ ci_mono sb sc /\ ci_mono sc sd` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
              ci_mono_emit_inst, pairTheory.SND] >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn` by
    metis_tac[ci_mono_def, fn_has_code_split, cs_extends_trans] >>
  `!out. step_inst_base (mk_inst sa.cs_next_id LT [idx;len] [out]) s =
    OK (update_var out (bool_to_word (w2n a < w2n b)) s)` by
    (gen_tac >> irule step_LT >> simp[]) >>
  `!op. MEM op [idx;len] ==> op_taint tn op = {} /\ op_prov G op = NONE` by (simp[] >> metis_tac[]) >>
  drule_all (bodyPtrSubscriptNumericTheory.emit_numeric_counted |>
    Q.INST [`opc` |-> `LT`] |> SIMP_RULE (srw_ss()) []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qabbrev_tac `s1 = update_var lt (bool_to_word (w2n a < w2n b)) s
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {lt})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (lt,{})` >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0
    (DRESTRICT G1 (COMPL {done}))
    (tn1 with t_var := tn1.t_var |+ (done,{}))
    (OK (update_var done (bool_to_word (~(w2n a < w2n b))) s1
      with vs_inst_idx := LENGTH sc.cs_current_insts)) /\
    sc.cs_current_bb = sb.cs_current_bb /\
    (!v. not_fresh_at sb v ==> v <> done)` by
    (irule (bodyPtrSubscriptNumericTheory.emit_numeric_counted |>
       Q.INST [`opc` |-> `ISZERO`, `ops` |-> `[Var lt]`]) >>
     simp[Abbr `s1`, Abbr `G1`, Abbr `tn1`, update_var_def,
          lookup_var_def, eval_operand_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
          op_taint_def, op_prov_def] >>
     qexists_tac `lt` >> simp[] >> gen_tac >> simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
          eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          bool_to_word_def]) >>
  qabbrev_tac `s2 = update_var done (bool_to_word (~(w2n a < w2n b))) s1
    with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  qabbrev_tac `G2 = DRESTRICT G1 (COMPL {done})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (done,{})` >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2
    (OK (jump_to (if ~(w2n a < w2n b) then exit else blabel) s2))` by
    (irule stmtAssertPtrTheory.assert_jnz_zero_path_ptr >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
     qexistsl_tac [`Var done`, `sc`, `sd`] >>
     gvs[Abbr `tn2`, Abbr `tn1`,
          emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def,
          update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
          op_taint_def] >> Cases_on `w2n a < w2n b` >> simp[bool_to_word_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK (jump_to (if w2n a < w2n b then blabel else exit) s2))` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[] >> disch_then
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> Cases_on `w2n a < w2n b` >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`, `jump_to (if w2n a < w2n b then blabel else exit) s2`] >>
  simp[Abbr `s2`, Abbr `s1`, Abbr `G2`, Abbr `G1`, Abbr `tn2`, Abbr `tn1`,
       jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> `not_fresh_at sb v` by
    metis_tac[ci_mono_def, not_fresh_at_mono] >> metis_tac[]
QED

Theorem widened_assign_scalar_init_counted:
  emit_inst ASSIGN [Lit w] [counter] sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    lookup_var counter t = SOME w /\
    FLOOKUP G' counter = NONE /\ op_taint tn' (Var counter) = {} /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!v. v <> counter ==>
      lookup_var v t = lookup_var v s /\ FLOOKUP G' v = FLOOKUP G v /\
      op_taint tn' (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSIGN [Lit w] [counter]]` by
    gvs[emit_inst_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id ASSIGN [Lit w] [counter])` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  drule_all (SRULE [forPtrAdminTheory.assign_literal_scalar_ghost]
    forPtrAdminTheory.assign_literal_zero_path_ptr) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  qexistsl_tac [`DRESTRICT G (COMPL {counter})`,
    `tn with t_var := tn.t_var |+ (counter,{})`,
    `update_var counter w s with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
       op_taint_def, arithmeticTheory.ADD1]
QED
