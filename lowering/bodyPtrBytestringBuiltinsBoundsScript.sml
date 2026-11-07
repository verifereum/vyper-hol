(* Scalar bounds checks shared by all slice sources. *)
Theory bodyPtrBytestringBuiltinsBounds
Ancestors
  builtinBytes fragGasSeqPtr stmtAppendStorageRunPtr stmtAppendStoragePathPtr
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  venomExecSemantics venomInst venomState emitHelperProps
  finite_map list words arithmetic context emitHelper compileEnv exprLoweringProps
  exprSimWordBuiltins instIdxIndep fragExec rich_list

Theorem slice_scalar_inst_check:
  MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops outs) s
Proof
  rpt strip_tac >>
  `!v. MEM (Var v) ops ==> FLOOKUP G v = NONE` by
    (rpt strip_tac >> first_x_assum drule >> simp[op_prov_def]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  gvs[FLOOKUP_DEF] >> metis_tac[]
QED

Theorem slice_scalar_counted_edge:
  MEM opc [ADD; LT; GT; OR; ISZERO; ASSERT] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops outs) /\
  step_inst_base (mk_inst id opc ops outs) s = OK t /\
  t.vs_requests = s.vs_requests ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops outs) t)
    (step_taint (mk_inst id opc ops outs) s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops outs) s` by
    (irule slice_scalar_inst_check >> metis_tac[]) >>
  `opc <> INVOKE /\ ~is_terminator opc /\ opc <> GAS` by
    gvs[is_terminator_def] >>
  mp_tac (Q.INST [`i` |-> `mk_inst id opc ops outs`, `lo` |-> `0`,
    `u` |-> `t`] straight_line_ptr_edge) >>
  simp[mk_inst_def]
QED

Theorem slice_assert_abort_counted:
  op_taint tn op = {} /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ASSERT [op] []) /\
  step_inst_base (mk_inst id ASSERT [op] []) s = Abort a t ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (Abort a t)
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule append_assert_abort_check >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`i` |-> `mk_inst id ASSERT [op] []`, `lo` |-> `0`]
    gas_path_ptr_abort) >> simp[mk_inst_def, is_terminator_def]
QED

Theorem slice_scalar_ghost:
  MEM opc [ADD; LT; GT; OR; ISZERO] /\
  (!op. MEM op ops ==> op_prov G op = NONE) /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G (mk_inst id opc ops [out]) s' =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s s' tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `first_prov G ops = NONE` by
    (qpat_x_assum `!op. _` mp_tac >>
     Induct_on `ops` >> simp[first_prov_def]) >>
  `new_site_bytes s s' = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  (simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def, taint_component_equality] >>
   Cases_on `ops` >> simp[out_taint_def] >>
   Cases_on `t` >- (simp[out_taint_def] >> Cases_on `eval_operand h s` >> simp[]) >>
   Cases_on `t'` >> simp[out_taint_def] >>
   Cases_on `eval_operand h s` >> simp[] >>
   Cases_on `t` >> simp[])
QED

Theorem compile_assert_slice_bounds_layout:
  compile_assert_slice_bounds a n limit sa = ((), sb) ==>
  sb.cs_next_var = sa.cs_next_var + 5 /\
  sb.cs_next_id = sa.cs_next_id + 6 /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  same_blocks sa sb /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id ADD [a; n]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) LT
       [Var (STRING #"%" (toString sa.cs_next_var)); a]
       [STRING #"%" (toString (sa.cs_next_var + 1))];
     mk_inst (sa.cs_next_id + 2) GT
       [Var (STRING #"%" (toString sa.cs_next_var)); limit]
       [STRING #"%" (toString (sa.cs_next_var + 2))];
     mk_inst (sa.cs_next_id + 3) OR
       [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
        Var (STRING #"%" (toString (sa.cs_next_var + 2)))]
       [STRING #"%" (toString (sa.cs_next_var + 3))];
     mk_inst (sa.cs_next_id + 4) ISZERO
       [Var (STRING #"%" (toString (sa.cs_next_var + 3)))]
       [STRING #"%" (toString (sa.cs_next_var + 4))];
     mk_inst (sa.cs_next_id + 5) ASSERT
       [Var (STRING #"%" (toString (sa.cs_next_var + 4)))] []]
Proof
  simp[compile_assert_slice_bounds_def, comp_bind_def, comp_ignore_bind_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_APPEND1, same_blocks_def]
QED

Theorem slice_scalar_update_ghost:
  MEM opc [ADD; LT; GT; OR; ISZERO] /\
  (!op. MEM op ops ==> op_prov G op = NONE) ==>
  step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >> irule slice_scalar_ghost >> simp[update_var_def]
QED

Theorem scalar_prov_restrict:
  op_prov G op = NONE ==> op_prov (DRESTRICT G keep) op = NONE
Proof
  Cases_on `op` >> simp[op_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem scalar_taint_update_other:
  op <> Var x ==>
  op_taint (tn with t_var := tv |+ (x,{})) op =
    op_taint (tn with t_var := tv) op
Proof
  Cases_on `op` >> simp[op_taint_def, FLOOKUP_UPDATE]
QED


(* A single scalar step with an opaque suffix: normalize the ghost before
   exposing the next instruction, rather than duplicating it down the list. *)
Theorem slice_scalar_seq_cons:
  MEM opc [ADD; LT; GT; OR; ISZERO] /\
  (!op. MEM op ops ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s = OK (update_var out w s) /\
  inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{})) code
    ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx) G' tn' ==>
  inst_seq_ptr D 0 ctx fn PG G tn ((mk_inst id opc ops [out])::code) s G' tn'
Proof
  strip_tac >>
  `!op. MEM op ops ==> op_prov G op = NONE` by metis_tac[] >>
  drule_all slice_scalar_update_ghost >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule slice_scalar_inst_check >>
     simp[update_var_def] >> gvs[]) >>
  simp[Once inst_seq_ptr_def]
QED

Theorem slice_bounds_mod_overflow:
  !modulus a n limit. a < modulus /\ n < modulus /\ limit < modulus ==>
  ((a + n) MOD modulus < a \/ limit < (a + n) MOD modulus <=>
   modulus <= a + n \/ limit < a + n)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a + n < modulus`
  >- simp[LESS_MOD] >>
  `a + n < 2 * modulus` by decide_tac >>
  `(a + n) MOD modulus = a + n - modulus` by
    (irule MOD_UNIQUE >> qexists_tac `1` >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED

(* Runtime/frame projection is separate from the ghost replay: callers
   need not expose the implementation of the arithmetic checks. *)
Theorem compile_assert_slice_bounds_normal_frame:
  compile_assert_slice_bounds a n limit sa = ((), sb) /\
  fresh_vars_wrt sa s /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n wa + w2n wn <= w2n wl /\
  t = s with vs_vars := t.vs_vars /\
  fresh_vars_wrt sb t /\
  (!x w. eval_operand x s = SOME w ==> eval_operand x t = SOME w)
Proof
  strip_tac >>
  `!x w z. eval_operand x s = SOME w /\ x = Var z ==> not_fresh_at sa z` by
    (rw[not_fresh_at_def] >>
     metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  `!j w ss. sa.cs_next_var <= j ==>
      eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss /\
      eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  drule compile_assert_slice_bounds_layout >> strip_tac >>
  Cases_on `w2n (wa + wn) < w2n wa` >>
  Cases_on `w2n wl < w2n (wa + wn)` >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, bool_to_word_def,
       eval_operand_def, lookup_var_update_var, WORD_OR_CLAUSES] >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qspec_then `dimword (:256)` mp_tac slice_bounds_mod_overflow >>
      disch_then (qspecl_then [`w2n wa`, `w2n wn`, `w2n wl`] mp_tac) >>
      gvs[word_add_def, w2n_n2w, w2n_lt]) >>
  conj_tac >- simp[update_var_def] >>
  conj_tac
  >- (gvs[fresh_vars_wrt_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `!j v ss. sa.cs_next_var <= j ==>
      eval_operand x (update_var (STRING #"%" (toString j)) v ss) = eval_operand x ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem slice_assert_seq:
  op_taint tn op = {} /\ eval_operand op s = SOME w /\ ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ASSERT [op] []] s G tn
Proof
  strip_tac >> Cases_on `w = 0w`
  >- (`step_inst_base (mk_inst id ASSERT [op] []) s =
        Abort Revert_abort (revert_state (set_returndata [] s))` by
        simp[step_inst_base_opcode_eqs, mk_inst_def] >>
      simp[inst_seq_ptr_def] >> irule append_assert_abort_check >> metis_tac[]) >>
  `step_inst_base (mk_inst id ASSERT [op] []) s = OK s` by
    simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ASSERT [op] []) s` by
    (irule append_scalar_inst_check >> simp[] >> metis_tac[]) >>
  simp[inst_seq_ptr_def, scalar_void_prov, scalar_assert_taint]
QED

Theorem slice_lookup_cursor[local]:
  lookup_var x (s with vs_inst_idx := k) = lookup_var x s
Proof
  simp[lookup_var_def]
QED

Theorem compile_assert_slice_bounds_ghost_sequence:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [a;n;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)) /\
  ~ctx_has_dalloca ctx /\
  names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var + j))) 5 ==>
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s
    (FOLDL (\g x. DRESTRICT g (COMPL {x})) G names)
    (tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names)
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss /\
    eval_operand n (update_var (STRING #"%" (toString j)) w ss) = eval_operand n ss /\
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `!j. sa.cs_next_var <= j ==>
    a <> Var (STRING #"%" (toString j)) /\
    n <> Var (STRING #"%" (toString j)) /\
    limit <> Var (STRING #"%" (toString j))` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  drule compile_assert_slice_bounds_layout >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  gvs[GENLIST_CONS, combinTheory.o_DEF, FOLDL, FUPDATE_LIST] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> qexists_tac `wa + wn` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, scalar_prov_restrict,
       scalar_taint_update_other] >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n (wa + wn) < w2n wa)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, slice_lookup_cursor, lookup_var_update_var,
       GREATER_DEF] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, scalar_prov_restrict,
       scalar_taint_update_other] >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n wl < w2n (wa + wn))` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, slice_lookup_cursor, lookup_var_update_var,
       GREATER_DEF] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  suspend "last_three"
QED

Resume compile_assert_slice_bounds_ghost_sequence[last_three]:
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n (wa + wn) < w2n wa) ||
               bool_to_word (w2n wl < w2n (wa + wn))` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, slice_lookup_cursor, lookup_var_update_var] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word ((bool_to_word (w2n (wa + wn) < w2n wa) ||
               bool_to_word (w2n wl < w2n (wa + wn))) = 0w)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       eval_op_inst_idx, eval_operand_def, slice_lookup_cursor, lookup_var_update_var] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[pred_setTheory.INTER_ASSOC, FUPDATE_COMMUTES] >>
  irule slice_assert_seq >>
  simp[op_taint_def, FLOOKUP_UPDATE, eval_op_inst_idx, eval_operand_def,
       slice_lookup_cursor, lookup_var_update_var]
QED

Finalise compile_assert_slice_bounds_ghost_sequence

Theorem compile_assert_slice_bounds_code:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts /\
    LENGTH (emitted_insts sa sb) = 6 /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> drule compile_assert_slice_bounds_layout >> strip_tac >>
  gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND] >>
  conj_tac
  >- (qexists_tac `l` >>
      rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem slice_bounds_ghost_frame:
  names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var + j))) 5 ==>
  (!x. not_fresh_at sa x ==>
    FLOOKUP (FOLDL (\g v. DRESTRICT g (COMPL {v})) G names) x = FLOOKUP G x /\
    op_taint (tn with t_var := tn.t_var |++ MAP (\v. (v,{})) names) (Var x) =
      op_taint tn (Var x))
Proof
  strip_tac >> gvs[GENLIST_CONS, combinTheory.o_DEF, FOLDL, FUPDATE_LIST] >>
  rpt strip_tac >> fs[not_fresh_at_def] >>
  simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem compile_assert_slice_bounds_counted_ok:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [a;n;limit] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    u.vs_current_bb = sb.cs_current_bb /\
    w2n wa + w2n wn <= w2n wl /\
    u = s with vs_vars := u.vs_vars /\ fresh_vars_wrt sb u /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op u = SOME w) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  `!op. MEM op [a;n;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)` by
    (fs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >> simp[] >>
     rw[not_fresh_at_def] >> metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  qabbrev_tac `names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var + j))) 5` >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s
    (FOLDL (\g x. DRESTRICT g (COMPL {x})) G names)
    (tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names)` by
    (irule compile_assert_slice_bounds_ghost_sequence >> metis_tac[]) >>
  drule_all compile_assert_slice_bounds_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_ptr >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    fs[FILTER_EQ_NIL, EVERY_MEM] >>
  simp[] >> strip_tac >>
  drule_all compile_assert_slice_bounds_normal_frame >> strip_tac >>
  qexistsl_tac [`FOLDL (\g x. DRESTRICT g (COMPL {x})) G names`,
    `tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names`] >>
  simp[] >> conj_tac
  >- (drule compile_assert_slice_bounds_layout >> strip_tac >>
      qpat_x_assum `u = _` (mp_tac o Q.AP_TERM `\t. t.vs_current_bb`) >>
      gvs[same_blocks_def]) >>
  match_mp_tac slice_bounds_ghost_frame >> simp[Abbr `names`]
QED

Theorem compile_assert_slice_bounds_reserved_prefix_run:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  (!op z. MEM op [a;n;limit] /\ op = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl ==>
  ?p. run_inst_seq (TAKE 5 (emitted_insts sa sb)) s = OK p /\
    p = s with vs_vars := p.vs_vars /\
    (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op p = eval_operand op s) /\
    step_inst_base (EL 5 (emitted_insts sa sb)) p =
      if w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn) then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss /\
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  drule compile_assert_slice_bounds_layout >> strip_tac >>
  `?p. run_inst_seq (TAKE 5 (emitted_insts sa sb)) s = OK p` by
    simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_pure2_def, exec_pure1_def, eval_operand_def, lookup_var_update_var] >>
  qexists_tac `p` >> simp[] >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, exec_pure1_def, eval_operand_def, lookup_var_update_var] >>
  strip_tac >> gvs[] >>
  conj_tac >- simp[update_var_def] >>
  reverse conj_tac
  >- (Cases_on `w2n (wa + wn) < w2n wa` >>
      Cases_on `w2n wl < w2n (wa + wn)` >>
      simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
           lookup_var_update_var, bool_to_word_def, WORD_OR_CLAUSES, GREATER_DEF]) >>
  rpt strip_tac >>
  `!j v ss. sa.cs_next_var <= j ==>
    eval_operand op (update_var (STRING #"%" (toString j)) v ss) = eval_operand op ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >> simp[]
QED

Theorem compile_assert_slice_bounds_prefix_run:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\ fresh_vars_wrt sa s /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl ==>
  ?p. run_inst_seq (TAKE 5 (emitted_insts sa sb)) s = OK p /\
    p = s with vs_vars := p.vs_vars /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op p = SOME w) /\
    step_inst_base (EL 5 (emitted_insts sa sb)) p =
      if w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn) then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >>
  `!op w z. eval_operand op s = SOME w /\ op = Var z ==> not_fresh_at sa z` by
    (rw[not_fresh_at_def] >> metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  `!op z. MEM op [a;n;limit] /\ op = Var z ==> not_fresh_at sa z` by
    (simp[] >> metis_tac[]) >>
  drule_all compile_assert_slice_bounds_reserved_prefix_run >> strip_tac >>
  qexists_tac `p` >> simp[] >> metis_tac[]
QED


Theorem compile_assert_slice_bounds_counted_abort:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fresh_vars_wrt sa s /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [a;n;limit] ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  run_inst_seq (emitted_insts sa sb) s = Abort ab u ==>
  ab = Revert_abort /\
  ?p G' tn' j.
    run_inst_seq (TAKE 5 (emitted_insts sa sb)) s = OK p /\
    p = s with vs_vars := p.vs_vars /\
    u = revert_state (set_returndata [] p) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (Abort Revert_abort (u with vs_inst_idx := j)) /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op p = SOME w) /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all compile_assert_slice_bounds_prefix_run >> strip_tac >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
    [EL 5 (emitted_insts sa sb)]` by
    (drule compile_assert_slice_bounds_layout >> simp[]) >>
  `ab = Revert_abort /\ u = revert_state (set_returndata [] p)` by
    (qpat_x_assum `run_inst_seq _ _ = Abort _ _` mp_tac >>
     once_asm_rewrite_tac[] >>
     drule run_inst_seq_append >>
     disch_then (qspec_then `[EL 5 (emitted_insts sa sb)]` assume_tac) >>
     qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
     qpat_x_assum `run_inst_seq (_ ++ _) _ = _` (fn th => rewrite_tac[th]) >>
     simp[run_inst_seq_def] >>
     Cases_on `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` >>
     gvs[] >> metis_tac[]) >>
  simp[] >>
  qpat_x_assum `emitted_insts _ _ = _` kall_tac >>
  `!op. MEM op [a;n;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)` by
    (fs[DISJ_IMP_THM, FORALL_AND_THM] >> rpt strip_tac >> simp[] >>
     rw[not_fresh_at_def] >> metis_tac[fresh_vars_wrt_eval_operand, GREATER_EQ]) >>
  qabbrev_tac `names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var + j))) 5` >>
  `inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s
    (FOLDL (\g x. DRESTRICT g (COMPL {x})) G names)
    (tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names)` by
    (irule compile_assert_slice_bounds_ghost_sequence >> simp[Abbr `names`] >>
     qexistsl_tac [`a`,`limit`,`n`,`wa`,`wl`,`wn`] >>
     simp[] >> metis_tac[MEM]) >>
  drule_all compile_assert_slice_bounds_code >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_ptr >> strip_tac >>
  qexistsl_tac [`FOLDL (\g x. DRESTRICT g (COMPL {x})) G names`,
    `tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names`, `j`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  match_mp_tac slice_bounds_ghost_frame >> simp[Abbr `names`]
QED

Theorem slice_bounds_reserved_runtime:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  (!op z. MEM op [start;len;limit] /\ op = Var z ==> not_fresh_at sa z) /\
  eval_operand start s = SOME wa /\ eval_operand len s = SOME wn /\
  eval_operand limit s = SOME wl ==>
  ?p. p = s with vs_vars := p.vs_vars /\
    (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op p = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x p = lookup_var x s) /\
    run_inst_seq (emitted_insts sa sb) s =
      if w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn) then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >> drule_all compile_assert_slice_bounds_reserved_prefix_run >> strip_tac >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
    [EL 5 (emitted_insts sa sb)]` by
    (drule compile_assert_slice_bounds_layout >> simp[]) >>
  qexists_tac `p` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op. _` (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def] >> metis_tac[]) >>
  qpat_assum `run_inst_seq (TAKE 5 _) _ = OK _`
    (mp_then Any mp_tac run_inst_seq_append) >>
  disch_then (qspec_then `[EL 5 (emitted_insts sa sb)]` mp_tac) >>
  simp[run_inst_seq_def] >>
  Cases_on `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` >>
  gvs[] >> metis_tac[]
QED

Theorem slice_bounds_reserved_natural_runtime:
  compile_assert_slice_bounds start len limit sa = ((),sb) /\
  (!op z. MEM op [start;len;limit] /\ op = Var z ==> not_fresh_at sa z) /\
  eval_operand start s = SOME (n2w a) /\ eval_operand len s = SOME (n2w n) /\
  eval_operand limit s = SOME (n2w cap) /\
  a < dimword (:256) /\ n < dimword (:256) /\ cap < dimword (:256) ==>
  ?p. p = s with vs_vars := p.vs_vars /\
    (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
      eval_operand op p = eval_operand op s) /\
    (!x. not_fresh_at sa x ==> lookup_var x p = lookup_var x s) /\
    run_inst_seq (emitted_insts sa sb) s =
      if dimword (:256) <= a + n \/ cap < a + n then
        Abort Revert_abort (revert_state (set_returndata [] p))
      else OK p
Proof
  strip_tac >> drule_all slice_bounds_reserved_runtime >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  `((a + n) MOD dimword (:256) < a \/ cap < (a + n) MOD dimword (:256)) <=>
    dimword (:256) <= a + n \/ cap < a + n` by
    (irule slice_bounds_mod_overflow >> simp[]) >>
  gvs[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w]
QED

Theorem compile_assert_slice_bounds_reserved_normal_frame:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  (!op z. MEM op [a;n;limit] /\ op = Var z ==> not_fresh_at sa z) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n wa + w2n wn <= w2n wl /\ t = s with vs_vars := t.vs_vars /\
  (!op. (!z. op = Var z ==> not_fresh_at sa z) ==>
    eval_operand op t = eval_operand op s) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all slice_bounds_reserved_runtime >> strip_tac >>
  Cases_on `w2n (wa + wn) < w2n wa \/ w2n wl < w2n (wa + wn)` >> gvs[] >>
  qspec_then `dimword (:256)` mp_tac slice_bounds_mod_overflow >>
  disch_then (qspecl_then [`w2n wa`, `w2n wn`, `w2n wl`] mp_tac) >>
  gvs[word_add_def, w2n_n2w, w2n_lt]
QED
