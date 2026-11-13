(* Finite counter control segments, before any loop induction. *)
Theory forPtrControl
Ancestors forPtrAdmin forPtrBoundary emitHelperProps venomState venomInst
  venomExecSemantics finite_map ptrDiscipline fragGasPathPtr stmtAssertPtr
  integer_word ptrSafeRun

Theorem for_counter_entry_path_ptr:
  si.cs_blocks = sa.cs_blocks /\ si.cs_current_bb = sa.cs_current_bb /\
  si.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id ASSIGN [Lit 0w] [ctr]] /\
  sb.cs_blocks = si.cs_blocks /\ sb.cs_current_bb = si.cs_current_bb /\
  sb.cs_current_insts = si.cs_current_insts ++
    [mk_inst si.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa si fn /\ fn_has_code si sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {ctr}))
    (tn with t_var := tn.t_var |+ (ctr,{}))
    (OK (jump_to lbl (update_var ctr 0w s)))
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst id ASSIGN [Lit 0w] [ctr])` by
    (qpat_x_assum `fn_has_code si sb fn` kall_tac >>
     drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {ctr}))
    (tn with t_var := tn.t_var |+ (ctr,{}))
    (OK ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SRULE [assign_literal_scalar_ghost] assign_literal_zero_path_ptr) >>
     simp[] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {ctr}))
    (tn with t_var := tn.t_var |+ (ctr,{}))
    ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {ctr}))
    (tn with t_var := tn.t_var |+ (ctr,{}))
    (OK (jump_to lbl
      ((update_var ctr 0w s) with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule for_emit_jump_zero_path_ptr >>
     simp[update_var_def] >> qexistsl_tac [`si`, `sb`] >> simp[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >> simp[jump_to_def]
QED

Theorem for_counter_scalar_frame:
  sf = jump_to lbl (update_var ctr w s) /\
  Gf = DRESTRICT G (COMPL {ctr}) /\
  tnf = (tn with t_var := tn.t_var |+ (ctr,{})) ==>
  lookup_var ctr sf = SOME w /\ FLOOKUP Gf ctr = NONE /\
  op_taint tnf (Var ctr) = {} /\ sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\
  (!p. p <> ctr ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  simp[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem for_eq_scalar_ghost[local]:
  step_prov PG G (mk_inst id EQ [left;right] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id EQ [left;right] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, out_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, mk_inst_def, taint_component_equality] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem for_counter_test_path_ptr:
  si.cs_blocks = sa.cs_blocks /\ si.cs_current_bb = sa.cs_current_bb /\
  si.cs_current_insts = sa.cs_current_insts ++
    [mk_inst id EQ [Var ctr;bound] [out]] /\
  sb.cs_blocks = si.cs_blocks /\ sb.cs_current_bb = si.cs_current_bb /\
  sb.cs_current_insts = si.cs_current_insts ++
    [mk_inst si.cs_next_id JNZ [Var out; Label exit; Label looplbl] []] /\
  fn_has_code sa si fn /\ fn_has_code si sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var ctr s = SOME w /\ eval_operand bound s = SOME z /\
  op_taint tn (Var ctr) = {} /\ op_taint tn bound = {} /\
  op_prov G (Var ctr) = NONE /\ op_prov G bound = NONE ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (jump_to (if w = z then exit else looplbl)
      (update_var out (if w = z then 1w else 0w) s)))
Proof
  strip_tac >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst id EQ [Var ctr;bound] [out])` by
    (qpat_x_assum `fn_has_code si sb fn` kall_tac >>
     drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst id EQ [Var ctr;bound] [out]) s =
    OK (update_var out (if w = z then 1w else 0w) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def] >>
     Cases_on `w = z` >> simp[bool_to_word_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (if w = z then 1w else 0w) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_at (Pat `step_inst_base _ _ = _`) eq_zero_path_ptr >>
     simp[for_eq_scalar_ghost]) >>
  `gas_path_ptr D 0 ctx fn PG
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    ((update_var out (if w = z then 1w else 0w) s)
      with vs_inst_idx := SUC s.vs_inst_idx) 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (jump_to (if w = z then exit else looplbl)
      ((update_var out (if w = z then 1w else 0w) s)
        with vs_inst_idx := SUC s.vs_inst_idx)))` by
    (irule assert_jnz_zero_path_ptr >>
     simp[update_var_def] >>
     qexistsl_tac [`Var out`, `si`, `sb`] >>
     simp[update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE, op_taint_def]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >> simp[jump_to_def]
QED

(* ADD and ASSIGN share the scalar overwrite interface.  The existing
   copy-loop scalar ghost facts are local to their source theory. *)
Theorem for_scalar_update_ghost[local]:
  FLOOKUP G root = NONE /\ op_taint tn (Var root) = {} /\
  ((opc = ADD /\ args = [Var root; Lit lit]) \/
   (opc = ASSIGN /\ args = [Var root])) ==>
  step_prov PG G (mk_inst id opc args [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
  step_taint (mk_inst id opc args [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, out_taint_def,
       op_taint_def, imm_taint_def, range_bytes_def,
       taint_component_equality] >>
  Cases_on `lookup_var root s` >> gvs[eval_operand_def, op_taint_def]
QED

Theorem for_assign_scalar_path_ptr[local]:
  FLOOKUP G root = NONE /\ op_taint tn (Var root) = {} /\
  lookup_var root s = SOME w /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ASSIGN [Var root] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id ASSIGN [Var root] [out]) (update_var out w s) =
    DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ASSIGN [Var root] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule for_scalar_update_ghost >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ASSIGN [Var root] [out]) (update_var out w s))
    (step_taint (mk_inst id ASSIGN [Var root] [out]) s (update_var out w s) tn)
    (OK ((update_var out w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule straight_line_zero_path_ptr >>
     simp[GSYM mk_inst_def, is_terminator_def] >> reverse conj_tac
     >- (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def,
          codegenRelTheory.source_memory_write_ranges_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          op_taint_def, step_inst_non_invoke] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, update_var_def]) >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def]) >> gvs[]
QED

Theorem for_add_scalar_path_ptr[local]:
  FLOOKUP G root = NONE /\ op_taint tn (Var root) = {} /\
  lookup_var root s = SOME w /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var root; Lit lit] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (w + lit) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var root; Lit lit] [out]) s =
    OK (update_var out (w + lit) s)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Var root; Lit lit] [out])
      (update_var out (w + lit) s))
    (step_taint (mk_inst id ADD [Var root; Lit lit] [out]) s
      (update_var out (w + lit) s) tn)
    (OK ((update_var out (w + lit) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule copy_len_binop_zero_path_ptr >> simp[GSYM mk_inst_def] >>
     simp[op_taint_def, imm_taint_def]) >>
  `step_prov PG G (mk_inst id ADD [Var root; Lit lit] [out])
     (update_var out (w + lit) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id ADD [Var root; Lit lit] [out]) s
     (update_var out (w + lit) s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule for_scalar_update_ghost >> simp[]) >> gvs[]
QED

Theorem for_counter_increment_path_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var ctr s = SOME w /\
  FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}))
    (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{}))
    (OK ((update_var ctr (w + 1w)
      (update_var tmp (w + 1w) s))
      with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tmp}))
    (tn with t_var := tn.t_var |+ (tmp,{}))
    (OK ((update_var tmp (w + 1w) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule for_add_scalar_path_ptr >> simp[] >> metis_tac[]) >>
  qabbrev_tac `sm = (update_var tmp (w + 1w) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (tmp,{})` >>
  qabbrev_tac `Gm = DRESTRICT G (COMPL {tmp})` >>
  `gas_path_ptr D 0 ctx fn PG Gm tm sm 0
    (DRESTRICT Gm (COMPL {ctr}))
    (tm with t_var := tm.t_var |+ (ctr,{}))
    (OK ((update_var ctr (w + 1w) sm)
      with vs_inst_idx := SUC sm.vs_inst_idx))` by
    (irule for_assign_scalar_path_ptr >>
     simp[Abbr `sm`, Abbr `tm`, Abbr `Gm`, update_var_def,
          lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     qexistsl_tac [`id2`, `tmp`] >> simp[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >>
  simp[Abbr `sm`, Abbr `tm`, Abbr `Gm`, update_var_def]
QED

Theorem for_counter_backedge_path_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var ctr; Lit 1w] [tmp]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 ASSIGN [Var tmp] [ctr]) /\
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  LENGTH sa.cs_current_insts = SUC (SUC s.vs_inst_idx) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_var ctr s = SOME w /\
  FLOOKUP G ctr = NONE /\ op_taint tn (Var ctr) = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}))
    (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{}))
    (OK (jump_to lbl (update_var ctr (w + 1w)
      (update_var tmp (w + 1w) s))))
Proof
  strip_tac >>
  drule_all for_counter_increment_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qabbrev_tac `sf = (update_var ctr (w + 1w)
    (update_var tmp (w + 1w) s))
      with vs_inst_idx := SUC (SUC s.vs_inst_idx)` >>
  qabbrev_tac `Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr})` >>
  qabbrev_tac `tf = tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})` >>
  `gas_path_ptr D 0 ctx fn PG Gf tf sf 0 Gf tf
    (OK (jump_to lbl sf))` by
    (irule for_emit_jump_zero_path_ptr >>
     simp[Abbr `sf`, update_var_def] >>
     qexistsl_tac [`sa`, `sb`] >> simp[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >>
  simp[Abbr `sf`, Abbr `Gf`, Abbr `tf`, jump_to_def]
QED

Theorem for_counter_backedge_frame:
  sf = jump_to lbl (update_var ctr w (update_var tmp w s)) /\
  Gf = DRESTRICT (DRESTRICT G (COMPL {tmp})) (COMPL {ctr}) /\
  tnf = (tn with t_var := (tn.t_var |+ (tmp,{})) |+ (ctr,{})) ==>
  lookup_var ctr sf = SOME w /\ lookup_var tmp sf = SOME w /\
  FLOOKUP Gf ctr = NONE /\ FLOOKUP Gf tmp = NONE /\
  op_taint tnf (Var ctr) = {} /\ op_taint tnf (Var tmp) = {} /\
  sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  (!p. p <> ctr /\ p <> tmp ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  simp[lookup_var_def, update_var_def, jump_to_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  Cases_on `ctr = tmp` >> simp[]
QED
