(* Counted element-address arithmetic; no loop or representation unfolding. *)
Theory forPtrAddress
Ancestors forPtrAdmin forPtrElement typedCopyLoopHeaderPtr typedCopyPtr
  ptrDiscipline ptrSafeRun venomExecSemantics venomInst venomState
  finite_map fragGasPathPtr

Theorem for_mul_scalar_path_ptr[local]:
  op_taint tn (Var idx) = {} /\ lookup_var idx s = SOME a /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var idx; Lit b] [out]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MUL [Var idx; Lit b] [out]) s =
    OK (update_var out (a*b) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst id MUL [Var idx; Lit b] [out]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >>
     rpt strip_tac >> gvs[op_taint_def, imm_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id MUL [Var idx; Lit b] [out])
      (update_var out (a*b) s))
    (step_taint (mk_inst id MUL [Var idx; Lit b] [out]) s
      (update_var out (a*b) s) tn)
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule straight_line_zero_path_ptr >>
     simp[GSYM mk_inst_def, is_terminator_def]) >>
  `step_prov PG G (mk_inst id MUL [Var idx; Lit b] [out])
      (update_var out (a*b) s) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id MUL [Var idx; Lit b] [out]) s
      (update_var out (a*b) s) tn = tn with t_var := tn.t_var |+ (out,{})` by
    (irule typed_copy_loop_arith_ghost >> simp[update_var_def]) >> gvs[]
QED

Theorem for_dynamic_add_ghost[local]:
  FLOOKUP G off = NONE ==>
  step_prov PG G (mk_inst id ADD [Var p; Var off] [q]) (update_var q w s) =
    set_prov G [q] (FLOOKUP G p) /\
  step_taint (mk_inst id ADD [Var p; Var off] [q]) s (update_var q w s) tn =
    (tn with t_var := tn.t_var |+ (q,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var q w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def, mk_inst_def] >>
  conj_tac >- (Cases_on `FLOOKUP G p` >> simp[]) >>
  simp[step_taint_def, set_var_taint_def, out_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, mk_inst_def, taint_component_equality] >>
  Cases_on `eval_operand (Var p) s` >> simp[]
QED

Theorem for_dynamic_add_path_ptr[local]:
  FLOOKUP G off = NONE /\
  op_taint tn (Var p) = {} /\ op_taint tn (Var off) = {} /\
  lookup_var p s = SOME a /\ lookup_var off s = SOME b /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ADD [Var p; Var off] [q]) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (set_prov G [q] (FLOOKUP G p))
    (tn with t_var := tn.t_var |+ (q,{}))
    (OK ((update_var q (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var p; Var off] [q]) s =
    OK (update_var q (a+b) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [Var p; Var off] [q])
      (update_var q (a+b) s))
    (step_taint (mk_inst id ADD [Var p; Var off] [q]) s
      (update_var q (a+b) s) tn)
    (OK ((update_var q (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule copy_len_binop_zero_path_ptr >> simp[GSYM mk_inst_def]) >>
  `step_prov PG G (mk_inst id ADD [Var p; Var off] [q])
     (update_var q (a+b) s) = set_prov G [q] (FLOOKUP G p) /\
   step_taint (mk_inst id ADD [Var p; Var off] [q]) s
     (update_var q (a+b) s) tn = tn with t_var := tn.t_var |+ (q,{})` by
    (irule for_dynamic_add_ghost >> simp[]) >> gvs[]
QED

Theorem for_element_address_path_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var idx; Lit (n2w stride)] [off]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 ADD [Var p; Var off] [q]) /\
  lookup_var idx s = SOME (n2w k) /\ lookup_var p s = SOME w /\
  op_taint tn (Var idx) = {} /\ op_taint tn (Var p) = {} /\
  p <> off /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (set_prov (DRESTRICT G (COMPL {off})) [q] (FLOOKUP G p))
    (tn with t_var := (tn.t_var |+ (off,{})) |+ (q,{}))
    (OK ((update_var q (w + n2w k * n2w stride)
      (update_var off (n2w k * n2w stride) s))
      with vs_inst_idx := SUC (SUC s.vs_inst_idx)))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {off}))
    (tn with t_var := tn.t_var |+ (off,{}))
    (OK ((update_var off (n2w k * n2w stride) s)
      with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule for_mul_scalar_path_ptr >> simp[] >> metis_tac[]) >>
  qabbrev_tac `sm = (update_var off (n2w k * n2w stride) s)
    with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `tm = tn with t_var := tn.t_var |+ (off,{})` >>
  qabbrev_tac `Gm = DRESTRICT G (COMPL {off})` >>
  `gas_path_ptr D 0 ctx fn PG Gm tm sm 0
    (set_prov Gm [q] (FLOOKUP Gm p))
    (tm with t_var := tm.t_var |+ (q,{}))
    (OK ((update_var q (w + n2w k * n2w stride) sm)
      with vs_inst_idx := SUC sm.vs_inst_idx))` by
    (irule for_dynamic_add_path_ptr >>
     simp[Abbr `sm`, Abbr `tm`, Abbr `Gm`, update_var_def, lookup_var_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     gvs[lookup_var_def, op_taint_def] >>
     qexistsl_tac [`id2`, `off`] >> simp[]) >>
  rev_drule gas_path_ptr_then >> disch_then drule >>
  simp[Abbr `sm`, Abbr `tm`, Abbr `Gm`, update_var_def, FLOOKUP_DRESTRICT]
QED

Theorem for_element_address_frame:
  sf = ((update_var q (w+delta) (update_var off delta s))
    with vs_inst_idx := SUC (SUC s.vs_inst_idx)) /\
  Gf = set_prov (DRESTRICT G (COMPL {off})) [q] (FLOOKUP G p) /\
  tnf = (tn with t_var := (tn.t_var |+ (off,{})) |+ (q,{})) ==>
  lookup_var q sf = SOME (w+delta) /\ FLOOKUP Gf q = FLOOKUP G p /\
  op_taint tnf (Var q) = {} /\ sf.vs_memory = s.vs_memory /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
  (!v. v <> off /\ v <> q ==>
    lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
    op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> Cases_on `FLOOKUP G p` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       set_prov_def, FLOOKUP_DRESTRICT, op_taint_def]
QED

Theorem for_local_element_address_path_covered_ptr:
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  entry.type = ArrayTV tv (Fixed n) /\ lookup_var p s = SOME w /\ k < n /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id MUL [Var idx; Lit (n2w (type_memory_size tv))] [off]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst id2 ADD [Var p; Var off] [q]) /\
  lookup_var idx s = SOME (n2w k) /\
  op_taint tn (Var idx) = {} /\ op_taint tn (Var p) = {} /\
  p <> off /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    ptr_covers Gf tnf q sf (type_memory_size tv) /\
    lookup_var q sf = SOME (w + n2w k * n2w (type_memory_size tv)) /\
    FLOOKUP Gf q = FLOOKUP G p /\ op_taint tnf (Var q) = {} /\
    sf.vs_memory = s.vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!v. v <> off /\ v <> q ==>
      lookup_var v sf = lookup_var v s /\ FLOOKUP Gf v = FLOOKUP G v /\
      op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  drule_all for_element_address_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK sf` >>
  qmatch_asmsub_abbrev_tac `set_prov gm [q] gp` >>
  qabbrev_tac `Gf = set_prov gm [q] gp` >>
  qabbrev_tac `tf = tn with t_var := (tn.t_var |+ (off,{})) |+ (q,{})` >>
  qexistsl_tac [`Gf`, `tf`, `sf`] >> conj_tac
  >- simp[Abbr `Gf`, Abbr `tf`] >>
  conj_asm2_tac
  >- (gvs[Abbr `gp`] >>
      drule_all for_local_array_element_coverage >> simp[]) >>
  simp[Abbr `gp`] >> irule for_element_address_frame >>
  simp[Abbr `sf`, Abbr `Gf`, Abbr `tf`, Abbr `gm`]
QED
