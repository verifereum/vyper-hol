Theory bodyPtrBytestringBuiltinsUintBody
Ancestors
  bodyPtrBytestringBuiltinsUintBlockInv bodyPtrBytestringBuiltinsUintInvariant
  bodyPtrBytestringBuiltinsUintBlocks bodyPtrBytestringBuiltinsUintArithmetic
  bodyPtrBytestringBuiltinsUintGhost exprSimUint2Str
  fragGasPathPtr fragGasSeqPtr typedCopyPtr ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics finite_map words list rich_list
  codegenRel contextCodegenRel

Theorem uint_pointer_binop_ghost:
  (opc = ADD \/ opc = SUB) ==>
  step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out w s) =
    set_prov G [out] (first_prov G [left;right]) /\
  step_taint (mk_inst id opc [left;right] [out]) s (update_var out w s) tn =
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       store_taint_def, adopt_reset_def, imm_taint_def, range_bytes_def,
       taint_component_equality, out_taint_def] >>
  Cases_on `eval_operand left s` >> simp[]
QED

Theorem uint_pointer_add_site_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [left;right] [out]) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  op_prov G left = SOME site ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (out,site))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (x+y) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all uint_pointer_add_counted_edge >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  simp[uint_pointer_binop_ghost, first_prov_def, set_prov_def]
QED

Theorem uint_pointer_sub_site_edge:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id SUB [Var root;delta] [out]) /\
  lookup_var root s = SOME x /\ eval_operand delta s = SOME (n2w i) /\
  op_taint tn (Var root) = {} /\ op_taint tn delta = {} /\
  FLOOKUP G root = SOME site ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (out,site))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK (update_var out (x-n2w i) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all pointer_sub_counted_edge >>
  disch_then (qspecl_then [`D`, `PG`, `G`] mp_tac) >>
  simp[uint_pointer_binop_ghost, op_prov_def, first_prov_def, set_prov_def]
QED

Theorem u2s_address_counted_ptr:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block (u2s_label a 2) fn.fn_blocks =
    SOME <|bb_label := u2s_label a 2; bb_instructions := u2s_body a (Var p) n|> /\
  s.vs_current_bb = u2s_label a 2 /\ s.vs_inst_idx = 2 /\
  lookup_var p s = SOME (n2w b) /\ lookup_var (u2s_var a 1) s = SOME (n2w i) /\
  FLOOKUP G p = SOME (b,sz) /\ op_taint tn (Var p) = {} /\
  op_taint tn (Var (u2s_var a 1)) = {} /\ i <= n ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (G |+ (u2s_var a 7,(b,sz)) |+ (u2s_var a 8,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}) |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n-i))
      (update_var (u2s_var a 7) (n2w (b+n)) s) with vs_inst_idx := 4))
Proof
  strip_tac >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 (G |+ (u2s_var a 7,(b,sz)))
    (tn with t_var := tn.t_var |+ (u2s_var a 7,{}))
    (OK (update_var (u2s_var a 7) (n2w b + n2w n) s with
      vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule uint_pointer_add_site_edge >> simp[] >>
     qexistsl_tac [`a.cs_next_id+10`, `Var p`, `Lit (n2w n)`] >>
     simp[get_instruction_def, u2s_body_def, u2s_inst_def, eval_operand_def,
          op_taint_def, op_prov_def]) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ g t (OK mid)` >>
  `gas_path_ptr_edge D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 8,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    (irule uint_pointer_sub_site_edge >>
     simp[Abbr `mid`, Abbr `g`, Abbr `t`, update_var_def] >>
     qexistsl_tac [`Var (u2s_var a 1)`, `a.cs_next_id+11`, `u2s_var a 7`] >>
     simp[get_instruction_def, u2s_body_def, u2s_inst_def, eval_operand_def,
          op_taint_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def] >>
     gvs[op_taint_def, lookup_var_def, GSYM word_add_n2w]) >>
  `~(update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx).vs_halted` by
    simp[update_var_def, Abbr `mid`] >>
  `gas_path_ptr D 0 ctx fn PG g t mid 0 (g |+ (u2s_var a 8,(b,sz)))
    (t with t_var := t.t_var |+ (u2s_var a 8,{}))
    (OK (update_var (u2s_var a 8) (n2w (b+n)-n2w i) mid with
      vs_inst_idx := SUC mid.vs_inst_idx))` by
    metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES] >>
  gvs[Abbr `g`, Abbr `t`, Abbr `mid`, update_var_def,
      GSYM word_add_n2w, GSYM n2w_sub] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED
