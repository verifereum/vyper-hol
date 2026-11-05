(* Finite counter control segments, before any loop induction. *)
Theory forPtrControl
Ancestors forPtrAdmin forPtrBoundary emitHelperProps venomState venomInst
  venomExecSemantics finite_map ptrDiscipline fragGasPathPtr

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

Theorem for_counter_entry_frame:
  sf = jump_to lbl (update_var ctr 0w s) /\
  Gf = DRESTRICT G (COMPL {ctr}) /\
  tnf = (tn with t_var := tn.t_var |+ (ctr,{})) ==>
  lookup_var ctr sf = SOME 0w /\ FLOOKUP Gf ctr = NONE /\
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
