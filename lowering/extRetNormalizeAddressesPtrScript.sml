Theory extRetNormalizeAddressesPtr
Ancestors
  extRetBytesCopyCountedPtr typedCopyLoopHeaderPtr typedCopyPtr
  fragGasPathPtr fragGasSeqPtr fragExec compileEnv context emitHelper
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  bodyPtrDefs words finite_map pred_set arithmetic

Theorem mul_slice_counted_ptr[local]:
  fn_has_code sa sb fn /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst id MUL [left;right] [out]] /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
    (OK ((update_var out (a*b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_prov PG G (mk_inst id MUL [left;right] [out]) (update_var out (a*b) s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id MUL [left;right] [out]) s (update_var out (a*b) s) tn =
     (tn with t_var := tn.t_var |+ (out,{}))` by
    (irule typed_copy_loop_arith_ghost_clean >> simp[update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst id MUL [left;right] [out]) s =
     OK (update_var out (a*b) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id MUL [left;right] [out]) s` by
    (irule typed_copy_loop_test_check >> simp[update_var_def] >> metis_tac[]) >>
  qpat_x_assum `step_prov _ _ _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  qpat_x_assum `step_taint _ _ _ _ = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule emitted_step_counted_ptr >> simp[mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]
QED

Theorem add_slice_counted_ptr[local]:
  fn_has_code sa sb fn /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [mk_inst id ADD [left;right] [out]] /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ADD [left;right] [out]) (update_var out (a+b) s))
    (step_taint (mk_inst id ADD [left;right] [out]) s (update_var out (a+b) s) tn)
    (OK ((update_var out (a+b) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [left;right] [out]) s = OK (update_var out (a+b) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def, exec_pure2_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id ADD [left;right] [out]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  irule emitted_step_counted_ptr >> simp[mk_inst_def, is_terminator_def] >>
  qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]
QED

(* The instruction-slice interface does not assume that either child has a
   positive footprint.  In particular it does not invent source provenance. *)
Theorem normalize_array_addresses_execution_counted_ptr:
  lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
  lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
  op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {} /\
  ALL_DISTINCT [so;doff;sp;dp] /\
  (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
  w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) /\
  si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
  si.cs_current_insts = sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [Var sr;Var so] [sp];
     mk_inst (id+3) ADD [Var dr;Var doff] [dp]] /\
  fn_has_code sb si fn /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = si.cs_current_bb /\
    sf.vs_inst_idx = LENGTH si.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
    lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. ~MEM p [so;doff;sp;dp] ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (* Exact ADD ghosts permit coverage to be attached to these same witnesses. *)
    ?s2 t3 s3 t4 g2 tn2 g3 tn3.
      s2 = ((update_var doff (n2w (i*ds))
        (update_var so (n2w (i*ss)) s)) with vs_inst_idx := s.vs_inst_idx+2) /\
      t3 = update_var sp (a+n2w (i*ss)) s2 /\
      s3 = (t3 with vs_inst_idx := s.vs_inst_idx+3) /\
      t4 = update_var dp (b+n2w (i*ds)) s3 /\
      sf = (t4 with vs_inst_idx := s.vs_inst_idx+4) /\
      g2 = DRESTRICT (DRESTRICT G (COMPL {so})) (COMPL {doff}) /\
      tn2 = (tn with t_var := (tn.t_var |+ (so,{})) |+ (doff,{})) /\
      g3 = step_prov PG g2 (mk_inst (id+2) ADD [Var sr;Var so] [sp]) t3 /\
      tn3 = step_taint (mk_inst (id+2) ADD [Var sr;Var so] [sp]) s2 t3 tn2 /\
      Gf = step_prov PG g3 (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) t4 /\
      tnf = step_taint (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) s3 t4 tn3
Proof
  strip_tac >>
  qabbrev_tac `s1 = (update_var so (n2w (i*ss)) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `s2 = (update_var doff (n2w (i*ds)) s1) with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `t3 = update_var sp (a+n2w (i*ss)) s2` >>
  qabbrev_tac `s3 = t3 with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `t4 = update_var dp (b+n2w (i*ds)) s3` >>
  qabbrev_tac `s4 = t4 with vs_inst_idx := SUC s3.vs_inst_idx` >>
  qabbrev_tac `g1 = DRESTRICT G (COMPL {so})` >>
  qabbrev_tac `g2 = DRESTRICT g1 (COMPL {doff})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (so,{})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (doff,{})` >>
  qabbrev_tac `g3 = step_prov PG g2 (mk_inst (id+2) ADD [Var sr;Var so] [sp]) t3` >>
  qabbrev_tac `tn3 = step_taint (mk_inst (id+2) ADD [Var sr;Var so] [sp]) s2 t3 tn2` >>
  qabbrev_tac `g4 = step_prov PG g3 (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) t4` >>
  qabbrev_tac `tn4 = step_taint (mk_inst (id+3) ADD [Var dr;Var doff] [dp]) s3 t4 tn3` >>
  qexistsl_tac [`g4`,`tn4`,`s4`] >>
  qabbrev_tac `c1 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so]]` >>
  qabbrev_tac `c2 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff]]` >>
  qabbrev_tac `c3 = sb with cs_current_insts := sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [Var sr;Var so] [sp]]` >>
  `cs_extends sb c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\
   cs_extends c3 si /\ cs_extends c1 si /\ cs_extends c2 si` by
    simp[Abbr `c1`, Abbr `c2`, Abbr `c3`, cs_extends_def,
         listTheory.APPEND_ASSOC] >>
  `fn_has_code sb c1 fn /\ fn_has_code c1 c2 fn /\
   fn_has_code c2 c3 fn /\ fn_has_code c3 si fn` by
    metis_tac[fn_has_code_split] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (simp_tac (srw_ss()) [Abbr `g1`, Abbr `tn1`, Abbr `s1`, GSYM word_mul_n2w] >>
     irule mul_slice_counted_ptr >>
     simp[eval_operand_def, op_taint_def] >>
     qexistsl_tac [`id`,`Var ctr`,`Lit (n2w ss)`,`sb`,`c1`] >>
     gvs[Abbr `c1`, eval_operand_def, op_taint_def]) >>
  `gas_path_ptr D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)` by
    (simp_tac (srw_ss()) [Abbr `g2`, Abbr `tn2`, Abbr `s2`, GSYM word_mul_n2w] >>
     irule mul_slice_counted_ptr >>
     simp[Abbr `s1`, update_var_def] >>
     qexistsl_tac [`id+1`,`Var ctr`,`Lit (n2w ds)`,`c1`,`c2`] >>
     gvs[Abbr `c1`, Abbr `c2`, Abbr `tn1`,
         eval_operand_def, op_taint_def, lookup_var_def, update_var_def,
         FLOOKUP_UPDATE, listTheory.APPEND_ASSOC]) >>
  `gas_path_ptr D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)` by
    (simp_tac (srw_ss()) [Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `t3`] >>
     irule add_slice_counted_ptr >>
     simp[Abbr `s2`, Abbr `s1`, update_var_def] >>
     qpat_x_assum `Abbrev (g4 = _)` kall_tac >>
     qpat_x_assum `Abbrev (tn4 = _)` kall_tac >>
     qpat_x_assum `Abbrev (s4 = _)` kall_tac >>
     qpat_x_assum `Abbrev (t4 = _)` kall_tac >>
     gvs[Abbr `tn2`, Abbr `tn1`, eval_operand_def, op_taint_def,
         lookup_var_def, FLOOKUP_UPDATE] >>
     qexistsl_tac [`c2`,`c3`] >>
     gvs[Abbr `c2`, Abbr `c3`, listTheory.APPEND_ASSOC]) >>
  `gas_path_ptr D 0 ctx fn PG g3 tn3 s3 0 g4 tn4 (OK s4)` by
    (simp_tac (srw_ss()) [Abbr `g4`, Abbr `tn4`, Abbr `s4`, Abbr `t4`] >>
     irule add_slice_counted_ptr >>
     simp[Abbr `s3`, Abbr `t3`, Abbr `s2`, Abbr `s1`, update_var_def] >>
     qpat_x_assum `Abbrev (g3 = _)` kall_tac >>
     gvs[Abbr `tn3`, copy_len_binop_ghost_frame] >>
     gvs[Abbr `tn2`, Abbr `tn1`, eval_operand_def, op_taint_def,
         lookup_var_def, FLOOKUP_UPDATE] >>
     qexistsl_tac [`c3`,`si`] >>
     gvs[Abbr `c3`, listTheory.APPEND_ASSOC]) >>
  conj_tac
  >- metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES] >>
  reverse (rpt conj_tac)
  >- (qexistsl_tac [`s2`,`t3`,`s3`,`t4`,`g2`,`tn2`,`g3`,`tn3`] >>
      simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
           Abbr `t4`, Abbr `t3`, Abbr `g4`, Abbr `g3`, Abbr `g2`, Abbr `g1`,
           Abbr `tn4`, Abbr `tn3`, Abbr `tn2`, Abbr `tn1`, update_var_def,
           arithmeticTheory.ADD1]) >>
  simp[Abbr `tn4`, Abbr `tn3`, Abbr `t4`, Abbr `t3`,
       copy_len_binop_ghost_frame, Abbr `tn2`, Abbr `tn1`] >>
  simp[Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       GSYM word_add_n2w, arithmeticTheory.ADD1] >>
  simp[Abbr `g4`, Abbr `g3`, Abbr `g2`, Abbr `g1`,
       copy_len_binop_ghost_frame, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` kall_tac) >>
  simp[FLOOKUP_UPDATE, venom_state_component_equality] >>
  simp[step_taint_def, mk_inst_def, imm_taint_def, adopt_reset_def] >> gvs[]
QED

Theorem normalize_array_addresses_counted_ptr:
  !ctr s i tn sr dr a b G S T so doff sp dp ss ds sn dn si sb id fn ctx D PG.
  lookup_var ctr s = SOME (n2w i) /\ op_taint tn (Var ctr) = {} /\
  lookup_var sr s = SOME a /\ lookup_var dr s = SOME b /\
  ptr_covers G tn sr s S /\ ptr_covers G tn dr s T /\
  ALL_DISTINCT [so;doff;sp;dp] /\
  (!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ sr <> v /\ dr <> v) /\
  i*ss < S /\ i*ss+sn <= S /\ i*ds < T /\ i*ds+dn <= T /\
  w2n a+i*ss < dimword(:256) /\ w2n b+i*ds < dimword(:256) /\
  si.cs_blocks = sb.cs_blocks /\ si.cs_current_bb = sb.cs_current_bb /\
  si.cs_current_insts = sb.cs_current_insts ++
    [mk_inst id MUL [Var ctr;Lit (n2w ss)] [so];
     mk_inst (id+1) MUL [Var ctr;Lit (n2w ds)] [doff];
     mk_inst (id+2) ADD [Var sr;Var so] [sp];
     mk_inst (id+3) ADD [Var dr;Var doff] [dp]] /\
  fn_has_code sb si fn /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = si.cs_current_bb /\
    sf.vs_inst_idx = LENGTH si.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var sp sf = SOME (n2w (w2n a+i*ss)) /\
    lookup_var dp sf = SOME (n2w (w2n b+i*ds)) /\
    ptr_covers Gf tnf sp sf sn /\ ptr_covers Gf tnf dp sf dn /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!p. ~MEM p [so;doff;sp;dp] ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint tn (Var sr) = {} /\ op_taint tn (Var dr) = {}` by
    gvs[ptr_covers_def] >>
  drule_all normalize_array_addresses_execution_counted_ptr >>
  disch_then (qspecl_then [`PG`,`G`,`D`] strip_assume_tac) >>
  `ptr_covers g3 tn3 sp t3 sn` by
    (qpat_assum `g3 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tn3 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `t3 = _` (fn th => rewrite_tac[th]) >>
     irule typed_copy_loop_dynamic_offset_covers >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          ptr_covers_def, FLOOKUP_DRESTRICT, op_taint_def] >>
     conj_tac >- gvs[lookup_var_def] >>
     conj_tac >- gvs[lookup_var_def] >>
     qexists_tac `S'` >> gvs[ptr_covers_def, lookup_var_def, op_taint_def]) >>
  `ptr_covers g3 tn3 sp s3 sn` by
    gvs[ptr_covers_def, lookup_var_def] >>
  `ptr_covers Gf tnf sp sf sn` by
    (qpat_assum `Gf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tnf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `sf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `t4 = _` (fn th => rewrite_tac[th]) >>
     `sp <> dp` by gvs[] >>
     simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
     qpat_x_assum `ptr_covers g3 tn3 sp s3 sn` mp_tac >>
     simp[ptr_covers_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `ptr_covers g3 tn3 dr s3 T'` by
    (qpat_assum `g3 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tn3 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `s3 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `t3 = _` (fn th => rewrite_tac[th]) >>
     `dr <> sp /\ dr <> so /\ dr <> doff` by gvs[] >>
     simp[ptr_covers_def, copy_len_binop_ghost_frame] >>
     gvs[ptr_covers_def, lookup_var_def, update_var_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]) >>
  `ptr_covers Gf tnf dp t4 dn` by
    (qpat_assum `Gf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tnf = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `t4 = _` (fn th => rewrite_tac[th]) >>
     irule typed_copy_loop_dynamic_offset_covers >> simp[] >>
     conj_tac >- gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     conj_tac >- gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     qexists_tac `T'` >> gvs[]) >>
  `ptr_covers Gf tnf dp sf dn` by
    gvs[ptr_covers_def, lookup_var_def] >>
  qexistsl_tac [`Gf`,`tnf`,`sf`] >> simp[]
QED
