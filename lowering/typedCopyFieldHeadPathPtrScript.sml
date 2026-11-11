(* Two offsets followed by a hypothetical recursive typed copy. *)
Theory typedCopyFieldHeadPathPtr
Ancestors
 typedCopyOffsetClosedPathPtr placeMemoryFieldsForward fragGasPathPtr
 fragExec context compileEnv exprLoweringProps loweringStateRelDefs
 typedCopyPtr typedMemoryCopy bodyPtrDefs vyperTypeSystem words
 venomState finite_map ptrDiscipline arithmetic

Theorem compile_typed_copy_field_head_path_ptr:
 !D ctx func PG cenv tenv dt st.
 (!root off sa op sb G tn s a cap n.
   compile_with_byte_offset (Var root) off sa = (op,sb) /\
   not_fresh_at sa root /\ lookup_var root s = SOME a /\
   ptr_covers G tn root s cap /\ off <= cap /\ off+n <= cap /\
   w2n a + off < dimword(:256) /\ fn_has_code sa sb func /\
   s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   ~s.vs_halted /\ ~ctx_has_dalloca ctx ==>
   cs_extends sa sb /\ ?p Gf tnf sf.
   op = Var p /\ lookup_var p sf = SOME (n2w (w2n a+off)) /\
   ptr_covers Gf tnf p sf n /\ not_fresh_at sb p /\
   gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
   sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!q. not_fresh_at sa q ==>
    lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
    op_taint tnf (Var q) = op_taint tn (Var q))) /\
 (!dst src sa sb G tn s a b dtv stv v.
   acyclic_struct_metadata cenv.ce_struct_fields /\
   sfields_tenv_consistent cenv.ce_struct_fields tenv /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv st dt /\ evaluate_type tenv st = SOME stv /\
   evaluate_type tenv dt = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed cenv (Var dst) dt (Var src) st sa = ((),sb) /\
   not_fresh_at sa dst /\ not_fresh_at sa src /\
   lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
   ptr_covers G tn src s (type_memory_bytes cenv st) /\
   ptr_covers G tn dst s (type_memory_bytes cenv dt) /\
   w2n a + type_memory_bytes cenv st < dimword(:256) /\
   w2n b + type_memory_bytes cenv dt < dimword(:256) /\
   (w2n a + type_memory_bytes cenv st <= w2n b \/
    w2n b + type_memory_bytes cenv dt <= w2n a) /\
   fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
   ~ctx_has_dalloca ctx /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory stv v (w2n a) m) ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
   (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
    op_taint tnf (Var p) = op_taint tn (Var p)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + type_memory_bytes cenv dt) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n b) m)) ==>
 !dst src doff soff a0 a1 a2 a3 dp sp G tn s dw sw DN scap dtv stv v.
 acyclic_struct_metadata cenv.ce_struct_fields /\
 sfields_tenv_consistent cenv.ce_struct_fields tenv /\
 (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
   ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
     sz = type_memory_size tv) fields) /\
 type_widens_to tenv st dt /\ evaluate_type tenv st = SOME stv /\
 evaluate_type tenv dt = SOME dtv /\
 value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
 compile_with_byte_offset (Var dst) doff a0 = (dp,a1) /\
 compile_with_byte_offset (Var src) soff a1 = (sp,a2) /\
 compile_store_memory_typed cenv dp dt sp st a2 = ((),a3) /\
 not_fresh_at a0 dst /\ not_fresh_at a0 src /\
 lookup_var dst s = SOME dw /\ lookup_var src s = SOME sw /\
 ptr_covers G tn dst s DN /\ ptr_covers G tn src s scap /\
 doff + type_memory_bytes cenv dt <= DN /\
 soff + type_memory_bytes cenv st <= scap /\
 w2n dw + DN < dimword(:256) /\ w2n sw + scap < dimword(:256) /\
 (w2n dw + DN <= w2n sw \/ w2n sw + scap <= w2n dw) /\
 fn_has_code a0 a3 func /\ s.vs_current_bb = a0.cs_current_bb /\
 s.vs_inst_idx = LENGTH a0.cs_current_insts /\ ~s.vs_halted /\
 ~ctx_has_dalloca ctx /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
  val_in_memory stv v (w2n sw + soff) m) ==>
 cs_extends a0 a3 /\ ?Gf tnf sf.
 gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = a3.cs_current_bb /\
 sf.vs_inst_idx = LENGTH a3.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
  vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
  vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at a0 p ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n dw+doff <= i /\ i < w2n dw+doff+type_memory_bytes cenv dt) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory dtv v (w2n dw+doff) m) /\
 lookup_var dst sf = SOME dw /\ lookup_var src sf = SOME sw /\
 ptr_covers Gf tnf dst sf DN /\ ptr_covers Gf tnf src sf scap
Proof
 rpt gen_tac >>
 disch_then (CONJUNCTS_THEN2 (mk_asm "offset") (mk_asm "child")) >>
 rpt gen_tac >> strip_tac >>
 `cs_extends a0 a1 /\ cs_extends a1 a2 /\ cs_extends a2 a3` by
  (rpt conj_tac
   >- metis_tac[compile_with_byte_offset_extends]
   >- metis_tac[compile_with_byte_offset_extends] >>
   mp_tac (cj 1 ci_mono_typed_memory_family) >>
   simp[ci_mono_def] >> metis_tac[pairTheory.SND]) >>
 `cs_extends a0 a2 /\ cs_extends a0 a3` by metis_tac[cs_extends_trans] >>
 `fn_has_code a0 a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func` by
  metis_tac[fn_has_code_split] >>
 `doff <= DN /\ soff <= scap /\
  w2n dw + doff < dimword(:256) /\ w2n sw + soff < dimword(:256)` by decide_tac >>
 asm "offset" drule_all >>
 strip_tac >>
 rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 G1 tn1 (OK s1)` >>
 `lookup_var src s1 = SOME sw /\ not_fresh_at a1 src` by
  (conj_tac >- simp[] >>
   asm_x "offset" kall_tac >> asm_x "child" kall_tac >>
   `a0.cs_next_var <= a1.cs_next_var` by
    (qpat_assum `compile_with_byte_offset (Var dst) doff a0 = _`
      (mp_then Any mp_tac compile_with_byte_offset_fresh) >> simp[]) >>
   fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `ptr_covers G1 tn1 src s1 scap` by
  gvs[ptr_covers_def] >>
 asm "offset" drule_all >>
 strip_tac >>
 asm_x "offset" kall_tac >>
 rename1 `gas_path_ptr D 0 ctx func PG G1 tn1 s1 0 G2 tn2 (OK s2)` >>
 `a0.cs_next_var <= a1.cs_next_var /\ a1.cs_next_var <= a2.cs_next_var` by
  (conj_tac
   >- (qpat_assum `compile_with_byte_offset (Var dst) doff a0 = _`
       (mp_then Any mp_tac compile_with_byte_offset_fresh) >> simp[]) >>
   qpat_assum `compile_with_byte_offset (Var src) soff a1 = _`
     (mp_then Any mp_tac compile_with_byte_offset_fresh) >> simp[]) >>
 `!q. not_fresh_at a0 q ==> not_fresh_at a1 q /\ not_fresh_at a2 q` by
  (asm_x "child" kall_tac >> fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `lookup_var p s2 = SOME (n2w (w2n dw+doff)) /\ not_fresh_at a2 p` by
  (asm_x "child" kall_tac >> simp[] >>
   fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 `ptr_covers G2 tn2 p s2 (type_memory_bytes cenv dt)` by gvs[ptr_covers_def] >>
 `w2n (n2w (w2n dw+doff):256 word) = w2n dw+doff /\
  w2n (n2w (w2n sw+soff):256 word) = w2n sw+soff` by simp[w2n_n2w, LESS_MOD] >>
 `w2n dw+doff+type_memory_bytes cenv dt < dimword(:256) /\
  w2n sw+soff+type_memory_bytes cenv st < dimword(:256) /\
  (w2n sw+soff+type_memory_bytes cenv st <= w2n dw+doff \/
   w2n dw+doff+type_memory_bytes cenv dt <= w2n sw+soff)` by decide_tac >>
 `!m. mem_agree_outside tn2.t_mem s2.vs_memory m ==>
   val_in_memory stv v (w2n (n2w (w2n sw+soff):256 word)) m` by gvs[] >>
 gvs[] >> asm_x "child"
   (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
 simp[] >> disch_then (qspecl_then [`G2`,`tn2`,`s2`] mp_tac) >>
 simp[w2n_n2w, LESS_MOD] >>
 disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
 first_x_assum drule_all >> strip_tac >>
 `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf)` by
  (map_every (fn q => qpat_assum q mp_tac)
    [`gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 (OK s1)`,
     `gas_path_ptr _ _ _ _ _ G1 tn1 s1 _ G2 tn2 (OK s2)`,
     `gas_path_ptr _ _ _ _ _ G2 tn2 s2 _ Gf tnf (OK sf)`] >>
   rpt (pop_assum kall_tac) >> metis_tac[gas_path_ptr_then, ADD_CLAUSES]) >>
 qexistsl [`Gf`,`tnf`,`sf`] >> simp[] >>
 rpt conj_tac >>
 TRY (rename1 `sf with <|vs_memory := _; vs_vars := _;
   vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = s` >>
   gvs[venom_state_component_equality] >> NO_TAC) >>
 gvs[ptr_covers_def] >> metis_tac[]
QED
