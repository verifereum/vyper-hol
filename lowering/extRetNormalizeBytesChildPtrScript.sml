Theory extRetNormalizeBytesChildPtr
Ancestors
  extRetNormalizeBytesPtr bodyPtrIfExpMaterializedPost bodyPtrDefs
  exprSimProps valueCopyBytes valueTypingMemoryProps valueEncoding
  valueEncodingProofs vyperTyping vfmConstants fragExec compileEnv
  exprLoweringProps venomState venomExecSemantics ptrDiscipline ptrCoverage
  reasonCopySourcePtr bodyPtrBopTypedBytes finite_map list rich_list arithmetic

(* A child needs coverage as well as its robust semantic value.  In
   particular the padded runtime source window is not inferred from the
   larger destination layout.  Padding taint is copied, not erased. *)
Theorem normalize_bytes_child_counted_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory stv v (w2n a) m)) /\
  ptr_covers G tn src s (val_store_size stv v) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword(:256) /\ n < dimword(:256) ==>
  n <= type_memory_size dtv /\
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!i. ~(w2n b <= i /\ i < w2n b+type_memory_size dtv) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n b <= i /\ i < w2n b+type_memory_size dtv)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type sty` by
    metis_tac[bop_machine_word_not_bytestring] >>
  `ptr_val_ok cx sty v (Var src) G tn s` by
    (irule ifexp_materialized_ptr_post >>
     simp[] >> qexistsl_tac [`val_store_size stv v`, `a`] >>
     simp[eval_operand_def]) >>
  `val_store_size dtv v = n` by
    (qspecl_then [`get_tenv cx`, `dty`, `dtv`] mp_tac bytestring_type_value >>
     asm_rewrite_tac[] >> strip_tac >> gvs[] >>
     gvs[value_has_type_def, val_store_size_def, word_size_def]) >>
  `n <= type_memory_size dtv` by
    metis_tac[value_has_type_memory_wf, val_store_size_le] >>
  `ptr_covers G tn dst s n` by
    metis_tac[ptr_covers_mono] >>
  drule_all normalize_bytes_robust_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  simp[] >> qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac
  >- (qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _;
        vs_inst_idx := _|>) = s` mp_tac >>
      simp[venom_state_component_equality] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!ft fv p. _` (qspecl_then [`ft`, `fv`, `p`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    qpat_x_assum `!i. p <= i /\ _ ==> _` (qspec_then `i` mp_tac) >>
    decide_tac)) >>
  simp[]
QED
