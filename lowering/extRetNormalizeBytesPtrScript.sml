Theory extRetNormalizeBytesPtr
Ancestors
  bodyPtrIfExpBytesResources bodyPtrIfExpBytesPost
  bodyPtrMakeArrayPrimitiveInstall stmtReasonLitFragMemory
  bodyPtrDefs exprSimProps valueCopyBytes robustCopyTransportPtr
  valueEncoding valueEncodingProofs vyperTyping vfmConstants
  fragExec compileEnv exprLoweringProps venomState venomExecSemantics
  ptrDiscipline finite_map list rich_list arithmetic

(* Padded runtime store coverage is supplied by ptr_mem_ok, not by
   cleanliness of the live footprint. Padding taint is transported. *)
Theorem normalize_bytes_robust_counted_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_val_ok cx sty v (Var src) G tn s /\
  is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword(:256) /\ n < dimword(:256) /\
  ptr_covers G tn dst s n ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
      val_in_memory dtv v (w2n b) m) /\
    (!ft fv p. val_wf ft fv /\
      (!i. p <= i /\ i < p + val_footprint ft fv ==>
        ~(w2n b <= i /\ i < w2n b+n)) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory ft fv p m) ==>
      !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory ft fv p m)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n <= val_store_size stv v` by
    (qspecl_then [`get_tenv cx`, `sty`, `stv`] mp_tac bytestring_type_value >>
     asm_rewrite_tac[] >> strip_tac >> gvs[] >>
     gvs[value_has_type_def, val_store_size_def, word_size_def]) >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule_all ifexp_bytes_source_resources >> strip_tac >>
  `ptr_covers G tn src s n /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory stv v (w2n a) m)` by metis_tac[operand_11] >>
  drule bytestring_store_install_shape >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    simp[emitted_insts_def, DROP_APPEND1] >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all compile_store_bytestring_robust_gas_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `sf.vs_current_bb = s.vs_current_bb /\ ~sf.vs_halted` by
    (qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
     simp[Once venom_state_component_equality]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    metis_tac[LENGTH_APPEND] >>
  qpat_x_assum `n = _` kall_tac >>
  qexistsl_tac [`Gf`, `tnf`,
    `sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`] >>
  simp[] >>
  conj_tac
  >- (qpat_x_assum `(sf with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
      simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `!i. _ ==> mem_bytes_at i 1 sf.vs_memory = _` mp_tac >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def] >>
      qpat_x_assum `!p. not_fresh_at sa p ==> _` drule >>
      simp[lookup_var_def]) >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b+n}`] >>
  simp[]
QED
