(* Common counted interface for the nonrecursive typed-copy branches. *)
Theory typedCopyReturnBasePtr
Ancestors
  typedCopyReturnWordPtr typedCopyReturnBytesPtr bodyPtrIfExpBytesInputs
  entryDecodeStaticProps reasonCopySourcePtr typedCopyDomain vyperTypeArgFits
  exprSimBufferStore typedMemoryCopy valueEncoding vyperTypeSystem arithmetic context

Theorem typed_copy_return_base_ptr:
  (is_word_type dty \/ is_bytestring_type dty \/ dty = NoneT) /\
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  w2n a + type_memory_size stv < dimword(:256) /\
  w2n b + type_memory_size dtv < dimword(:256) /\
  regions_disjoint (w2n a) (type_memory_size stv) (w2n b) (type_memory_size dtv) /\
  (type_memory_size stv <> 0 ==> ptr_covers G tn src s (type_memory_size stv)) /\
  (type_memory_size dtv <> 0 ==> ptr_covers G tn dst s (type_memory_size dtv)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n b) m) /\
    (!i. i < w2n b \/ w2n b + type_memory_size dtv <= i ==>
       mem_byte_at t.vs_memory i = mem_byte_at s.vs_memory i /\
       (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type dty`
  >- (`sty = dty` by metis_tac[typed_copy_word_widening] >> gvs[] >>
      `type_memory_size dtv = 32` by metis_tac[word_type_memory_size] >>
      gvs[] >> irule typed_copy_word_robust_counted >> simp[] >>
      goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
      qexistsl_tac [`a`,`tenv`] >> simp[]) >>
  Cases_on `is_bytestring_type dty`
  >- suspend "bytes" >>
  `dty = NoneT` by metis_tac[] >> gvs[] >>
  `sty = NoneT` by
    (Cases_on `sty` >> fs[type_widens_to_def, arg_type_fits_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, type_memory_size_def] >>
  drule_all typed_copy_none_counted >>
  disch_then (qspecl_then [`tn`,`w2n b`,`fn`,`ctx`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`G`,`tn`,`s`] >> simp[]
QED

Resume typed_copy_return_base_ptr[bytes]:
  `is_bytestring_type sty` by metis_tac[typed_copy_bytestring_source] >>
  `type_memory_bytes ce sty = type_memory_size stv /\
   type_memory_bytes ce dty = type_memory_size dtv` by
    (conj_tac >> irule typed_copy_memory_size >> qexists_tac `tenv` >>
     simp[] >> metis_tac[]) >>
  drule_all bytes_typed_padded_size >>
  disch_then (qx_choose_then `len` (map_every assume_tac o CONJUNCTS)) >>
  `?len'. ((?bs. v = BytesV bs /\ len' = LENGTH bs) \/
           (?str. v = StringV str /\ len' = LENGTH str)) /\
    32 + 32 * ((len'+31) DIV 32) <= type_memory_size dtv` by
    metis_tac[bytes_typed_padded_size] >>
  `len' = len` by (gvs[] >> metis_tac[]) >>
  qpat_x_assum `len' = len` SUBST_ALL_TAC >>
  qabbrev_tac `n = 32 + 32 * ((len+31) DIV 32)` >>
  `n <= type_memory_size stv /\ n <= type_memory_size dtv /\ 0 < n` by
    gvs[Abbr `n`] >>
  `len+31 < dimword(:256) /\ n < dimword(:256)` by
    (qspec_then `32` mp_tac DIVISION >> simp[] >>
     disch_then (qspec_then `len+31` strip_assume_tac) >>
     qmatch_asmsub_abbrev_tac `len+31 = _ + residue` >>
     `residue < 32` by simp[Abbr `residue`] >>
     gvs[Abbr `n`] >> decide_tac) >>
  `type_memory_size stv <> 0 /\ type_memory_size dtv <> 0` by decide_tac >>
  `ptr_covers G tn src s n /\ ptr_covers G tn dst s n` by
    (conj_tac >> irule ptr_covers_mono >> metis_tac[]) >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    gvs[Once compile_store_memory_typed_def] >>
  `n = 32 + 32 * ((len+31) DIV 32)` by simp[Abbr `n`] >>
  mp_tac (Q.INST [`cap` |-> `type_memory_size dtv`]
          (SPEC_ALL store_bytestring_counted)) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> qexistsl_tac [`H`,`tm`,`t`] >> simp[] >> rpt strip_tac >>
  `mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tm.t_mem <=> i IN tn.t_mem)` by
    (qpat_x_assum `!i. _ ==> mem_bytes_at _ _ _ = _ /\ _`
      (qspec_then `i` mp_tac) >> simp[]) >> simp[] >>
  qpat_x_assum `mem_bytes_at _ _ _ = _`
    (mp_tac o AP_TERM ``EL 0 : word8 list -> word8``) >>
  simp[buffer_window_byte]
QED

Finalise typed_copy_return_base_ptr
