Theory bodyPtrIfExpBytesPost
Ancestors
  bodyPtrIfExpBytesCounted typedCopyRobustTransportPtr representationCleanPtr
  valueCopyBytes valueEncodingProps robustCopyTransportPtr loweringPosts
  exprSimDefs exprSimProps venomMemProofs bodyPtrDefs list arithmetic
  exprSimBufferStore valueEncodingProofs

Theorem bytestring_copy_robust_destination:
  !tn tnf s sf a b len n tenv sty dty stv dtv v.
    sf.vs_memory = (mcopy b a n s).vs_memory /\
    (!i. i < n ==> (b+i IN tnf.t_mem <=> a+i IN tn.t_mem)) /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory stv v a m) ==>
    !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory dtv v b m
Proof
  rpt gen_tac >> strip_tac >>
  `val_in_memory stv v a s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `(!i. a <= i /\ i < a+32 ==> i NOTIN tn.t_mem) /\
   (!i. a+32 <= i /\ i < a+32+len ==> i NOTIN tn.t_mem)` by
    (qspecl_then [`tenv`, `sty`, `stv`] mp_tac bytestring_type_value >>
     asm_rewrite_tac[] >> strip_tac >> gvs[] >>
     FIRST [drule robust_val_in_memory_bytes_clean,
            drule robust_val_in_memory_string_clean] >> simp[]) >>
  `32 <= n /\ 32+len <= n` by
    (qspec_then `32` mp_tac DIVISION >>
     (impl_tac >- decide_tac) >>
     disch_then (qspec_then `len+31` strip_assume_tac) >>
     qpat_x_assum `n = _` SUBST1_TAC >> decide_tac) >>
  rpt gen_tac >> disch_tac >>
  `mem_bytes_at (b+0) 32 m = mem_bytes_at (a+0) 32 s.vs_memory` by
    (irule clean_copied_window >>
     qexistsl_tac [`n`, `sf`, `tn.t_mem`, `tnf.t_mem`] >> simp[]) >>
  `mem_bytes_at (b+32) len m = mem_bytes_at (a+32) len s.vs_memory` by
    (irule clean_copied_window >>
     qexistsl_tac [`n`, `sf`, `tn.t_mem`, `tnf.t_mem`] >> simp[]) >>
  `val_in_memory dtv v a s.vs_memory` by
    (irule bytestring_val_in_memory_transfer >> conj_tac >- simp[] >>
     qexistsl_tac [`sty`, `dty`, `tenv`, `stv`] >> simp[]) >>
  qpat_x_assum `!m. mem_agree_outside tn.t_mem _ m ==> _` kall_tac >>
  qpat_x_assum `val_in_memory stv v _ _` kall_tac >>
  drule_all bytestring_type_value >> strip_tac >>
  gvs[valueEncodingTheory.val_in_memory_def,
      valueEncodingTheory.mem_word_at_def, GSYM valueEncodingTheory.mem_bytes_at_def]
QED

Theorem bytestring_copy_effects:
  !tn tnf s sf a b n.
    sf.vs_memory = (mcopy b a n s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | b <= i /\ i < b+n}) UNION
      {b+i | i < n /\ a+i IN tn.t_mem} ==>
    (!i. ~(b <= i /\ i < b+n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i < n ==> (b+i IN tnf.t_mem <=> a+i IN tn.t_mem)) /\
    (!i. ~(b <= i /\ i < b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule buffer_mcopy_exterior >> decide_tac) >>
  simp[] >> rpt strip_tac >> simp[] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem compile_store_bytestring_robust_gas_path_ptr:
  !D ctx fn PG sa sb src dst G tn s a b len n tenv sty dty stv dtv v bb.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
        (OK (sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))) /\
      run_inst_seq (emitted_insts sa sb) s = OK sf /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!i. i < n ==> (w2n b+i IN tnf.t_mem <=> w2n a+i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b+n) ==>
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!ft fv p. val_wf ft fv /\
        (p + type_memory_size ft <= w2n b \/ w2n b+n <= p) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bodyPtrIfExpCopyHeaderTheory.robust_bytestring_header >> strip_tac >>
  drule_all compile_store_bytestring_gas_path_ptr >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `(sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s` by
    (`eval_operand (Var src) s = SOME a /\ eval_operand (Var dst) s = SOME b` by
       simp[venomStateTheory.eval_operand_def] >>
     `!x. Var src = Var x \/ Var dst = Var x ==> not_fresh_at sa x` by
       (rpt strip_tac >> gvs[]) >>
     `32 + 32 * word_size len < dimword(:256)` by
       gvs[vfmConstantsTheory.word_size_def] >>
     drule_all buffer_store_bytestring_run >> strip_tac >> gvs[]) >>
  drule_all bytestring_copy_effects >> strip_tac >>
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
     val_in_memory dtv v (w2n b) m` by
    (rpt strip_tac >> irule bytestring_copy_robust_destination >> metis_tac[]) >>
  drule robust_representation_exterior_frame >> disch_then drule >>
  disch_then (assume_tac o SIMP_RULE bool_ss [AND_IMP_INTRO]) >>
  qpat_x_assum `n = _` kall_tac >>
  qpat_x_assum `tnf.t_mem = _` kall_tac >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> asm_rewrite_tac[] >>
  rpt strip_tac >> qpat_x_assum `!ft fv p m. _` irule >> asm_rewrite_tac[]
QED
