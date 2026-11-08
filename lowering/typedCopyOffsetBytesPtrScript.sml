(* Resource-based offset creation followed by robust bytestring copying. *)
Theory typedCopyOffsetBytesPtr
Ancestors typedCopyOffsetPtr typedCopyRobustFramePtr

Theorem compile_with_byte_offset_old_not_fresh[local]:
  compile_with_byte_offset op off sa = (src,sb) /\ not_fresh_at sa q ==>
  not_fresh_at sb q
Proof
  strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_with_byte_offset_def] >> Cases_on `off = 0` >>
     simp[compileEnvTheory.comp_return_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
       compileEnvTheory.emit_def] >> rpt strip_tac >> gvs[]) >>
  gvs[compileEnvTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem compile_offset_bytestring_robust_frag_ptr:
  !cx ctx PG R root off sa src sb dst sc G tn s a b total len n
   tenv sty dty stv dtv v.
    compile_with_byte_offset (Var root) off sa = (src,sb) /\
    compile_store_bytestring src (Var dst) sb = ((),sc) /\
    not_fresh_at sa root /\ not_fresh_at sa dst /\
    lookup_var root s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn root s total /\ ptr_covers G tn dst s n /\
    off < total /\ off+n <= total /\ w2n a+off < dimword(:256) /\
    n = 32 + 32 * ((len+31) DIV 32) /\
    len+31 < dimword(:256) /\ n < dimword(:256) /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a+off) m) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sc
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mcopy (w2n b) (w2n a+off) n s).vs_memory /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!j. j < n ==> (w2n b+j IN tnf.t_mem <=> w2n a+off+j IN tn.t_mem)) /\
      (!j. ~(w2n b <= j /\ j < w2n b+n) ==>
        (j IN tnf.t_mem <=> j IN tn.t_mem)) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. not_fresh_at sa q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >> (
  drule_all compile_with_byte_offset_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  rename1 `lookup_var p s1 = SOME (n2w (w2n a+off))` >>
  `not_fresh_at sb dst` by
    (irule compile_with_byte_offset_old_not_fresh >> metis_tac[]) >>
  `lookup_var dst s1 = SOME b /\ ptr_covers Gf tnf dst s1 n` by
    (qpat_assum `!q. not_fresh_at sa q ==> _` (qspec_then `dst` strip_assume_tac) >>
     gvs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `!m. mem_agree_outside tnf.t_mem s1.vs_memory m ==>
      val_in_memory stv v (w2n (n2w (w2n a+off):256 word)) m` by
    (simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  qpat_x_assum `src = Var p` SUBST_ALL_TAC >>
  drule_at (Pat `compile_store_bytestring _ _ _ = _`)
    compile_store_bytestring_robust_ambient_frag_ptr >>
  disch_then (drule_at (Pat `lookup_var p _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ p _ _`)) >>
  simp[] >>
  disch_then (fn th =>
    qpat_assum `evaluate_type tenv sty = SOME stv`
      (mp_then (Pat `evaluate_type _ _ = SOME _`) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `evaluate_type tenv dty = SOME dtv`
      (mp_then (Pat `evaluate_type _ _ = SOME _`) mp_tac th)) >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`, `len`] mp_tac) >>
  disch_then (qspec_then `v` mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl [`G2`, `tn2`, `s2`] >>
  conj_tac >- suspend "compose" >>
  gvs[] >> conj_tac
  >- (qpat_x_assum `s2.vs_memory = _` mp_tac >>
      simp[venomExecSemanticsTheory.mcopy_def,
        venomStateTheory.write_memory_with_expansion_def]) >>
  simp[] >> conj_tac >- metis_tac[] >> rpt strip_tac >>
  `not_fresh_at sb q` by
    (irule compile_with_byte_offset_old_not_fresh >> metis_tac[]) >>
  metis_tac[])
QED

Resume compile_offset_bytestring_robust_frag_ptr[compose]:
  markerLib.RESUME_TAC >> (
  `cs_extends sb sc` by
    (mp_tac (Q.SPECL [`Var p`, `Var dst`, `sb`]
       exprLoweringPropsTheory.ci_mono_compile_store_bytestring) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  irule fragExecPtrTheory.frag_exec_ptr_seq >>
  qpat_assum `frag_exec_ptr _ _ _ sa sb _ _ _` (irule_at Any) >> simp[])
QED

Finalise compile_offset_bytestring_robust_frag_ptr
