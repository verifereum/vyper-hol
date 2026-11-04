(* Primitive normalization consumes the framed word-copy boundary. *)
Theory wordCopyRobustPtr
Ancestors typedCopyPtr valueEncodingProps representationCleanPtr robustCopyTransportPtr
  bodyPtrDefs valueEncoding valueEncodingProofs list venomMemProofs

Theorem compile_store_word_robust_framed_frag_ptr:
  !cx ctx PG R cenv dst dst_ty src src_ty sa sb G tn s a b tv v.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
      ((),sb) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
     (?x. v = FlagV x) \/ (?x. v = DecimalV x)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t st. g = G /\ t = tn /\ st = s)
        (\g t st. g = Gf /\ t = tnf /\ st = sf) R /\
      sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
        sf.vs_memory s.vs_memory /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n b) m) /\
      (!ft fv p. val_wf ft fv /\
        (!i. p <= i /\ i < p + val_footprint ft fv ==>
          ~(w2n b <= i /\ i < w2n b + 32)) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory ft fv p m) ==>
        !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
          val_in_memory ft fv p m)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_prim_clean] >>
  drule_all compile_store_word_framed_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac >- suspend "destination" >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b + 32}`] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Resume compile_store_word_robust_framed_frag_ptr[destination]:
  rpt strip_tac >>
  `mem_bytes_at (w2n b) 32 m = mem_bytes_at (w2n b) 32 sf.vs_memory` by
    (irule LIST_EQ >> simp[] >> rpt strip_tac >>
     rename1 `j < 32` >>
     `w2n b + j NOTIN tnf.t_mem` by simp[] >>
     `mem_bytes_at (w2n b+j) 1 sf.vs_memory = mem_bytes_at (w2n b+j) 1 m` by
       (fs[mem_agree_outside_def] >> metis_tac[]) >>
     qpat_x_assum `mem_bytes_at _ 1 _ = mem_bytes_at _ 1 _` mp_tac >>
     simp[LIST_EQ_REWRITE, EL_mem_bytes_at]) >>
  `val_in_memory tv v (w2n a) s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mem_word_at (w2n b) m = mem_word_at (w2n b) sf.vs_memory` by
    asm_simp_tac bool_ss [mem_word_at_def, GSYM mem_bytes_at_def] >>
  `mem_word_at (w2n b) m = mload (w2n a) s` by
    metis_tac[mstore_mem_word_at_same] >>
  gvs[val_in_memory_def, mem_word_at_eq_mload]
QED

Finalise compile_store_word_robust_framed_frag_ptr

Theorem compile_store_word_robust_frag_ptr:
  !cx ctx PG R cenv dst dst_ty src src_ty sa sb G tn s a b tv v.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
      ((),sb) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
     (?x. v = FlagV x) \/ (?x. v = DecimalV x)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t st. g = G /\ t = tn /\ st = s)
        (\g t st. g = Gf /\ t = tnf /\ st = sf) R /\
      sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
        sf.vs_memory s.vs_memory /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p)) /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n b) m)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all compile_store_word_robust_framed_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED
