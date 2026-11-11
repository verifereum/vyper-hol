Theory extRetNormalizeWordPtr
Ancestors
  extRetScalarCopyCountedPtr typedCopyPtr bodyPtrDefs fragGasPathPtr
  representationCleanPtr robustCopyTransportPtr valueEncoding valueEncodingProofs
  valueEncodingProps list venomMemProofs finite_map ptrDiscipline

(* The primitive normalization child: counted execution plus robust footprints. *)
Theorem normalize_word_robust_counted_ptr:
  is_word_type ty /\
  compile_store_memory_typed ce (Var dst) ty (Var src) sty sa = ((),sb) /\
  not_fresh_at sa dst /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
   (?x. v = FlagV x) \/ (?x. v = DecimalV x)) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_prim_clean] >>
  drule_all compile_store_word_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
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
      gvs[val_in_memory_def, mem_word_at_eq_mload]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
    `{i | w2n b <= i /\ i < w2n b + 32}`] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED
