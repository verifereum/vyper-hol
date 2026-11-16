(* Same selected bytestring copy packet, with the caller's allocation floor. *)
Theory bodyFullForArrayLocalBytesLo
Ancestors
  forPtrBytes instSeqPtrLo ptrDiscipline venomState

Theorem for_iter_bytes_copy_checked_lo:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  is_bytestring_type ty /\
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_size tv < dimword (:256) /\
  ptr_covers G tn src s (type_memory_size tv) /\
  ptr_covers G tn dst s (type_memory_size tv) /\
  ~ctx_has_dalloca ctx /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  ?sf gf tf.
    (!k. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) gf tf) /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + type_memory_size tv}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
      op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  drule_all for_iter_bytes_copy_checked >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexistsl [`sf`, `gf`, `tf`] >>
  reverse conj_tac >- simp[] >>
  gen_tac >> irule inst_seq_ptr_zero_to_lo >>
  simp[] >> conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
  qexists_tac `D` >> simp[]
QED
