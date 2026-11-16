(* Exact-size local-array copy: retain the selected execution and ghosts,
   transporting only the pointer certificate's lower bound. *)
Theory bodyFullForArrayLocalBulkLo
Ancestors forPtrBulk instSeqPtrLo

Theorem for_iter_bulk_copy_checked_lo:
  !lo cenv src dst stride ty sa sb n G tn s a b ctx tv v D fn PG.
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  compile_iter_elem_copy cenv (Var src) (Var dst) stride LocMemory F ty ty
    sa = ((),sb) /\
  type_memory_bytes cenv ty = n /\ n < dimword (:256) /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ~ctx_has_dalloca ctx /\ val_wf tv v /\ val_footprint tv v <= n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?tf sf.
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G tf /\
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b + n}
      sf.vs_memory s.vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tf (Var p) = op_taint tn (Var p)) /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all for_iter_bulk_copy_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl [`tf`, `sf`] >> simp[] >>
  irule inst_seq_ptr_zero_to_lo >> simp[] >> qexists_tac `D` >> simp[]
QED
