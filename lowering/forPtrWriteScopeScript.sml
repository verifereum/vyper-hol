(* A finite separated write preserves the outer invariant. This is not a
   frame requirement on an arbitrary body callback. *)
Theory forPtrWriteScope
Ancestors bodyPtrDefs forPtrElement forPtrBytes robustCopyTransportPtr
  forPtrScope forPtrElementFrame finite_map pred_set

Theorem ghost_local_after_separated_write:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
  op_taint tf (Var p) = op_taint tn (Var p) /\
  val_wf entry.type entry.value /\
  (!w i. lookup_var p s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
    i NOTIN writes) /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) ==>
  ptr_covers gf tf p sf sz /\
  !w mem. lookup_var p sf = SOME w /\
    mem_agree_outside tf.t_mem sf.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> drule_all ghost_inv_local_ptr >> strip_tac >>
  conj_tac >- metis_tac[for_ptr_covers_transport] >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `tn.t_mem`, `tf.t_mem`, `writes`] >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

Theorem ghost_inv_after_separated_write:
  ghost_inv d cenv cx es G tn s /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf entry.type entry.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
      i NOTIN writes) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es gf tf sf
Proof
  strip_tac >> simp[ghost_inv_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      qpat_x_assum `!p. p IN kept ==> _` drule >> strip_tac >>
      drule_all ghost_local_after_separated_write >> simp[])
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[ghost_inv_def, return_buf_ptr_def] >>
      metis_tac[for_ptr_covers_transport])
  >- (fs[ghost_inv_def] >> metis_tac[])
  >> fs[ghost_inv_def, stor_taint_ok_def]
QED

(* The copy starts with only the outer locals live. In particular it does
   not preserve the previous iteration's binding while overwriting it. *)
Theorem ghost_inv_install_after_separated_write:
  ghost_inv d cenv cx es G tn s /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name old p sz.
    lookup_scopes name es.scopes = SOME old /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf old.type old.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint old.type old.value ==>
      i NOTIN writes) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  sf.vs_call_ctx = s.vs_call_ctx /\ sf.vs_accounts = s.vs_accounts /\
  sf.vs_transient = s.vs_transient /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  (!p sz. FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers gf tf p sf sz /\
    !w mem. lookup_var p sf = SOME w /\
      mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) gf tf sf
Proof
  strip_tac >> drule_all ghost_inv_after_separated_write >> strip_tac >>
  drule_all ghost_inv_push_top_ext >> strip_tac >>
  drule ghost_inv_set_top_entry >>
  disch_then (qspecl_then [`FEMPTY`, `es.scopes`, `id`, `entry`] mp_tac) >>
  simp[]
QED

(* A common consumer for the word, bulk and bytestring endpoints. The
   exterior taint premise comes from their same-endpoint companions; the
   shared opcode interface supplies every storage/immutable frame here. *)
Theorem ghost_inv_install_after_finite_copy:
  ghost_inv d cenv cx es G tn s /\
  EVERY (\i. MEM i.inst_opcode [MLOAD; ADD; AND; MSTORE; MCOPY]) code /\
  run_inst_seq code s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn code s gf tf /\
  mem_agree_outside writes sf.vs_memory s.vs_memory /\
  (!i. i NOTIN writes ==> (i IN tf.t_mem <=> i IN tn.t_mem)) /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name old p sz.
    lookup_scopes name es.scopes = SOME old /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf old.type old.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint old.type old.value ==>
      i NOTIN writes) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  (!p sz. FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers gf tf p sf sz /\
    !w mem. lookup_var p sf = SOME w /\
      mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) gf tf sf
Proof
  strip_tac >> drule_all finite_copy_endpoint_frames >> strip_tac >>
  drule_all ghost_inv_install_after_separated_write >> simp[]
QED

(* Bulk consumer: all copy postconditions refer to the given endpoint,
   including the zero-sized, empty-code endpoint. *)
Theorem ghost_inv_install_bulk_copy:
  ghost_inv d cenv cx es G tn s /\
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  n < dimword (:256) /\ lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  run_inst_seq (emitted_insts sa sb) s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s gf tf /\
  mem_agree_outside {i | w2n b <= i /\ i < w2n b+n} sf.vs_memory s.vs_memory /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name old p sz.
    lookup_scopes name es.scopes = SOME old /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf old.type old.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint old.type old.value ==>
      i < w2n b \/ w2n b+n <= i) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  (!p sz. FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers gf tf p sf sz /\
    !w mem. lookup_var p sf = SOME w /\
      mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) gf tf sf
Proof
  strip_tac >> drule_all compile_bulk_copy_endpoint_frames >> strip_tac >>
  irule ghost_inv_install_after_separated_write >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`kept`, `{i | w2n b <= i /\ i < w2n b+n}`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac std_ss [arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.NOT_LESS,
    arithmeticTheory.ADD_COMM] >> fs[arithmeticTheory.ADD_COMM] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ghost_inv_install_bytes_copy:
  ghost_inv d cenv cx es G tn s /\
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  w2n (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) <= capacity /\
  run_inst_seq (emitted_insts sa sb) s = OK sf /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s gf tf /\
  mem_agree_outside {i | w2n b <= i /\ i < w2n b+capacity} sf.vs_memory s.vs_memory /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name old p sz.
    lookup_scopes name es.scopes = SOME old /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf old.type old.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint old.type old.value ==>
      i < w2n b \/ w2n b+capacity <= i) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  (!p sz. FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers gf tf p sf sz /\
    !w mem. lookup_var p sf = SOME w /\
      mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) gf tf sf
Proof
  strip_tac >> drule_all compile_bytes_copy_endpoint_frames >> strip_tac >>
  irule ghost_inv_install_after_separated_write >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`kept`, `{i | w2n b <= i /\ i < w2n b+capacity}`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac std_ss [arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.NOT_LESS,
    arithmeticTheory.ADD_COMM] >> fs[arithmeticTheory.ADD_COMM] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem ghost_inv_install_word_copy:
  ghost_inv d cenv cx es G tn s /\
  run_inst_seq [mk_inst iid MLOAD [Var src] [tmp];
    mk_inst (iid+1) MSTORE [Var dst; Var tmp] []] s = OK sf /\
  inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst iid MLOAD [Var src] [tmp];
     mk_inst (iid+1) MSTORE [Var dst; Var tmp] []] s gf tf /\
  tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
  mem_agree_outside {i | w2n b <= i /\ i < w2n b+32} sf.vs_memory s.vs_memory /\
  (!p. p IN kept ==>
    lookup_var p sf = lookup_var p s /\ FLOOKUP gf p = FLOOKUP G p /\
    op_taint tf (Var p) = op_taint tn (Var p)) /\
  (!name old p sz.
    lookup_scopes name es.scopes = SOME old /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    p IN kept /\ val_wf old.type old.value /\
    !w i. lookup_var p s = SOME w /\
      w2n w <= i /\ i < w2n w + val_footprint old.type old.value ==>
      i < w2n b \/ w2n b+32 <= i) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
    cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p IN kept) /\
  cenv_top_ext cenv bc (FEMPTY :: es.scopes) /\
  (!p sz. FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) ==>
    ptr_covers gf tf p sf sz /\
    !w mem. lookup_var p sf = SOME w /\
      mem_agree_outside tf.t_mem sf.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem) ==>
  ghost_inv d bc cx
    (es with scopes := (FEMPTY |+ (id,entry)) :: es.scopes) gf tf sf
Proof
  strip_tac >> drule_all word_copy_endpoint_frames >> strip_tac >>
  irule ghost_inv_install_after_separated_write >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`kept`, `{i | w2n b <= i /\ i < w2n b+32}`] >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac std_ss [arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.NOT_LESS] >>
  first_assum ACCEPT_TAC
QED
