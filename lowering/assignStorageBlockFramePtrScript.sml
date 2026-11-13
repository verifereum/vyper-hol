(* Compose a counted element copy with the already copied array prefix. *)
Theory assignStorageBlockFramePtr
Ancestors
  assignBasePtrStorageLoop placeDynStorageEffect placeStoreCopyPath
  stmtSimStoreCopy venomState venomExecSemantics ptrDiscipline
  words arithmetic list

Theorem assign_base_store_taint_prefix_append:
  !j i loc b k tn.
    assign_base_store_taint_prefix loc b k tn (i+j) =
    assign_base_store_taint_prefix loc (b+n2w i*32w) (k+n2w i)
      (assign_base_store_taint_prefix loc b k tn i) j
Proof
  Induct_on `j` >- simp[assign_base_store_taint_prefix_def] >>
  rpt gen_tac >>
  simp[ADD_CLAUSES, assign_base_store_taint_prefix_def,
       assign_base_store_taint_frame, GSYM word_add_n2w,
       WORD_LEFT_ADD_DISTRIB, WORD_RIGHT_ADD_DISTRIB, WORD_ADD_ASSOC]
QED

Theorem store_copy_prefix_backend_frame:
  !n loc b k s t.
    s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient /\
    s.vs_memory = t.vs_memory /\ s.vs_call_ctx = t.vs_call_ctx ==>
    (store_copy_prefix loc b k s n).vs_accounts =
      (store_copy_prefix loc b k t n).vs_accounts /\
    (store_copy_prefix loc b k s n).vs_transient =
      (store_copy_prefix loc b k t n).vs_transient
Proof
  Induct >> simp[assign_base_store_prefix_zero] >>
  rpt gen_tac >> strip_tac >> first_x_assum drule_all >> strip_tac >>
  Cases_on `loc = LocStorage` >>
  simp[assign_base_store_prefix_suc, assign_base_store_prefix_frame,
       sstore_def, tstore_def, mload_def]
QED

Theorem assign_base_store_frame_block:
  assign_base_store_frame loc b k s0 tn0 i s tn /\
  assign_base_store_frame loc (b+n2w i*32w) (k+n2w i) s tn j u tf ==>
  assign_base_store_frame loc b k s0 tn0 (i+j) u tf
Proof
  strip_tac >>
  qabbrev_tac `q = store_copy_prefix loc b k s0 i` >>
  qabbrev_tac `tt = assign_base_store_taint_prefix loc b k tn0 i` >>
  `s.vs_accounts = q.vs_accounts /\ s.vs_transient = q.vs_transient /\
   s.vs_memory = q.vs_memory /\ s.vs_call_ctx = q.vs_call_ctx /\
   tn.t_stor = tt.t_stor /\ tn.t_trans = tt.t_trans /\
   tn.t_mem = tt.t_mem /\ tn.t_imm = tt.t_imm` by
    gvs[assign_base_store_frame_def, Abbr `q`, Abbr `tt`,
        assign_base_store_prefix_frame, assign_base_store_taint_frame] >>
  `!n a z. (store_copy_prefix loc a z s n).vs_accounts =
      (store_copy_prefix loc a z q n).vs_accounts /\
    (store_copy_prefix loc a z s n).vs_transient =
      (store_copy_prefix loc a z q n).vs_transient` by
    metis_tac[store_copy_prefix_backend_frame] >>
  `!n a z. (assign_base_store_taint_prefix loc a z tn n).t_stor =
      (assign_base_store_taint_prefix loc a z tt n).t_stor /\
    (assign_base_store_taint_prefix loc a z tn n).t_trans =
      (assign_base_store_taint_prefix loc a z tt n).t_trans` by
    (Induct >> simp[assign_base_store_taint_prefix_def] >>
     rpt gen_tac >> Cases_on `loc = LocStorage` >>
     gvs[assign_base_store_taint_prefix_def, assign_base_store_taint_frame]) >>
  simp[assign_base_store_frame_def, place_store_prefix_append,
       assign_base_store_taint_prefix_append, Abbr `q`, Abbr `tt`] >>
  fs[assign_base_store_frame_def]
QED
