(* Bytes copy writes n runtime bytes but reserves the full k-byte slot. *)
Theory bodyPtrMakeArrayPositiveBytes
Ancestors
  bodyPtrMakeArrayPositiveFrame bodyPtrMakeArrayBytesStore
  bodyPtrMakeArrayConsInvariant bodyPtrDefs list pair

Theorem literal_bytes_loop_store:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sa G tn s cells off /\
  literal_prefix_ok cells tn s /\
  compile_store_memory ce (Var src) (Var dst) ty sty sa = ((),sb) /\
  ~is_word_type ty /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  val_wf tv v /\ val_footprint tv v <= n /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32+32*((len+31) DIV 32) /\ n <= k /\ n < dimword(:256) /\
  ptr_mem_ok cx ty v (Var src) G tn s /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s n /\
  lookup_var dst s = SOME b /\ w2n b = addr+off /\ ptr_covers G tn dst s n /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ off+k <= capacity /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce fr /\
  (!p. not_fresh_at fr p ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `off+n <= capacity` by decide_tac >>
  drule_all literal_loop_store_ghost >> strip_tac >>
  drule_all literal_loop_store_exterior >> strip_tac >>
  drule literal_loop_frame_runtime >> strip_tac >>
  drule_all literal_bytes_store_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z)` >>
  `FLOOKUP H root = SOME (addr,capacity) /\ ptr_covers H tm root z capacity` by
    metis_tac[literal_loop_frame_allocation] >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb H tm z cells off` by
    (irule literal_loop_store_endpoint >> simp[] >>
     qexistsl [`G`, `n`, `s`, `sa`, `tn`] >> simp[] >> metis_tac[]) >>
  `EVERY (\(tv,v,p,k). p+k <= addr+off) cells` by
    (gvs[literal_loop_frame_def, EVERY_MEM, FORALL_PROD] >> metis_tac[]) >>
  `literal_prefix_ok cells tm z` by
    (irule literal_prefix_store_frame >> qexistsl [`addr+off`, `n`, `s`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf es sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k)` by
    (irule literal_loop_frame_advance >> simp[]) >>
  qexistsl [`z`, `H`, `tm`] >> simp[] >>
  `val_footprint tv v <= k` by decide_tac >>
  simp[literal_prefix_cell] >> metis_tac[]
QED
