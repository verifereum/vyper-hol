(* Common-witness probes: state relation and outstanding RHS snapshots. *)
Theory tuplePlaceStore
Ancestors
  tuplePlaceSnapshot assignRelayoutFrame placeStore placeStoreStorage
  exprLoweringProps compileEnv loweringStateRelDefs loweringPosts venomState venomExecSemantics
  valueEncoding valueEncodingProofs

Theorem tuple_place_local_relayout_snapshot:
  compile_store_memory cenv src (Var p) dty sty sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) sty dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ entry.type = dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ lookup_var p s = SOME dw /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  stmt_state_rel ctx func cenv cx es s /\
  find_containing_scope id es.scopes = SOME (pre,scope,entry,rest) /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. stmt_state_rel ctx func cenv cx
      (es with scopes := pre ++
        (scope |+ (id, entry with <|value := v; popped := []|>)) :: rest) t /\
    typed_copy_effect ctx func sa sb s t (w2n dw) (type_memory_size dtv) /\
    (!tv' v' b. val_in_memory tv' v' b s.vs_memory /\ val_wf tv' v' /\
      (b + type_memory_size tv' <= w2n dw \/
       w2n dw + type_memory_size dtv <= b) ==>
      val_in_memory tv' v' b t.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all local_memory_relayout_store_path >> strip_tac >>
  qexists `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `typed_copy_effect _ _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[tuple_place_copy_snapshot]
QED

(* A concrete storage/transient execution witness, not a second existential
   run glued to a frame theorem. Word slot writes do not allocate scratch. *)
Theorem tuple_place_word_slot_snapshot:
  emit_void (if tr then TSTORE else SSTORE) [dst;src] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME k /\
  eval_operand src s = SOME (typed_val_to_w256 tv v) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx (StoragePlace tr k tv) v ee = (INL (),ff) /\
  storage_place_region cx (StoragePlace tr k tv) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all place_store_word_backend_state >> strip_tac >>
  drule_all place_store_emit_slot_path >> strip_tac >>
  qexists `((if tr then tstore else sstore) k (typed_val_to_w256 tv v) s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `tr` >> gvs[stmt_state_rel_inst_idx, tstore_def, sstore_def,
                         lookup_var_def]
QED

(* Allocation and typed normalization retain bytes of every old allocation.
   Both frames refer to the endpoint used for the source-state relation. *)
Theorem tuple_place_normalize_frame:
  !cenv cx ctx func es sa sm sc buf dty sty dtv stv v src sw s.
    compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
    compile_store_memory_typed cenv buf.buf_operand dty src sty sm = ((),sc) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
      w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t dw. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME dw /\
      val_in_memory dtv v (w2n dw) t.vs_memory /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      t.vs_labels = s.vs_labels /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (!aid b len a n. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
        aid < sa.cs_next_id /\ b <= a /\ a + n <= b + len ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sm` by
    (qspec_then `type_memory_size dtv` (qspec_then `sa` mp_tac)
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by gvs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all place_store_alloc_buffer_path >>
  disch_then (qx_choose_then `u` (qx_choose_then `w`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qpat_x_assum `?p. buf.buf_operand = Var p /\ not_fresh_at sm p`
    strip_assume_tac >>
  `eval_operand src u = SOME sw` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `regions_disjoint (w2n sw) (type_memory_size stv)
     (w2n w) (type_memory_size dtv)` by
    (irule place_store_alloc_source_disjoint >>
     qexistsl_tac [`s`, `sa`] >> simp[Once arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >> qpat_x_assum `!aid b sz. _` drule_all >> simp[arithmeticTheory.ADD_COMM]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    gvs[regions_disjoint_def] >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
    place_store_memory_typed_path >>
  disch_then (qspecl_then [`get_tenv cx`, `dtv`, `stv`, `v`] mp_tac) >>
  disch_then (qspecl_then [`ctx`, `func`, `u`, `w`, `sw`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `exprSimStorageCopy$copy_static t = exprSimStorageCopy$copy_static u` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[exprSimStorageCopyTheory.copy_static_def, venom_state_component_equality]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _;
       vs_prev_bb := _; vs_current_bb := _; vs_inst_idx := _|> = u` mp_tac >>
     simp[venom_state_component_equality]) >>
  `stmt_state_rel ctx func cenv cx es t` by suspend "state" >>
  `!aid b len a n. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
     aid < sa.cs_next_id /\ b <= a /\ a + n <= b + len ==>
     mem_bytes_at a n t.vs_memory = mem_bytes_at a n s.vs_memory` by
    suspend "bytes" >>
  qexistsl_tac [`t`, `w`] >> suspend "post"
QED

Resume tuple_place_normalize_frame[state]:
  markerLib.RESUME_TAC >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `!name lb len. local_region cenv es.scopes u name lb len ==>
     w2n w + type_memory_size dtv <= lb \/ lb + len <= w2n w` by
    metis_tac[regions_disjoint_def] >>
  irule exprSimCopyTheory.copy_buffer_state_rel_frame >>
  qexistsl_tac [`w2n w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
       [STRING #"%" (toString sa.cs_next_var)]`, `u`, `sm`, `type_memory_size dtv`] >>
  asm_rewrite_tac[venomInstTheory.mk_inst_def] >> simp[]
QED

Resume tuple_place_normalize_frame[bytes]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `regions_disjoint (w2n w) (type_memory_size dtv) b len` by
    (qpat_x_assum `!aid b len. _` drule_all >> simp[]) >>
  `a + n <= w2n w \/ w2n w + type_memory_size dtv <= a` by
    (gvs[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!a len. _` drule >> simp[]
QED

Resume tuple_place_normalize_frame[post]:
  markerLib.RESUME_TAC >>
  drule_all exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  asm_rewrite_tac[] >> simp[eval_operand_def] >> metis_tac[eval_operand_def]
QED
Finalise tuple_place_normalize_frame
