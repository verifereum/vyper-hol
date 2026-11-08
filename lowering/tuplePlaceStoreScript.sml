(* Common-witness probes: state relation and outstanding RHS snapshots. *)
Theory tuplePlaceStore
Ancestors
  tuplePlaceSnapshot assignRelayoutFrame placeStore placeStoreStorage
  exprLoweringProps compileEnv loweringPosts venomState venomExecSemantics
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
