(*
 * Widened compound internal return at the store endpoint, with the ghost:
 * the pointer twin of stmtSimReturnWiden's
 * compile_internal_return_memory_widen_frag (compound branch).  The source
 * value, robust under tainted memory, is copied by
 * compile_store_memory_typed into the caller's return buffer, which must
 * not overlap the source; then RET.
 *
 * TOP-LEVEL:
 *   compile_internal_return_memory_widen_ptr
 *)
Theory internalReturnWidenPtr
Ancestors internalReturnStorePtr internalReturnCountedPtr
  internalReturnMemorySuffixPtr stmtLowering typedMemoryCopy compileEnv
  fragGasPathPtr

Theorem compile_internal_return_memory_widen_ptr:
  compile_internal_return_from_env ce ty sty (Var src) (Var rpc) sa = ((),sb) /\
  ce.ce_return_buf = SOME (PtrVar (Var dst) cap) /\ ce.ce_returns_count = 0 /\
  sty <> ty /\ ~is_word_type ty /\ ~is_bytestring_type ty /\
  type_widens_to tenv sty ty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv ty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\
  val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields.
     FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname, fty, sz). !tv.
       evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_memory_bytes ce ty = type_memory_size dtv /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME d /\
  w2n a + type_memory_size stv < dimword (:256) /\
  w2n d + type_memory_size dtv < dimword (:256) /\
  regions_disjoint (w2n a) (type_memory_size stv) (w2n d)
    (type_memory_size dtv) /\
  ptr_covers G tn src s (type_memory_size stv) /\
  ptr_covers G tn dst s (type_memory_size dtv) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (w2n a) m) /\
  stor_taint_ok cx tn s /\ not_fresh_at sa rpc /\
  lookup_var rpc s = SOME pc /\ op_taint tn (Var rpc) = {} ==>
  ?H tm t.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm
      (IntRet <| iret_values := []; iret_adopt_fmp := NONE |> t) /\
    typed_copy_state_frame sa (w2n d) (type_memory_size dtv) s t /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
         val_in_memory dtv v (w2n d) m) /\
    stor_taint_ok cx tm t /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))
Proof
  cheat
QED
