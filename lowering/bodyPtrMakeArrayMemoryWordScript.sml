(* Word materialization from a robust memory source.  The loaded scalar is
   clean but need not be a pointer; only old destinations retain coverage. *)
Theory bodyPtrMakeArrayMemoryWord
Ancestors
  wordLoadStorePtr bodyPtrMakeArrayLoad bodyPtrMakeArrayWordClean bodyPtrMakeArrayMloadFrame typedCopyPtr
  exprSimProps bodyPtrDefs valueEncodingProps venomState venomInst finite_map

Theorem memory_word_materialize_endpoint:
  ptr_covers G tn src s 32 /\
  ptr_mem_ok cx t v (Var src) G tn s /\ is_word_type t /\
  evaluate_type (get_tenv cx) t = SOME ty /\ value_has_type ty v /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var src] [tmp]) /\
  eval_operand (Var src) s = SOME a ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = ((update_var tmp (typed_val_to_w256 ty v) s) with
      vs_inst_idx := SUC s.vs_inst_idx) /\
    eval_operand (Var tmp) sf = SOME (typed_val_to_w256 ty v) /\
    op_taint tnf (Var tmp) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    sf.vs_memory = s.vs_memory /\
    (!x. x <> tmp ==>
      lookup_var x sf = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    (!dst n. tmp <> dst /\ ptr_covers G tn dst s n ==>
       ptr_covers Gf tnf dst sf n)
Proof
  strip_tac >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem`
    by (drule ptr_mem_word_clean >> simp[]) >>
  `val_in_memory ty v (w2n a) s.vs_memory` by
    (gvs[ptr_mem_ok_def] >>
     first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `mload (w2n a) s = typed_val_to_w256 ty v` by
    metis_tac[val_in_memory_word_type, mem_word_at_eq_mload] >>
  qexistsl_tac [
    `step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn`,
    `(update_var tmp (mload (w2n a) s) s) with
      vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >- (irule mload_ptr_path >> simp[]) >>
  drule_all mload_ghost_clean >> strip_tac >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       mload_ghost_frame] >>
  rpt strip_tac >>
  qpat_x_assum `mload _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  irule (SRULE [update_var_def] mload_ptr_old_coverage) >> simp[]
QED
