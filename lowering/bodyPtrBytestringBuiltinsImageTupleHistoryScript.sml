(* Proof-only finite suffix history: Entry alone loses the identity of a
   terminal allocation.  Offset literals are words, so test word equality. *)
Theory bodyPtrBytestringBuiltinsImageTupleHistory
Ancestors bodyPtrBytestringBuiltinsImageIfExp
          bodyPtrBytestringBuiltinsImageFrontier bodyPtrBytestringBuiltinsWindows
          words venomInst emitHelper emitHelperProps compileEnv list
          exprLowering context vyperAST

Definition tail_alloc_def:
  tail_alloc b xs <=>
    ?i w v p. b = Var v /\ xs = p ++ [mk_inst i ALLOCA [Lit w] [v]]
End

Definition tuple_history_def:
  tuple_history b k st <=> image_entry st /\
    (n2w k = (32w:256 word) ==> ~tail_alloc b st.cs_current_insts)
End

Theorem tuple_history_initial:
  image_entry st ==> tuple_history b 0 st
Proof
  simp[tuple_history_def, wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem tuple_history_callback:
  tuple_history b k st /\ image_entry u /\
  (tail_alloc b u.cs_current_insts ==> tail_alloc b st.cs_current_insts) ==>
  tuple_history b k u
Proof
  simp[tuple_history_def] >> metis_tac[]
QED

Theorem tail_alloc_append[simp]:
  tail_alloc b (xs ++ [inst]) <=>
  ?i w v. b = Var v /\ inst = mk_inst i ALLOCA [Lit w] [v]
Proof
  simp[tail_alloc_def] >> metis_tac[]
QED

Theorem image_pending2_add:
  image_pending2 (xs ++ [mk_inst i ADD [b; Lit w] [d]]) <=>
  w = 32w /\ tail_alloc b xs
Proof
  simp[image_pending2_def, tail_alloc_def, mk_inst_def] >> metis_tac[]
QED

Theorem image_add_not_pending3:
  ~image_pending3 (xs ++ [mk_inst i ADD ops outs])
Proof
  simp[image_pending3_def, mk_inst_def]
QED

Theorem image_bad_add[simp]:
  image_bad (xs ++ [mk_inst i ADD ops outs]) <=> image_bad xs
Proof
  `!a b c d p q. [mk_inst i ADD ops outs] <> p ++ [a;b;c;d] ++ q` by
    (rpt strip_tac >>
     qpat_x_assum `[_] = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp[image_bad_def, four_window_append, mk_inst_def]
QED

Theorem tuple_history_destination:
  tuple_history b k st /\ emit_op ADD [b; Lit (n2w k)] st = (dst,t) ==>
  image_entry t /\ ~tail_alloc b t.cs_current_insts
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[tuple_history_def, image_entry_def, image_pending2_add,
      image_add_not_pending3, tail_alloc_append] >>
  gvs[mk_inst_def]
QED

Theorem tuple_history_no_emission:
  tail_alloc b (SND (comp_return vv st)).cs_current_insts ==>
  tail_alloc b st.cs_current_insts
Proof
  simp[comp_return_def]
QED

Theorem tail_alloc_other:
  v <> saved ==>
  ~tail_alloc (Var saved) (xs ++ [mk_inst i ALLOCA [Lit w] [v]])
Proof
  simp[tail_alloc_append, mk_inst_def]
QED

Theorem tuple_history_after_destination:
  tuple_history b k st /\ emit_op ADD [b; Lit (n2w k)] st = (dst,t) ==>
  !k'. tuple_history b k' t
Proof
  rpt strip_tac >> drule_all tuple_history_destination >>
  simp[tuple_history_def]
QED

Theorem tuple_history_zero_iteration:
  !cfn cenv e b k st op u out t.
  expr_type e = TupleT [] /\ lowered_value_type cenv e = TupleT [] /\
  tuple_history b k st /\ cfn cenv (TupleT []) e st = (StackValue (TupleT []) op,u) /\
  image_entry u /\
  (tail_alloc b u.cs_current_insts ==> tail_alloc b st.cs_current_insts) /\
  compile_make_tuple cfn cenv [e] b k st = (out,t) ==>
  !k'. tuple_history b k' t
Proof
  rpt gen_tac >> strip_tac >>
  `tuple_history b k u` by metis_tac[tuple_history_callback] >>
  gvs[compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def,
      unwrap_value_def, compile_store_memory_def, compile_copy_memory_def,
      is_word_type_def, is_bytestring_type_def, type_memory_bytes_def,
      comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[tuple_history_after_destination]
QED

Theorem image_bad_mstore:
  image_bad (xs ++ [mk_inst i MSTORE ops outs]) ==>
  image_bad xs \/ image_pending3 xs
Proof
  `!a b c d p q. [mk_inst i MSTORE ops outs] <> p ++ [a;b;c;d] ++ q` by
    (rpt strip_tac >>
     qpat_x_assum `[_] = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  simp[image_bad_def, four_window_append, image_pending3_def] >>
  metis_tac[]
QED

Theorem tuple_history_mstore:
  image_entry st /\ emit_void MSTORE ops st = ((),t) ==>
  !b k. tuple_history b k t
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  gvs[tuple_history_def, image_entry_def, image_pending_barrier,
      tail_alloc_append] >>
  conj_tac >- metis_tac[image_bad_mstore] >> simp[mk_inst_def]
QED

Theorem tuple_history_word_iteration:
  !cfn cenv e ty b k st op u out t.
  expr_type e = ty /\ is_word_type ty /\
  tuple_history b k st /\ cfn cenv ty e st = (StackValue ty op,u) /\
  image_entry u /\
  (tail_alloc b u.cs_current_insts ==> tail_alloc b st.cs_current_insts) /\
  compile_make_tuple cfn cenv [e] b k st = (out,t) ==>
  !k'. tuple_history b k' t
Proof
  rpt gen_tac >> strip_tac >>
  `tuple_history b k u` by metis_tac[tuple_history_callback] >>
  gvs[compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def,
      unwrap_value_def, compile_store_memory_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all tuple_history_destination >> strip_tac >>
  metis_tac[tuple_history_mstore]
QED
