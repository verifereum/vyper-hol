(* The full dynarray-free tuple window survives destination evaluation. *)
Theory assignBorrowedTupleWindowPtr
Ancestors
  exprSimSubscriptArrayFrame exprSimAttributeFields bodyPtrDefs
  loweringPosts valueEncoding valueEncodingDefs exprSimHypsDefs
  ptrDiscipline venomState arithmetic

Theorem borrowed_tuple_target_window_ptr:
  expr_sim_inv cenv cx env es /\
  target_post ctx func cenv cx es sa sb s ee pv vt r t /\
  ghost_kept cenv es sa G tn s H tt /\
  local_region cenv es.scopes s name b sz /\
  local_val_at cenv cx name k (TupleTV tvs) (ArrayV (TupleV vs)) /\
  val_wf (TupleTV tvs) (ArrayV (TupleV vs)) /\
  dynarray_free (TupleTV tvs) /\
  k+type_memory_size (TupleTV tvs) <= sz ==>
  mem_bytes_at (b+k) (type_memory_size (TupleTV tvs)) t.vs_memory =
    mem_bytes_at (b+k) (type_memory_size (TupleTV tvs)) s.vs_memory /\
  (!i. b+k <= i /\ i < b+k+type_memory_size (TupleTV tvs) /\
    i IN tt.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV vs)) =
    type_memory_size (TupleTV tvs)` by simp[val_footprint_def] >>
  `locals_kept cenv es ee s t` by fs[target_post_def] >>
  conj_tac
  >- (mp_tac (Q.INST [`off` |-> `b+k`, `n` |-> `name`,
       `tv` |-> `TupleTV tvs`, `v` |-> `ArrayV (TupleV vs)`, `s'` |-> `t`]
       (SPEC_ALL locals_kept_dynarray_free_value)) >>
      simp[]) >>
  rpt strip_tac >>
  `!k'. dynarray_len_at cenv name k' ==> i < b+k' \/ b+k'+32 <= i` by
    (rpt strip_tac >> drule_all local_val_at_dynarray_apart >> decide_tac) >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_def]) >>
  qpat_x_assum `!n b sz i. local_region _ _ _ _ _ _ /\ _ ==> _`
    (qspecl_then [`name`,`b`,`sz`,`i`] mp_tac) >> simp[] >> decide_tac
QED
