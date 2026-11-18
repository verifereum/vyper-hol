(* Robust enclosing-value transport for a clean scalar path write. *)
Theory augAssignFullPathWriteRobust
Ancestors
  memoryPlaceStorePost assignBasePtrLocalStore vyperState valueEncodingProps pred_set

Theorem augassign_path_word_store_robust:
  mem_path_offset tv path = SOME (k,ltv) /\
  value_has_type tv oldroot /\ value_has_type ltv v /\
  evaluate_subscripts tv oldroot path = INL old /\
  assign_subscripts tv oldroot path (Replace v) = INL newroot /\
  type_memory_size ltv = 32 /\ val_wf ltv v /\
  val_footprint ltv v <= 32 /\
  val_in_memory ltv v (b+k) (mstore (b+k) w s).vs_memory /\
  (!m. mem_agree_outside tm s.vs_memory m ==>
    val_in_memory tv oldroot b m) ==>
  !m. mem_agree_outside (tm DIFF {q | b+k <= q /\ q < b+k+32})
    (mstore (b+k) w s).vs_memory m ==>
    val_in_memory tv newroot b m
Proof
  rpt strip_tac >>
  mp_tac (Q.INST
    [`entry` |-> `<|assignable := T; type := tv; value := oldroot; popped := []|>`,
     `entry'` |-> `<|assignable := T; type := tv; value := newroot; popped := []|>`,
     `path` |-> `path`, `k` |-> `k`, `ptv` |-> `ltv`,
     `off` |-> `b`, `v` |-> `v`, `mem` |-> `s.vs_memory`,
     `mem'` |-> `(mstore (b+k) w s).vs_memory`,
     `tm` |-> `tm`, `tm'` |-> `tm DIFF {q | b+k <= q /\ q < b+k+32}`]
    memory_place_replace_robust) >>
  simp[replace_memory_entry_def] >>
  impl_tac >-
    (rpt conj_tac
     >- (rpt strip_tac >> irule assign_base_ptr_clean_window_robust_value >>
         simp[] >> qexistsl_tac [`(mstore (b+k) w s).vs_memory`, `32`, `tm`] >>
         simp[arithmeticTheory.ADD_ASSOC])
     >- (rpt strip_tac >> sym_tac >>
         irule mstore_mem_bytes_at_disjoint >> decide_tac)
     >> simp[]) >>
  disch_then irule >>
  pure_rewrite_tac[Q.SPECL [`b`, `k`, `32`] arithmeticTheory.ADD_ASSOC] >>
  first_assum ACCEPT_TAC
QED
