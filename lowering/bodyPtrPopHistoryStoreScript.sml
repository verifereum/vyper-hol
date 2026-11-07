Theory bodyPtrPopHistoryStore
Ancestors bodyPtrPopMemoryStore bodyPtrPopMemoryHeader robustCopyTransportPtr
  exprSimPop exprSimAggregateEncoding vyperPlaceResultTyping vyperState
  valueEncoding bodyPtrDefs pred_set vyperValueOperation

(* A removed element still occupies its original payload window. This spatial
   fact is independent of whether the selected owner is live or historical. *)
Theorem pop_removed_child_robust_header_store:
  vs <> [] /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) a mem) /\
  mem_agree_outside {i | a <= i /\ i < a + 32} t.vs_memory s.vs_memory ==>
  !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory tv (LAST vs)
      (a + 32 + (LENGTH vs - 1) * type_memory_size tv) mem
Proof
  strip_tac >>
  `0 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
  `val_wf tv (LAST vs)` by
    (simp[listTheory.LAST_EL] >> irule elems_val_wf_EL >> simp[] >>
     goal_assum (drule_at Any)) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory tv (LAST vs)
       (a + 32 + (LENGTH vs - 1) * type_memory_size tv) mem` by
    (rpt strip_tac >>
     qpat_x_assum `!mem. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
     simp[val_in_memory_def] >> strip_tac >>
     drule elems_in_memory_EL >>
     disch_then (qspec_then `LENGTH vs - 1` mp_tac) >> simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn.t_mem`,
    `{i | a <= i /\ i < a + 32}`] >>
  simp[] >> fs[mem_agree_outside_def]
QED

(* The newest record wins precisely where its typed suffix read succeeds;
   no claim is made about every older record at the same physical address. *)
Theorem pop_record_removed_child_read:
  subscripts_type root_type
    (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) = SOME tv /\
  evaluate_subscripts tv (LAST vs) suffix = INL v ==>
  read_popped root_type
    ((path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]) ++ suffix)
    (record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history) = SOME v
Proof
  strip_tac >> simp[record_pop_def] >>
  irule read_popped_new_snapshot >>
  simp[listTheory.DROP_APPEND, listTheory.DROP_def]
QED

Theorem pop_historical_owner_source_step:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  evaluate_subscripts entry.type entry.value path = INR err /\
  replace_popped entry.type path (ArrayV (DynArrayV (FRONT vs))) entry.popped =
    SOME history ==>
  pop_place cx (MemoryPlace id path) es =
    (INL (PlaceR (MemoryPlace id
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),
     es with scopes := pre ++
       (sc |+ (id,entry with <| value := entry.value; popped :=
         record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history |>))::rest)
Proof
  strip_tac >>
  simp[pop_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, ignore_bind_def, return_def, lift_sum_def,
       check_def, set_scopes_def, popped_value_def, pop_element_def]
QED

Theorem pop_live_owner_source_step:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated ==>
  pop_place cx (MemoryPlace id path) es =
    (INL (PlaceR (MemoryPlace id
      (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))),
     es with scopes := pre ++
       (sc |+ (id,entry with <| value := updated; popped :=
         record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped |>))::rest)
Proof
  strip_tac >>
  simp[pop_place_def, read_memory_path_def, get_scopes_def, bind_def,
       lift_option_type_def, type_check_def, assert_def, ignore_bind_def,
       return_def, lift_sum_def, check_def, set_scopes_def,
       popped_value_def, pop_element_def]
QED

Theorem pop_removed_child_counted_store:
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME (n2w (LENGTH vs - 1)) /\
  op_taint tn value = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  vs <> [] /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) ==>
  !D PG. ?t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK t) /\
    t = ((mstore (w2n a) (n2w (LENGTH vs - 1)) s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv (LAST vs)
        (w2n a + 32 + (LENGTH vs - 1) * type_memory_size tv) mem)
Proof
  strip_tac >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    (drule pop_robust_dynarray_header_clean >> simp[]) >>
  rpt gen_tac >> drule_all pop_clean_header_store_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexists_tac `t` >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> irule pop_removed_child_robust_header_store >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cap`, `s`, `t`, `tn`] >> simp[]
QED

(* Validation scope and first remaining condition:

   pop_live_owner_source_step and pop_historical_owner_source_step expose the
   actual branches of pop_place, not a fabricated history transformer. In
   either branch the newest record is the removed child. Where a suffix read
   of that child succeeds and its declared path type is available,
   pop_record_removed_child_read identifies the winning source snapshot.
   pop_removed_child_counted_store proves robustness of that child at its
   original payload address on the actual clean decrement edge. The owner
   may itself be historical: the spatial proof uses its supplied robust
   representation, not live-root ghost_inv.

   These facts DO NOT validate the proposed invariant for every retained
   read. In particular, a query that fails within the newest child record
   continues into older deeper history; replace_popped similarly updates the
   first owner with a successful query, retaining older suffixes. Deriving
   compatible original-layout addresses and simultaneous representation for
   those fallback reads from an INITIAL LIVE CAPTURE plus prior mutations is
   still missing. It is not implied by merely having a typed history list.
   No freshness/disjointness premise is smuggled into the boundaries above.

   The exact remaining source/spatial interface is: for retained q with
   mem_path_offset root_tv q = SOME (k,qtv), read_memory_path updated_entry q =
   INL v must select either a still-live owner, the newest removed child, or
   an older successful owner whose representation at root_address+k has been
   retained. The first two require shortened-owner/path spatial lemmas;
   the third additionally requires an inductively established compatibility
   condition linking historical owners to the fixed root allocation. The
   checked boundaries establish only the removed-child case, NOT that
   compatibility condition, and NOT arbitrary captured-place preservation.
   Stop here for review rather than assume a global historical invariant.
*)
