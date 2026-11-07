Theory bodyPtrPopAlignedMutation
Ancestors bodyPtrPopHistoryStore gasSummaryComposePtr vyperState

(* Concrete paired mutation cuts, not whole-index retained-read preservation. *)
Theorem pop_live_owner_marked_store:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV (DynArrayV vs)) /\
  vs <> [] /\
  assign_subscripts entry.type entry.value path
    (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME (n2w (LENGTH vs - 1)) /\
  op_taint tn value = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) ==>
  !D PG. ?t.
    gas_marked_exec_ptr D (ctx,fn) PG (pop_place cx (MemoryPlace id path))
      (es,s,G,tn) []
      (INL (PlaceR (MemoryPlace id
        (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))))
      (es with scopes := pre ++
        (sc |+ (id,entry with <| value := updated; popped :=
          record_pop path (ArrayV (DynArrayV vs)) (LAST vs) entry.popped |>))::rest)
      G tn (OK t) /\
    t = ((mstore (w2n a) (n2w (LENGTH vs - 1)) s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv (LAST vs)
        (w2n a + 32 + (LENGTH vs - 1) * type_memory_size tv) mem)
Proof
  strip_tac >> rpt gen_tac >>
  drule_all pop_removed_child_counted_store >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexists_tac `t` >> reverse conj_tac >- simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`]
    gas_marked_exec_ptr_no_source_read)) >> simp[] >>
  gen_tac >> simp[pop_live_owner_source_step]
QED

Theorem pop_historical_owner_marked_store:
  find_containing_scope id es.scopes = SOME (pre,sc,entry,rest) /\
  entry.assignable /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\ vs <> [] /\
  evaluate_subscripts entry.type entry.value path = INR err /\
  replace_popped entry.type path (ArrayV (DynArrayV (FRONT vs))) entry.popped =
    SOME history /\
  emit_void MSTORE [Var dst; value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME (n2w (LENGTH vs - 1)) /\
  op_taint tn value = {} /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ elems_val_wf vs tv /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) (w2n a) mem) ==>
  !D PG. ?t.
    gas_marked_exec_ptr D (ctx,fn) PG (pop_place cx (MemoryPlace id path))
      (es,s,G,tn) []
      (INL (PlaceR (MemoryPlace id
        (path ++ [ValueSubscript (IntV &(LENGTH vs - 1))]))))
      (es with scopes := pre ++
        (sc |+ (id,entry with <| value := entry.value; popped :=
          record_pop path (ArrayV (DynArrayV vs)) (LAST vs) history |>))::rest)
      G tn (OK t) /\
    t = ((mstore (w2n a) (n2w (LENGTH vs - 1)) s)
      with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory tv (LAST vs)
        (w2n a + 32 + (LENGTH vs - 1) * type_memory_size tv) mem)
Proof
  strip_tac >> rpt gen_tac >>
  drule_all pop_removed_child_counted_store >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexists_tac `t` >> reverse conj_tac >- simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`]
    gas_marked_exec_ptr_no_source_read)) >> simp[] >>
  gen_tac >> simp[pop_historical_owner_source_step]
QED
