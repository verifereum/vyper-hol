(*
 * Expression simulation: compile_subscript_array_case, a case of exprSimPlaces on its
 * own so it can be proved apart.
 *
 * TOP-LEVEL:
 *   compile_subscript_array_case — an element of a static or dynamic array,
 *     with the bounds-check abort, by four subcases:
 *     compile_subscript_array_storage_call_case for a storage or transient
 *     base with an effect in the index, compile_subscript_array_ancestor_pop_case
 *     for a local base the index leaves reading a popped snapshot,
 *     compile_subscript_array_ctor_pop_case for a constructor immutable
 *     base the index leaves past its array's length or popped, and
 *     compile_subscript_array_live_case for the rest.
 *)

Theory exprSimSubscriptArray
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex supportedExprTraverse
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* The base's place still reads its current value in es: a local's path
   reaches it in the local's current value, not only in a snapshot its
   popped history keeps (read_memory_path); an immutable's path reaches it
   in the immutable's value; a storage place's slots are live
   (storage_read_live), not those of an element a pop left past its
   array's length.  Values always do. *)
Definition subscript_base_live_def:
  (subscript_base_live cx (PlaceR (MemoryPlace id path)) es <=>
     ?entry v. lookup_scopes id es.scopes = SOME entry /\
               evaluate_subscripts entry.type entry.value path = INL v) /\
  (subscript_base_live cx (PlaceR (ImmutablePlace src id path)) es <=>
     ?v es'. read_place cx (ImmutablePlace src id path) es = (INL v, es')) /\
  (subscript_base_live cx (PlaceR (StoragePlace tr slot tv)) es <=>
     storage_read_live cx tr (get_storage cx es tr) slot tv) /\
  (subscript_base_live cx _ es <=> T)
End

(* An element of an array whose index leaves the locals and the immutables
   as they were, whose base's place still reads its current value once the
   index is evaluated, with no effect in the index of a storage or
   transient base.  Cheated, for the alan run.  compile_subscript lowers
   the index after the base, and the base's value_vv must still hold its
   value when the index's fragment ends.  vv_post says only that the
   base's pointer is somewhere in a live local's region at a path of the
   base's type holding the base's value (vv_at, local_val_at), not that it
   is the base's place; but the index leaves the source locals as they
   were, so stmt_state_rel at the index's end state puts the same bytes
   there, the length words locals_kept exempts included, and the bounds
   check loads the base's length.  A storage base with no effect in the
   index sees its storage unchanged, and its live slots agree by
   storage_rel at the end state.  An immutable (LocCode) reads its length
   with compile_ptr_load's compile_imm_load_word (ILOAD in the
   constructor, where immutable_holds and immutables_rel keep the whole
   value in the staged buffer; DLOAD at runtime).  The bounds check
   itself, a source RuntimeError for an index out of range against
   compile_array_subscript's ASSERT, which aborts, is in expr_exit's
   allowance (exprSimArrayIndex). *)
Theorem compile_subscript_array_live_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (!t r t'. eval_expr cx idx t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tv t r t'. eval_expr cx obj s = (INL tv, t) /\
                   eval_expr cx idx t = (INL r, t') ==>
                   subscript_base_live cx tv t') /\
    (!ty st l. vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
               is_slot_addressed l ==> ~expr_has_effect idx) /\
    (!ty st s v t. cenv.ce_is_ctor /\
                   vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode ==>
                   eval_expr cx obj s <> (INL (Value v), t)) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of a storage or transient array whose index has an effect.
   ADMITTED (cheat).  The index can call a function that shrinks the
   array: self.a[0][self.f()], with self.a : DynArray[DynArray[uint256, 2],
   2] of length 1 and f popping it to empty.  The source reads a[0]'s
   length from its slot, which the pop leaves stale, and the lowering
   SLOADs the same slot after the call; but a[0]'s slots are then dead
   (storage_dead), and storage_rel after the call (storage_agree off the
   dead slots) relates nothing there, so the two reads, and the bounds
   checks on them, are not related.  A call frame that keeps the target
   slots the source does not write replaces this lemma. *)
Theorem compile_subscript_array_storage_call_case:
  !nocalls ctx func cenv cx ann obj idx et bd ty st l.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
    is_slot_addressed l /\ expr_has_effect idx ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of an array whose index changes the locals or the
   immutables (a pop in the index, or in the constructor a call that
   writes an immutable).  ADMITTED (cheat), for three reasons.
   - vv_post does not tie the base's pointer to its place: with
     x : DynArray[DynArray[uint256, 2], 2] holding [[5, 1], [5, 1]],
     x[1][x[0].pop()], a pointer at x[0]'s offset satisfies every
     hypothesis on the base as well as x[1]'s; the index shortens x[0],
     so a lowering reading the length there aborts where the source, with
     1 < 2 for x[1], goes on.  Likewise for an immutable, whose offset
     immutable_holds pins only through sub_layout.
   - The index can leave a local's base reading a popped snapshot:
     x[1][x.pop()[0]] with x of length 2 pops x[1], the base's place reads
     the snapshot (read_memory_path), and the index's expr_post keeps the
     local's bytes but its dynamic arrays' length words (locals_kept), so
     nothing says the bounds check's word still holds the snapshot's
     length.
   - False for an immutable in the constructor: with a :
     DynArray[DynArray[DynArray[uint256, 2], 2], 2] holding
     [[[1, 2], [0, 5]]], a[0][1][a[0].pop()[0]] (the pinned Python compiler
     accepts a pop of an immutable's member in __init__) pops a[0][1], and
     the source's read of the base's place raises a RuntimeError, since an
     immutable keeps no popped history (read_place's ImmutablePlace case is
     evaluate_subscripts alone), while the lowering ILOADs the stale length
     2 from the staged buffer, passes the bounds check for the index 0 and
     goes on, where expr_exit asks for an abort.
   A place-pointer clause in vv_post (a local place's pointer is the
   local's plus its path's offset, as place_ptr_rel says for targets), a
   locals_kept that keeps a length word unless memory holds the length
   read_memory_path reads there, and an immutable popped history replace
   this lemma. *)
Theorem compile_subscript_array_index_writes_case:
  !nocalls ctx func cenv cx ann obj idx et bd t r t'.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    eval_expr cx idx t = (INL r, t') /\
    (t'.scopes <> t.scopes \/ t'.immutables <> t.immutables) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of an array whose base's place, once the index is
   evaluated, no longer reads a current value, or, in the constructor,
   whose base is a value popped from an immutable: a popped element.
   ADMITTED (cheat).  x.pop()[i], for a local x : DynArray[DynArray[
   uint256, 2], 2], reads the popped element from x's popped history and
   the lowering from the bytes past x's new length; self.a.pop()[i], for
   storage, reads slots past a's new length, which are dead; a[0].pop()[i]
   in the constructor gives the element as a value and the lowering a
   pointer into the staged buffer past a[0]'s new length (immutable_holds'
   constructor form).  The index's expr_post keeps neither those bytes
   (locals_kept exempts the length words, the staged buffer is no
   allocation) nor the dead slots (storage_rel relates only live ones, and
   expr_post has no Venom storage frame), so the length word the bounds
   check loads is not related to the value's.  Posts that keep those bytes
   and slots replace this lemma. *)
Theorem compile_subscript_array_dead_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd s tv t r t'.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    eval_expr cx obj s = (INL tv, t) /\
    ((eval_expr cx idx t = (INL r, t') /\ ~subscript_base_live cx tv t') \/
     (?ty st v. cenv.ce_is_ctor /\
                vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode /\
                tv = Value v)) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

Theorem compile_subscript_array_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  rpt strip_tac >>
  Cases_on `?ty st l. vv_location (FST (compile_expr cenv ty obj st)) = SOME l /\
                      is_slot_addressed l /\ expr_has_effect idx`
  >- (gvs[] >> metis_tac[compile_subscript_array_storage_call_case]) >>
  Cases_on `?t r t'. eval_expr cx idx t = (INL r, t') /\
                     (t'.scopes <> t.scopes \/ t'.immutables <> t.immutables)`
  >- (gvs[] >> metis_tac[compile_subscript_array_index_writes_case]) >>
  Cases_on `?ty st s v t. cenv.ce_is_ctor /\
              vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode /\
              eval_expr cx obj s = (INL (Value v), t)`
  >- (gvs[] >>
      qspecl_then [`nocalls`,`ctx`,`func`,`cenv`,`cx`,`ann`,`obj`,`idx`,`et`,`bd`,
                   `s`,`Value v`,`t`,`r`,`t'`] mp_tac
        compile_subscript_array_dead_base_case >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      simp[]) >>
  Cases_on `!s tv t r t'. eval_expr cx obj s = (INL tv, t) /\
                          eval_expr cx idx t = (INL r, t') ==>
                          subscript_base_live cx tv t'`
  >- (irule compile_subscript_array_live_case >> metis_tac[]) >>
  gvs[] >>
  qspecl_then [`nocalls`,`ctx`,`func`,`cenv`,`cx`,`ann`,`obj`,`idx`,`et`,`bd`,
               `s`,`tv`,`t`,`r`,`t'`] mp_tac
    compile_subscript_array_dead_base_case >>
  simp[] >> metis_tac[]
QED
