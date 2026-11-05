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
   popped history keeps (read_memory_path), and an immutable's path reaches
   it in the immutable's value.  Storage places and values always do. *)
Definition subscript_base_live_def:
  (subscript_base_live cx (PlaceR (MemoryPlace id path)) es <=>
     ?entry v. lookup_scopes id es.scopes = SOME entry /\
               evaluate_subscripts entry.type entry.value path = INL v) /\
  (subscript_base_live cx (PlaceR (ImmutablePlace src id path)) es <=>
     ?v es'. read_place cx (ImmutablePlace src id path) es = (INL v, es')) /\
  (subscript_base_live cx _ es <=> T)
End

(* An element of an array whose base's place still reads its current value
   once the index is evaluated, with no effect in the index of a storage or
   transient base.  Cheated, for the alan run.  compile_subscript lowers
   the index after the base, and the base's value_vv must still hold its
   value when the index's fragment ends.  Where the base points into a live
   local's region, the index's expr_post keeps the local's bytes but its
   dynamic arrays' length words (locals_kept); the base's place reads the
   local's current value, so stmt_state_rel at the index's end state says
   what memory holds there, the length word the bounds check loads
   included.  In the constructor, a code base is an immutable's place
   (a value popped from an immutable is the ctor leaf's).  A storage base with no effect in the index sees its storage
   unchanged.  An immutable (LocCode) reads its length with
   compile_ptr_load's compile_imm_load_word (ILOAD in the constructor,
   where immutable_holds and immutables_rel keep the whole value in the
   staged buffer, DLOAD at runtime, where no call writes an immutable:
   bare_global_assignable is empty outside the constructor).  The bounds
   check itself, a source RuntimeError for an index out of range against
   compile_array_subscript's ASSERT, which aborts, is in expr_exit's
   allowance (exprSimArrayIndex). *)
Theorem compile_subscript_array_live_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
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

(* An element of an array in a local whose base's place, once the index is
   evaluated, reads only a snapshot of the local's popped history.
   ADMITTED (cheat).  x[1][x.pop()[0]], with x : DynArray[DynArray[uint256,
   2], 2] of length 2: the index pops x[1], the base's place (x, [1]) then
   reads the snapshot the pop recorded (read_memory_path), and the bounds
   check MLOADs x[1]'s length word at the base's pointer.  The index's
   expr_post keeps the local's bytes but its dynamic arrays' length words
   (locals_kept), and no invariant relates a snapshot to memory, so nothing
   says the word still holds the snapshot's length.  A locals_kept that
   keeps a length word unless memory holds the length read_memory_path
   reads there at the end state replaces this lemma. *)
Theorem compile_subscript_array_ancestor_pop_case:
  !nocalls ctx func cenv cx ann obj idx et bd s tv t r t' id path.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    eval_expr cx obj s = (INL tv, t) /\ eval_expr cx idx t = (INL r, t') /\
    tv = PlaceR (MemoryPlace id path) /\ ~subscript_base_live cx tv t' ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* An element of an array in an immutable, in the constructor, whose
   base's path, once the index is evaluated, is past its array's length, or
   whose base is a value popped from an immutable.  ADMITTED (cheat).
   The first is false: with a : DynArray[DynArray[DynArray[uint256, 2], 2],
   2] holding [[[1, 2], [0, 5]]], a[0][1][a[0].pop()[0]] (the pinned Python
   compiler accepts a pop of an immutable's member in __init__): the index
   pops a[0][1], and the source's read of the base's place (a, [0; 1])
   raises a RuntimeError, since an immutable keeps no popped history
   (read_place's ImmutablePlace case is evaluate_subscripts alone), while
   the lowering ILOADs the stale length 2 from the staged buffer, passes
   the bounds check for the index 0 and goes on, where expr_exit asks for
   an abort.  In the second (a[0].pop()[i]), pop_place gives the popped
   element as a value and the lowering a pointer to its bytes in the
   staged buffer, past the array's new length (immutable_holds' constructor
   form); the index's expr_post keeps the bytes of the allocations and
   the live locals, not those, so the length word the bounds check loads
   is not related to the value's.  A source semantics that reads a popped
   immutable member as a local's popped history does, with a post that
   keeps the staged buffer's bytes, replaces this lemma. *)
Theorem compile_subscript_array_ctor_pop_case:
  !nocalls ctx func cenv cx ann obj idx et bd s tv t r t'.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    eval_expr cx obj s = (INL tv, t) /\
    ((?src id path. tv = PlaceR (ImmutablePlace src id path) /\
                    eval_expr cx idx t = (INL r, t') /\
                    ~subscript_base_live cx tv t') \/
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
  Cases_on `?ty st s v t. cenv.ce_is_ctor /\
              vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode /\
              eval_expr cx obj s = (INL (Value v), t)`
  >- (gvs[] >>
      qspecl_then [`nocalls`,`ctx`,`func`,`cenv`,`cx`,`ann`,`obj`,`idx`,`et`,`bd`,
                   `s`,`Value v`,`t`,`r`,`t'`] mp_tac
        compile_subscript_array_ctor_pop_case >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      simp[]) >>
  Cases_on `!s tv t r t'. eval_expr cx obj s = (INL tv, t) /\
                          eval_expr cx idx t = (INL r, t') ==>
                          subscript_base_live cx tv t'`
  >- (irule compile_subscript_array_live_case >> metis_tac[]) >>
  gvs[] >>
  Cases_on `tv` >> gvs[subscript_base_live_def] >>
  rename1 `PlaceR pl` >> Cases_on `pl` >> gvs[subscript_base_live_def]
  >- (rename1 `MemoryPlace id path` >>
      qspecl_then [`nocalls`,`ctx`,`func`,`cenv`,`cx`,`ann`,`obj`,`idx`,`et`,`bd`,
                   `s`,`PlaceR (MemoryPlace id path)`,`t`,`r`,`t'`,`id`,`path`] mp_tac
        compile_subscript_array_ancestor_pop_case >>
      simp[subscript_base_live_def] >> metis_tac[])
  >- (rename1 `ImmutablePlace src id path` >>
      qspecl_then [`nocalls`,`ctx`,`func`,`cenv`,`cx`,`ann`,`obj`,`idx`,`et`,`bd`,
                   `s`,`PlaceR (ImmutablePlace src id path)`,`t`,`r`,`t'`] mp_tac
        compile_subscript_array_ctor_pop_case >>
      simp[subscript_base_live_def] >> metis_tac[])
QED
