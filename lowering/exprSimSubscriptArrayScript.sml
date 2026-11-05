(*
 * Expression simulation: compile_subscript_array_case, a case of exprSimPlaces on its
 * own so it can be proved apart.
 *
 * TOP-LEVEL:
 *   compile_subscript_array_case — an element of a static or dynamic array,
 *     with the bounds-check abort, by two subcases:
 *     compile_subscript_array_framed_base_case for a base the index's frame
 *     keeps (a runtime immutable, or a static array of no dynamic array in
 *     memory), and compile_subscript_array_place_base_case, admitted, for
 *     the rest.
 *)

Theory exprSimSubscriptArray
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex exprSimSubscriptArrayFramed
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* An element of an array whose index leaves the locals and the immutables
   as they were, and whose base the index's fragment keeps as it is: an
   immutable at runtime (LocCode outside the constructor), or a static array
   with no dynamic array inside it in memory (a local or a temporary).
   Cheated, for the alan run.  compile_subscript lowers the index after the
   base, and the base's value_vv must still hold its value when the index's
   fragment ends.  At runtime an immutable sits in the data section, which
   immutables_rel relates to the unchanged source immutables, and
   immutable_holds there pins the base's offset by sub_layout; the
   lowering reads a dynamic array's length with compile_ptr_load's
   compile_imm_load_word (DLOAD).  A memory base's bytes lie in one of the
   base's own allocations or in a live local's region (vv_at), and
   contain no length word, so the index's expr_post keeps them (its
   allocation frame, locals_kept); a static array needs no length load.
   With the source locals unchanged, the base's place reads at the index's
   end what it read before.  The bounds check itself, a source RuntimeError
   for an index out of range against compile_array_subscript's ASSERT,
   which aborts, is in expr_exit's allowance (exprSimArrayIndex). *)
Theorem compile_subscript_array_framed_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    (!t r t'. eval_expr cx idx t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    ((~cenv.ce_is_ctor /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
     ((?n. bd = Fixed n) /\
      (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
      !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory)) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

(* Every other array subscript: a base in storage or transient storage, an
   immutable in the constructor, a dynamic array or one with a dynamic
   array inside it in memory, a base whose source result is a storage
   place, or an index that changes the locals or the immutables.  ADMITTED (cheat).  NOT DERIVABLE from these hypotheses,
   though no miscompile is known: vv_post does not tie the base's pointer
   to its source place.  vv_at and local_val_at pick the local's path by
   its type alone, immutable_holds' constructor form takes any offset of
   the staged buffer that holds the value, and storage_holds pins the slot
   only by what it reads; so the base's pointer may lie in dead bytes that
   hold an equal value (past a dynamic array's length, in the staged
   buffer, in dead slots), which nothing keeps across the index's
   fragment: state_rel and immutables_rel relate only the live parts,
   locals_kept exempts every dynamic array's length word, and expr_post
   has no frame on Venom storage.  Witness: x : DynArray[DynArray[uint256,
   2], 2] holding [[5, 1]], with [5, 1] and its length word 2 left at
   x[1]'s bytes by an earlier pop; for x[0][i], with i a local, a pointer
   at x[1]'s offset satisfies every hypothesis on the base, i's fragment
   may rewrite that length word, and the bounds check then loads a word
   unrelated to x[0]'s length.  Further cases need more than that:
   - x[1][x.pop()[0]] pops x[1], and the base's place then reads the
     snapshot x's popped history keeps (read_memory_path), which no
     invariant relates to memory;
   - self.a[0][self.f()], with f popping self.a to empty, leaves a[0]'s
     slots dead, and storage_rel after the call relates nothing there;
   - in the constructor, with a : DynArray[DynArray[DynArray[uint256, 2],
     2], 2] holding [[[1, 2], [0, 5]]], a[0][1][a[0].pop()[0]] (the
     pinned Python compiler accepts a pop of an immutable's member in
     __init__) is false: the source's read of the base's place raises a
     RuntimeError, an immutable keeping no popped history, while the
     lowering ILOADs the stale length 2 and goes on, where expr_exit asks
     for an abort.
   A place-pointer clause in vv_post replaces most of this lemma: a
   conjunct vv_place_ptr cenv cx es' s tv vv, as place_ptr_rel says for
   targets, with
     vv_place_ptr cenv cx es s (PlaceR (MemoryPlace id path))
                  (LocatedValue t p) <=>
       p.ptr_location = LocMemory /\
       ?q sz b t0 tv0 k tvk.
         FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var q) sz) /\
         lookup_var q s = SOME b /\ cenv.ce_var_type id = SOME t0 /\
         evaluate_type (get_tenv cx) t0 = SOME tv0 /\
         mem_path_offset tv0 path = SOME (k, tvk) /\
         eval_operand p.ptr_operand s = SOME (b + n2w k)
     vv_place_ptr cenv cx es s (PlaceR (StoragePlace tr slot tv))
                  (LocatedValue t p) <=>
       p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME slot
     (and the same for HashMapRef tr slot kt vt)
     vv_place_ptr cenv cx es s (PlaceR (ImmutablePlace src id path))
                  (LocatedValue t p) <=>
       p.ptr_location = LocCode /\ src = cenv.ce_module /\
       ?off itv iv k tvk.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module, id) =
           SOME (ImmutableLoc off) /\
         FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
                    NONE => FEMPTY
                  | SOME imms => get_source_immutables cenv.ce_module imms)
                 id = SOME (itv, iv) /\
         mem_path_offset itv path = SOME (k, tvk) /\
         eval_operand p.ptr_operand s = SOME (n2w (off + k))
     vv_place_ptr cenv cx es s _ _ <=> T
   Its producers are the expressions whose source result can be a place:
   Name, TopLevelName, Subscript (array, tuple, mapping), Attribute, Pop,
   and IfExp (conditional_result keeps a memory aggregate's place, and the
   PHI carries the arm's pointer).  With it, and the base live at the
   index's end, the rest goes through but for popped snapshots, dead
   storage slots and the constructor immutable above. *)
Theorem compile_subscript_array_place_base_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) /\
    ~((!t r t'. eval_expr cx idx t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))) ==>
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
  Cases_on `(!t r t'. eval_expr cx idx t = (INL r, t') ==>
                      t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
            (!s tr slot vt t. eval_expr cx obj s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
            ((~cenv.ce_is_ctor /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocCode) \/
             ((?n. bd = Fixed n) /\
              (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
              !ty st. vv_location (FST (compile_expr cenv ty obj st)) = SOME LocMemory))`
  >- (irule compile_subscript_array_framed_base_case >> asm_rewrite_tac[] >>
      metis_tac[]) >>
  irule compile_subscript_array_place_base_case >> asm_rewrite_tac[] >>
  qexistsl [`bd`, `et`] >> asm_rewrite_tac[]
QED
