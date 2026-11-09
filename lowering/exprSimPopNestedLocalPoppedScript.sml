(*
 * Pop on a nested memory local whose target reads a popped snapshot: the
 * residual case of pop_nested_local_sim, admitted on its own (see the
 * comment on it).
 *)

Theory exprSimPopNestedLocalPopped
Ancestors
  exprSimPopNestedBase
  exprSimPopNestedLocalPost exprSimPopNestedLocalRun exprSimCalldataSlice
  exprSimPopNestedLocalSuffix vyperEvalExprPreservesScopesDom
  exprSimPopNestedLocalSource exprSimPopNestedLocalHandoff gasOutcome gasSummary gasSummaryCompose gasExemptCert
  loweringPosts bodySim exprSimHypsDefs stmtSimProps
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation vyperLookup

(* RESIDUAL (popped history): a target whose place, after its evaluation,
   is dead in the local's value and read from the local's popped history.

   The target's own index pops an ancestor of the popped array: in
   x[0][x.pop()[0][0]].pop(), with x : DynArray[DynArray[DynArray[uint256,
   2],2],2] of length 1, extend_place checks x[0] against x's live value,
   the index then pops x, and the last step reads x[0] from the history
   (read_memory_path), so the place x[0][i] is dead in x's value.  The
   lowering computed x[0]'s pointer before the index popped x and pops the
   array it finds there: the stale bytes of the popped element, which are
   the history's snapshot.

   Stated for one run of the target, at the state tend it ends in: the
   place is dead in the local's value there and read from the history.
   Every such run pops an ancestor of the target's own base from inside
   its index, a self-overlapping assignment target that upstream rejects
   ("risky overlap"), so this stays admitted for the target read/write
   overlap exclusion.

   The invariants lack this fact: stmt_state_rel's local_ptrs_rel relates
   only entry.value to memory, and popped_keys_indexed only types the
   history.  So nothing relates the snapshot the source pops to the bytes
   the lowering pops.  E.g. x : DynArray[DynArray[uint256,2],2] with value
   ArrayV (DynArrayV []) and history
   [([ValueSubscript (IntV 0)], ArrayV (DynArrayV [IntV 5]))], memory all
   zero at x's region: local_ptrs_rel holds (x's length word is 0), the
   source pops x[0] from the snapshot, and the lowering loads length 0 at
   x[0]'s pointer and aborts.  The fix is for local_ptrs_rel to also
   relate a local's popped history to memory. *)
Theorem pop_nested_local_popped_case:
  !ctx func cenv cx env ann bt es id n sa sm r s0 hdr loc pt lc ws esz q
   marks tend t path entry err v.
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = NameTarget id /\
    type_place_target env bt = SOME (Type (ArrayT ann (Dynamic n))) /\
    fn_has_code sa r func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_expr cx (Pop ann bt)) expr_vv_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    compile_get_target_ptr compile_expr cenv bt sa = ((hdr,loc,pt),sm) /\
    Abbrev (lc = case loc of NONE => LocMemory | SOME l => l) /\
    Abbrev (ws = word_scale lc) /\
    Abbrev (esz = elem_size_in_location cenv lc
                    (case pt of SOME (ValPT (ArrayT et _)) => et
                              | _ => BaseT (IntT 256))) /\
    compile_dynarray_pop hdr ws esz cenv.ce_is_ctor cenv.ce_imm_alloca lc sm =
      (q,r) /\
    ci_mono sa sm /\ ci_mono sm r /\
    fn_has_code sa sm func /\ fn_has_code sm r func /\
    gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
    gas_marked_exec F (ctx,func) (eval_target_place cx bt) (es,s0) marks
      (INL (MemoryPlace id path)) tend (OK t) /\
    target_post ctx func cenv cx es sa sm s0 (tend with gas_obs := [])
      (PlaceR (MemoryPlace id path)) (Type (ArrayT ann (Dynamic n)))
      (hdr,loc,pt) t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    lookup_scopes id tend.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err /\
    read_popped entry.type path entry.popped = SOME v ==>
    ?res es_end r'.
      gas_marked_exec F (ctx,func)
        (vyperState$bind (eval_target_place cx bt) (pop_place cx)) (es,s0)
        marks res es_end r' /\
      ((?u. r' = OK u /\
            ?tv. res = INL tv /\
                 vv_post ctx func cenv cx (Pop ann bt) es sa r s0
                   (es_end with gas_obs := []) tv
                   (LocatedValue ann (mk_ptr q lc)) u /\
                 u.vs_current_bb = r.cs_current_bb /\
                 u.vs_inst_idx = LENGTH r.cs_current_insts) \/
       exit_result r' /\ expr_exit res r')
Proof
  cheat
QED
