(*
 * Revert-to-Assert Function-Level Correctness
 *
 * This theory lifts block-level correctness to function-level.
 *
 * ============================================================================
 * PROOF STATUS
 * ============================================================================
 *
 * FULLY PROVEN (no cheats):
 *   - transform_blocks_length       : Transformation preserves block count
 *   - transform_blocks_labels       : Transformation preserves block labels
 *   - lookup_block_transform_blocks : Block lookup NONE/SOME is preserved
 *   - lookup_block_transform_some   : SOME lookup in original implies SOME in transformed
 *   - transform_context_functions   : Context transformation structure
 *   - transform_context_entry       : Context entry point preserved
 *
 * STRUCTURED WITH CHEATS (depends on rtaBlockTheory cheats):
 *   - transform_block_run_ok        : Block-level OK result equivalence
 *   - transform_block_run_halt      : Block-level Halt preservation
 *   - transform_block_run_revert    : Block-level Revert preservation
 *   - transform_block_run_error     : Block-level Error preservation
 *   - transform_function_correct    : Function-level correctness
 *   - transform_preserves_halts     : Derived from transform_function_correct
 *   - transform_preserves_reverts   : Derived from transform_function_correct
 *
 * DEPENDENCY CHAIN:
 *   rtaBlockTheory.rta_then_block_equiv_general (cheated)
 *   rtaBlockTheory.rta_else_block_equiv_general (cheated)
 *       |
 *       v
 *   transform_block_run_ok/halt/revert/error (structured, inner cheats)
 *       |
 *       v
 *   transform_function_correct (cheated, needs block-level helpers)
 *       |
 *       v
 *   transform_preserves_halts/reverts (derived)
 *
 * REMAINING WORK:
 *   1. Complete rta_*_block_equiv_general in rtaBlockTheory (prefix case)
 *   2. Connect block-level theorems to transform_block_run_* proofs
 *   3. Complete transform_function_correct using the block helpers
 *
 * ============================================================================
 *)

Theory rtaFunction
Ancestors
  rtaBlock rtaTransform venomInst venomSem

(* ==========================================================================
   Helper Lemmas
   ========================================================================== *)

(* Transform preserves block count *)
Theorem transform_blocks_length:
  !blocks next_id bbs bbs' next_id'.
    transform_blocks blocks next_id bbs = (bbs', next_id') ==>
    LENGTH bbs' = LENGTH bbs
Proof
  Induct_on `bbs` >> rw[transform_blocks_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`blocks`, `next_id''`, `next_id'`] >> simp[]
QED

(* Transform preserves block labels *)
Theorem transform_blocks_labels:
  !blocks next_id bbs bbs' next_id'.
    transform_blocks blocks next_id bbs = (bbs', next_id') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct_on `bbs` >> rw[transform_blocks_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac transform_block_label >> simp[] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`blocks`, `next_id''`, `next_id'`] >> simp[]
QED

(* Lookup in transformed blocks *)
Theorem lookup_block_transform_blocks:
  !blocks next_id bbs bbs' next_id' lbl.
    transform_blocks blocks next_id bbs = (bbs', next_id') ==>
    (lookup_block lbl bbs' = NONE <=> lookup_block lbl bbs = NONE)
Proof
  Induct_on `bbs` >> rw[transform_blocks_def, lookup_block_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  simp[lookup_block_def] >>
  imp_res_tac transform_block_label >> gvs[] >>
  first_x_assum (qspecl_then [`blocks`, `next_id''`, `bbs''`, `next_id'`, `lbl`] mp_tac) >>
  simp[]
QED

(* If original lookup succeeds, transformed lookup also succeeds *)
Theorem lookup_block_transform_some:
  !fn lbl bb.
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    ?bb'. lookup_block lbl (transform_function fn).fn_blocks = SOME bb'
Proof
  rw[transform_function_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule lookup_block_transform_blocks >> strip_tac >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  Cases_on `lookup_block lbl blocks'` >> simp[]
QED

(* ==========================================================================
   Block-Level Run Equivalence
   ========================================================================== *)

(* Helper: When transform_block produces bb', run_block on bb and bb' are related.
   Uses the generalized block equivalence theorems from rtaBlockTheory.

   PRECONDITIONS:
     - s.vs_inst_idx = 0 : Required by block-level theorems (start at beginning of block)
     - ~s.vs_halted      : Required for execution

   PROOF STRUCTURE:
     Case analysis on transform_block:
     - No transformation (bb' = bb): trivial, result is identical
     - Then-rewrite: By rta_then_block_equiv_general
       - If original jumped to else_lbl (cond=0), transformed also jumps to else_lbl
       - If original jumped to then_lbl (cond!=0), transformed Reverts
     - Else-rewrite: By rta_else_block_equiv_general
       - If original jumped to then_lbl (cond!=0), transformed also jumps to then_lbl
       - If original jumped to else_lbl (cond=0), transformed Reverts

   DEPENDENCIES: Requires rta_then_block_equiv_general and rta_else_block_equiv_general
   from rtaBlockTheory (both currently cheated for the prefix instruction case). *)
Theorem transform_block_run_ok:
  !blocks next_id bb bb' next_id' fn s s'.
    transform_block blocks next_id bb = (bb', next_id') /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
    run_block fn bb s = OK s' ==>
    (?s''. run_block fn bb' s = OK s'' /\ s''.vs_current_bb = s'.vs_current_bb) \/
    (?s''. run_block fn bb' s = Revert s'')
Proof
  rpt strip_tac >>
  fs[transform_block_def] >>
  gvs[AllCaseEqs()] >| [
    (* Then-rewrite case: use rta_then_block_equiv_general *)
    cheat,
    (* Else-rewrite case: use rta_else_block_equiv_general *)
    cheat
  ]
QED

(* Helper: run_block on transformed block for Halt case
   PROOF: The transformation only changes the terminator. If original Halts,
   it must be from a STOP instruction in the prefix, which is preserved.
   Since we don't transform STOP instructions, Halt is preserved. *)
Theorem transform_block_run_halt:
  !blocks next_id bb bb' next_id' fn s s'.
    transform_block blocks next_id bb = (bb', next_id') /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
    run_block fn bb s = Halt s' ==>
    ?s''. run_block fn bb' s = Halt s''
Proof
  rpt strip_tac >>
  fs[transform_block_def] >>
  gvs[AllCaseEqs()] >| [
    (* Then-rewrite case *)
    cheat,
    (* Else-rewrite case *)
    cheat
  ]
QED

(* Helper: run_block on transformed block for Revert case
   PROOF: If original Reverts, it either came from:
   1. A REVERT instruction in the prefix - preserved identically
   2. A failed ASSERT in the prefix - preserved identically
   The transformation doesn't change prefix instructions, so Revert is preserved. *)
Theorem transform_block_run_revert:
  !blocks next_id bb bb' next_id' fn s s'.
    transform_block blocks next_id bb = (bb', next_id') /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
    run_block fn bb s = Revert s' ==>
    ?s''. run_block fn bb' s = Revert s''
Proof
  rpt strip_tac >>
  fs[transform_block_def] >>
  gvs[AllCaseEqs()] >| [
    (* Then-rewrite case *)
    cheat,
    (* Else-rewrite case *)
    cheat
  ]
QED

(* Helper: run_block on transformed block for Error case
   PROOF: Errors come from invalid operations in prefix instructions.
   Since prefix is preserved, errors are preserved. *)
Theorem transform_block_run_error:
  !blocks next_id bb bb' next_id' fn s e.
    transform_block blocks next_id bb = (bb', next_id') /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
    run_block fn bb s = Error e ==>
    ?e'. run_block fn bb' s = Error e'
Proof
  rpt strip_tac >>
  fs[transform_block_def] >>
  gvs[AllCaseEqs()] >| [
    (* Then-rewrite case *)
    cheat,
    (* Else-rewrite case *)
    cheat
  ]
QED

(* ==========================================================================
   Function Execution Equivalence
   ========================================================================== *)

(* The key correctness theorem: running a transformed function
   produces equivalent terminal results to the original.

   Key insight: The transformation may "short-circuit" reverts, meaning:
   - Original: JNZ jumps to revert block, then revert block produces Revert
   - Transformed: ASSERT directly produces Revert

   So transformed may use less fuel but produce the same terminal result.

   The theorem says:
   - Halt → Halt (both terminate normally)
   - Revert → Revert (both revert, transformed may do so earlier)
   - Error → Error (structural errors preserved)
   - OK → either OK with same current_bb, or Revert (short-circuit case)

   For the OK case, when original continues to a revert block, transformed
   may Revert directly. This is still correct semantics since the original
   would Revert on the next iteration anyway. *)
Theorem transform_function_correct:
  !fn fuel s result.
    run_function fuel fn s = result ==>
    ?result'.
      run_function fuel (transform_function fn) s = result' /\
      (* Terminal results are preserved *)
      ((?s'. result = Halt s') ==> ?s''. result' = Halt s'') /\
      ((?s'. result = Revert s') ==> ?s''. result' = Revert s'') /\
      ((?e. result = Error e) ==> ?e'. result' = Error e') /\
      (* For OK, either same continuation or short-circuit to Revert *)
      ((?s'. result = OK s') ==>
         (?s''. result' = OK s'' /\ s''.vs_current_bb = s'.vs_current_bb) \/
         (?s''. result' = Revert s''))
Proof
  cheat
QED

(* Specialization: halts are preserved *)
Theorem transform_preserves_halts:
  !fn fuel s s'.
    run_function fuel fn s = Halt s' ==>
    ?s''. run_function fuel (transform_function fn) s = Halt s''
Proof
  rpt strip_tac >>
  drule transform_function_correct >>
  rw[] >> fs[]
QED

(* Specialization: reverts are preserved *)
Theorem transform_preserves_reverts:
  !fn fuel s s'.
    run_function fuel fn s = Revert s' ==>
    ?s''. run_function fuel (transform_function fn) s = Revert s''
Proof
  rpt strip_tac >>
  drule transform_function_correct >>
  rw[] >> fs[]
QED

(* ==========================================================================
   Context-Level Correctness
   ========================================================================== *)

(* Transform context applies transform_function to each function *)
Theorem transform_context_functions:
  !ctx.
    (transform_context ctx).ctx_functions =
    MAP transform_function ctx.ctx_functions
Proof
  rw[transform_context_def]
QED

(* Transform context preserves entry point *)
Theorem transform_context_entry:
  !ctx. (transform_context ctx).ctx_entry = ctx.ctx_entry
Proof
  rw[transform_context_def]
QED
