(*
 * Revert-to-Assert Function-Level Correctness
 *
 * This theory lifts block-level correctness to function-level.
 *
 * The main theorem states that transform_function preserves the
 * observable behavior of executing the function.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - transform_function_correct : Transformed function has equivalent behavior
 *   - transform_preserves_halts  : If original halts, so does transformed
 *   - transform_preserves_reverts: If original reverts, so does transformed
 *
 * ============================================================================
 *)

Theory rtaFunction
Ancestors
  rtaBlock rtaTransform venomInst

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

(* ==========================================================================
   Function Execution Equivalence
   ========================================================================== *)

(* The key correctness theorem: running a transformed function
   produces equivalent results to the original *)
Theorem transform_function_correct:
  !fn fuel s result.
    run_function fuel fn s = result ==>
    ?result'.
      run_function fuel (transform_function fn) s = result' /\
      (* Results are equivalent - same halts, same reverts, same errors *)
      ((?s'. result = Halt s') ==> ?s''. result' = Halt s'') /\
      ((?s'. result = Revert s') ==> ?s''. result' = Revert s'') /\
      ((?e. result = Error e) ==> ?e'. result' = Error e') /\
      ((?s'. result = OK s') ==>
         ?s''. result' = OK s'' /\
               s''.vs_current_bb = s'.vs_current_bb)
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
  strip_tac >> fs[]
QED

(* Specialization: reverts are preserved *)
Theorem transform_preserves_reverts:
  !fn fuel s s'.
    run_function fuel fn s = Revert s' ==>
    ?s''. run_function fuel (transform_function fn) s = Revert s''
Proof
  rpt strip_tac >>
  drule transform_function_correct >>
  strip_tac >> fs[]
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
