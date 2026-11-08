# One-time semantic frame / runtime safety contract audit

C1.image.units diagnostic. No new definition, theorem, source candidate, or target
change. This report separates applicable static facts from missing dynamic facts.

## Exact queried frame

bodyPtrPreds 20-25 quantifies d, PG, tops, ctx, func, cenv, env, requested ty, es.
body_inv and expr_body_pre imply BOTH expression judgments. After unfolding the
vv judgment (bodyPtrDefs 296-325), the additional entry hypotheses are:
compile_expr result (vv,sb) from sa; fn_has_code sa sb func; distinct instruction
ids; local_ptrs_reserved; no context DALLOCA; runtime not constructor; old return
buffer/PC variable conditions; gas_admissible source eval; stmt_state_rel at s0;
ghost_inv d ... G0 tn0 s0; not halted; PC at sa boundary. PG,G0,tn0 are arbitrary
quantified inputs subject ONLY to these clauses. There is no frame_reachable
premise. The expression need not be an AST occurrence in tops.

## Definition expansion and implication table

| Desired bridge premise | What actual queried frame supplies | Verdict |
|---|---|---|
| Successful installed context | body_inv 61-88: actual runtime/deploy lower unit = SOME, ctx equality, target policy, support and built function/struct/event metadata | derivable |
| Function membership/lookup | stmt_state_rel 412-422 includes alloca_room. alloca_room 245ff explicitly requires lookup_function func.fn_name ctx.ctx_functions = SOME func | derivable lookup; not runtime reachability |
| Active instruction at requested PC | fn_has_code + PC boundary identifies compiled code when nonempty; emptiness/termination handled separately | local code reasoning possible; not entry reachability |
| Consistent source/target data | state_rel compileEnv 1465-1480: local_ptrs_rel, storage/transient/account/immutable/log/call context relations, nonstatic, outcomes, request agreement, pending deletions | derivable; no ghost history or path |
| Allocation bounds | stmt_state_rel: alloca_inv; alloca_room; fmp_room; immutable separation/base; recorded allocation sizes agree with ALLOCA literal | derivable disjointness/frontier/size facts; not access bounds for every arithmetic-derived pointer |
| Source typing of local queried e | expr_body_pre includes well_typed_expr env e, expr_sim_inv, widths/limits/call-safety/ABI conditions | derivable for queried e; not all installed source |
| Pointer static confinement | lower_vyper_runtime_unit_fn_ptr_ok (vyperLoweringCorrect 1071ff) and ptr_ok_check_sound (ptrOkCheck 282-292) yield fn_ptr_ok for functions and reachable_fn | derivable via success/checker bridge (runtime); static only |
| PC reachable from canonical entry | frame_reachable inductive ptrDiscipline 456-507 starts enters_block at actual ctx_entry and active inst, then actual step_inst/block/call/return transitions | ABSENT; alloca_room lookup and local state_rel do not assert these transitions |
| Canonical starting ghosts | frame_reachable_entry uses PG=[], G=FEMPTY, entry_taint; calls derive PG from caller operand provenance and reset callee ghosts; subsequent rules use step_prov/step_taint/entry_prov | ABSENT for arbitrary PG,G0,tn0 of judgment |
| Entry-to-current ghost history | frame_reachable_next/block/call/ret explicitly thread provenance and taint | ABSENT; ghost_inv is not that history |
| Every-fuel entry safety | ptr_safe_ptr_discipline 1072-1084 has this as premise, not conclusion | ABSENT; cannot invert theorem |
| Current arbitrary-ghost dynamic edge safety | access_ok/taint_ok/ptr_safe_step for current state/ghost and actual instructions | NOT supplied by static fn_ptr_ok; must be proved compositionally or by new valid bridge |

alloca_room's remaining conjuncts: finite transitive call closure, acyclic called
functions, frontier + pending allocation size + call-depth-cardinality times
unit_alloca_frame below dimword256. This is a capacity budget, not a witness of
execution to the PC. state_rel does not constrain PC except through local binding
relations, nor require source evaluation to have followed installed source code.

## Ghost invariant is deliberately local

bodyPtrDefs 80-92 constrains live PtrVar locals found in es.scopes and ce_vars:
untainted ptr_covers for declared region and values surviving memory taint;
return_buf_ptr for d, untainted return PC and stor_taint_ok. ptr_covers 45-49
requires actual operand value, provenance allocation and capacity. ghost_inv
does not constrain every compiler temporary, initialize every PG, assert an
entry history, or imply arbitrary temporary MSTORE access_ok. It can be vacuous
for locals in an empty environment. This is not itself a counterexample: fn code
and all other frame requirements must still be inhabited simultaneously.

## Verified theorem directions / dependencies

* ptrOkCheck.ptr_ok_check_sound concludes fn_ptr_ok and fn_ptr_ok(reachable_fn).
  Its proof uses static checker soundness, not this target; it supplies no
  dynamic ptr_safe_run, gas path or relation to G0/tn0.
* ptrSafeRun.ptr_safe_ptr_discipline concludes ptr_discipline and taint_within
  only after assuming ALL fuel ptr_safe_blocks at canonical entry. Its local
  frame_reachable_ptr_point also assumes that safety. Backward use is circular.
* loweringPtrCorrect.lower_vyper_runtime_unit_run_ptr_safe_composed 48-70 DOES
  conclude all-fuel entry safety, but assumes source_typing_ok/storage/deployment,
  valid call, initial state, outcomes and all gas-mark nonexemption. More
  importantly its declared dependency chain (file 19-28) is loweringPtrBodyRun ->
  bodyStmtsSimPtr -> bodySimPtrMain's body induction. That induction consumes the
  expression case containing this target. Using it here is circular, even if
  locally inherited admissions permit importing it. It also only initializes
  PG=[],G=FEMPTY,entry_taint, not arbitrary queried ghosts.
* loweringMemCorrect.lower_vyper_runtime_unit_ptr_taint uses this S3 composed run
  (loweringPtrCorrect comments 13-14); it is equally circular and has stronger
  global source/transaction premises absent from the queried frame.
* gasPathPtrExec.gas_path_ptr_exec consumes an already established counted pointer
  path to derive execution. It cannot supply the path's safe edges from S1.

No acyclic applicable dynamic-safety chain was identified. This is a bounded
contract audit, not a statement that no such lemma could ever be proved.

## Even safe edges would not finish this judgment

gas_outcome_ptr must match the source evaluation (including gas observations,
exception/exemption outcomes) with a counted path. The normal vv post additionally
requires vv_post, exact sb PC, ghost_inv in final source state, ptr_vv_ok, full
ptr_buf_ok for memory LocatedValue and nonword StackValue, and ghost_kept for
older variables. The lower-value judgment requires expr_post and ptr_val_ok.
Static confinement or even dynamic ptr_inst_ok alone proves none of this source
simulation/postcondition package. S1 erase results do not upgrade to S3 paths.

## Minimal missing contract / recommendation

A semantic completion route needs a noncircular derivation, from the EXACT frame
antecedents above and target operand hypotheses, of counted Concat evaluation
with arbitrary PG,G0,tn0 and all specified posts. The known detached id11
Concat overhang prevents casually postulating an unrestricted fragment-safety
lifting theorem. Reachability cannot be inserted as a new frozen hypothesis.

If attempting falsehood instead, the exact witness specification is:
1. fixed cx,ty,Concat n,args satisfying arity implication/body_exprs_ptr_ok;
2. tops, policy, successful actual unit, ctx, cenv, env, es with body_inv and
   expr_body_pre of queried Concat (source itself need not contain Concat);
3. actual installed func, sa,sb,vv, compile_expr equality and fn_has_code FULL
   compiled fragment, ids distinct, reserved locals/old return vars, no DALLOCA;
4. concrete s0,G0,tn0,d,PG satisfying stmt_state_rel, ghost_inv, runtime/nonhalt
   and PC boundary plus gas_admissible;
5. checked failure of gas_outcome_ptr (not merely one chosen path), e.g. forced
   deterministic successful source evaluation/unique target prefix with an
   unsafe mandatory edge, ruling out exceptions, exemptions and alternate paths.

Current detached literal-Concat fixtures cover portions of 1,4,5 separately,
not the installed full-code and simultaneous-frame clauses. Do NOT call this an
admissible counterexample. Recommend resolving the independent finite Slice
global-guard diagnostic next, then strategist selection; no new image search or
generic checker-to-dynamic-safety theorem is justified by this audit.
