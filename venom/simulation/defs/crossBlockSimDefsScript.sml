(*
 * Cross-Block Simulation — Definitions
 *
 * Generalizes lift_result to allow cross-result block simulation:
 * one side may return OK (continue) while the other returns terminal,
 * with the continuing side resolving to a matching terminal result
 * within a bounded number of additional block steps.
 *
 * Example: RTA transforms JNZ @revert → ASSERT (inline revert).
 *   Original block: OK (jump_to @revert)
 *   Transformed block: Abort Revert_abort
 *   Resolution (n=1): run original's revert block → Abort Revert_abort
 *
 * Standard lift_result is the special case n=0 (no resolution needed).
 *
 * TOP-LEVEL:
 *   resolves_to          — bounded-step resolution relation
 *   resolving_block_sim  — existential wrapper (some n exists)
 *)

Theory crossBlockSimDefs
Ancestors
  passSimulationDefs

(* ===== Resolution-based block simulation ===== *)

(* resolves_to R_ok R_term bbs1 bbs2 n r1 r2:
   Block results r1, r2 are related, allowing up to n extra block steps
   on whichever side returned OK while the other is terminal.

   bbs1: blocks for resolving r1 (original function)
   bbs2: blocks for resolving r2 (transformed function)
   n: resolution budget

   n=0: standard lift_result (no extra steps)
   n=k+1: lift_result, OR one side takes a block step and resolves in k *)
Definition resolves_to_def:
  (resolves_to R_ok R_term bbs1 bbs2 0 r1 r2 <=>
    lift_result R_ok R_term R_term r1 r2) /\
  (resolves_to R_ok R_term bbs1 bbs2 (SUC n) r1 r2 <=>
    lift_result R_ok R_term R_term r1 r2 \/
    (* Original continues: run next block, resolve remainder *)
    (?v bb. r1 = OK v /\ ~v.vs_halted /\
      lookup_block v.vs_current_bb bbs1 = SOME bb /\
      !fuel ctx.
        resolves_to R_ok R_term bbs1 bbs2 n
          (run_block fuel ctx bb (v with vs_inst_idx := 0)) r2) \/
    (* Transformed continues: symmetric *)
    (?v bb. r2 = OK v /\ ~v.vs_halted /\
      lookup_block v.vs_current_bb bbs2 = SOME bb /\
      !fuel ctx.
        resolves_to R_ok R_term bbs1 bbs2 n
          r1 (run_block fuel ctx bb (v with vs_inst_idx := 0))))
End

(* Existential wrapper: block results are related with some resolution bound *)
Definition resolving_block_sim_def:
  resolving_block_sim R_ok R_term bbs1 bbs2 r1 r2 <=>
    ?n. resolves_to R_ok R_term bbs1 bbs2 n r1 r2
End
