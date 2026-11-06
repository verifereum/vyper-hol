Theory fnPlanLineageReachable
Ancestors
  fnPlanLineageSetup fnPlanLineageInventory stackPlanGen stackPlanTypes
  stackModel list finite_map pred_set

(* Candidate only: no reachability or preservation theorem is asserted.
   pos and pred identify the program point and incoming PHI projection;
   history records permitted residual physical identities. queries is the
   stack-only search footprint at THIS stage, not all future queries.
   Equal spill coverage is deliberately not a substitute for a core hit. *)
Definition lineage_pair_candidate_def:
  lineage_pair_candidate (pos:num) (pred:string) demand queries history ps qs <=>
    ps.ps_alloc = qs.ps_alloc /\ ps.ps_spilled = qs.ps_spilled /\
    (?left right core.
      ps.ps_stack = left ++ core /\ qs.ps_stack = right ++ core /\
      EVERY (\x. MEM x history) (left ++ right) /\
      (!v. MEM v demand ==>
        MEM (Var v) core \/ Var v IN FDOM ps.ps_spilled) /\
      (!v. MEM v demand ==>
        LIST_ELEM_COUNT (Var v) ps.ps_stack +
          (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) /\
      (!x. MEM x queries ==>
        MEM x core \/ (~MEM x left /\ ~MEM x right)))
End

Theorem lineage_pair_candidate_diagonal:
  !pos pred demand queries history ps.
    EVERY (\v. MEM (Var v) ps.ps_stack) demand /\
    ALL_DISTINCT ps.ps_stack /\ ps.ps_spilled = FEMPTY ==>
    lineage_pair_candidate pos pred demand queries history ps ps
Proof
  rpt gen_tac >> strip_tac >>
  simp[lineage_pair_candidate_def] >>
  qexistsl_tac [`[]`, `[]`, `ps.ps_stack`] >>
  simp[] >> conj_tac
  >- gvs[EVERY_MEM] >>
  rpt strip_tac >> irule all_distinct_elem_count_le_one >> simp[]
QED

Theorem lineage_pair_candidate_parameters:
  !fn ch growth spill_base ctr pos pred queries history.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    lineage_pair_candidate pos pred
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
      queries history
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base ctr)))
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base ctr)))
Proof
  rpt strip_tac >> irule lineage_pair_candidate_diagonal >>
  drule_all native_parameter_inventory >> strip_tac >>
  drule_all native_parameter_coverage >> simp[]
QED

(* Local closure stress test, NOT a reachable task counterexample. A stale
   prefix is initially shielded by the current copy. Selective spilling
   removes the shield while retaining coverage in the common spill map. *)
Definition candidate_spill_left_def:
  candidate_spill_left =
    (init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"]
End
Definition candidate_spill_right_def:
  candidate_spill_right =
    (init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"; Var "x"]
End

Theorem candidate_spill_before:
  lineage_pair_candidate 0 "entry" ["x"] [Var "x"] [Var "x"]
    candidate_spill_left candidate_spill_right
Proof
  simp[lineage_pair_candidate_def, candidate_spill_left_def,
       candidate_spill_right_def] >>
  qexistsl_tac [`[]`, `[Var "x"]`, `[Var "x"]`] >> EVAL_TAC
QED

Theorem candidate_spill_after_fails:
  ~lineage_pair_candidate 1 "entry" ["x"] [Var "x"] [Var "x"]
    (SND (do_spill_tos candidate_spill_left))
    (SND (do_spill_tos candidate_spill_right))
Proof
  EVAL_TAC >> simp[]
QED

(* Transition-premise matrix for this candidate (all closure rows OPEN).

   At position (pos,pred) the IH is lineage_pair_candidate pos pred D Q H ps qs.
   The desired next IH is the same predicate at the next position with that
   stage's actual D', Q', H' and the two actual resulting states.

   INITIAL/PARAMETERS: checked diagonal instance above. native_parameter_inventory
   and native_parameter_coverage supply canonical coverage and uniqueness.
   This does NOT yet include block cleanup or prove an arbitrary entry D.

   CLEANUP/BLOCK SETUP: shared-core cleanup replay coordinates code only with
   distinct core and equal allocators. The candidate gives neither core
   distinctness for dead names nor aligned cleanup choices. New D' coverage,
   spill coverage and new Q' shielding must also be established. OPEN.

   ORDINARY INPUT/REORDER/POP: native_regular_next_live_upper requires coverage
   of compute_operands, upper resource for operand_vars operands ++ nl,
   distinct outputs, and input physical absence of every output. Candidate
   supplies these bounds only when D includes those variables; it does NOT
   supply output freshness. native_regular_last_use_extinction can erase a
   uniquely represented consumed name not in nl or outputs, with <=16 operands.
   Neither theorem alone produces output freshness or next footprint shielding.
   Core-relative absence also does not instantiate the native upper theorem's
   whole-canonical-stack absence premise. OPEN.

   SELECTIVE SPILL/OPTIMISTIC SEARCH: even fixed D and Q are not preserved by
   do_spill_tos, as candidate_spill_before/after_fails show. Coverage moves to
   spills but stack-only queries can see an older residual identity. H merely
   bounds permitted residual names; it has no epoch or last-survivor argument.
   Enlarging H or shrinking D cannot repair this Q clause. OPEN (checked local
   failure). The example does not prove this query occurs on a ready path.

   PHI PREFIX: existing native schedule replay supplies equal common suffixes
   at successful join origins. Input projection and repeated source renaming
   require sequential, not simultaneous, demand. Candidate must be transported
   from D to the exact per-PHI D', updating H and Q after each rename. It supplies
   no old-output extinction or epoch information. OPEN.

   TERMINAL JMP: coverage of distinct targets gives restoration capacity only
   if D includes all projected targets and their distinctness is established.
   Guarded support plus join_reached yields suffix facts, not next demand or
   query shielding. Variable residual prefixes remain permitted. OPEN.

   DFS SAVE/SIBLING: saved stacks and spill maps must satisfy the next block's
   projected D, while evolving allocator fields are spliced in by the planner.
   Candidate equal-field clauses are relational and do not themselves prove
   this mixed state is a valid next certificate. OPEN.

   LINEAGE SPLICE/BACKEDGE: actual_dfs_fields aligns non-stack fields but does
   not align demand resources or Q. A finite history of names H is insufficient
   to distinguish the current definition from the stale copy in the checked
   spill test. A temporal epoch/last-surviving-copy argument or an actually
   smaller reachable search footprint is needed before induction. OPEN.

   DISPOSITION: initialization is checked; universal closure is NOT validated.
   Do not use this candidate as a premise in the frozen theorem. In particular
   no deep-join or cyclic fixture is claimed to establish its preservation.
*)
