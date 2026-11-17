(* Successful worklist exploration supplies a bounded, successor-closed
   abstract invariant.  No execution semantics are used in this theory. *)
Theory stackBoundClosure
Ancestors
  stackBoundDefs arithmetic list option pair finite_map vfmContext vfmOperation

(* Membership in the checker's pc-indexed collection of visited stacks. *)
Definition bytecode_stack_seen_def:
  bytecode_stack_seen seen (pc, stk:abstract_stack) <=>
    MEM stk (case FLOOKUP seen pc of NONE => [] | SOME stacks => stacks)
End

Theorem bytecode_stack_seen_update[local]:
  !seen pc stk q.
    bytecode_stack_seen
      (seen |+ (pc, stk ::
        (case FLOOKUP seen pc of NONE => [] | SOME stacks => stacks))) q <=>
    q = (pc,stk) \/ bytecode_stack_seen seen q
Proof
  rpt gen_tac >> PairCases_on `q` >>
  simp[bytecode_stack_seen_def, FLOOKUP_UPDATE] >>
  Cases_on `pc = q0` >> gvs[] >> metis_tac[]
QED

(* The frontier covers all outgoing edges of visited states.  Accepting
   exploration closes the frontier and preserves the checked height bound. *)
Theorem bytecode_stack_closure_invariant[local]:
  !fuel limit parsed dests todo seen.
    bytecode_stack_closure fuel limit parsed dests todo seen /\
    (!pc a. bytecode_stack_seen seen (pc,a) ==> LENGTH a <= limit) /\
    (!q q'. bytecode_stack_seen seen q /\
      MEM q' (bytecode_stack_successors parsed dests q) ==>
      bytecode_stack_seen seen q' \/ MEM q' todo) ==>
    ?C. (!q. bytecode_stack_seen seen q \/ MEM q todo ==> C q) /\
        (!pc a. C (pc,a) ==> LENGTH a <= limit) /\
        (!q q'. C q /\ MEM q' (bytecode_stack_successors parsed dests q)
                ==> C q')
Proof
  Induct_on `fuel`
  >- (rpt gen_tac >> Cases_on `todo`
      >- (simp[Once bytecode_stack_closure_def] >> strip_tac >>
          qexists_tac `bytecode_stack_seen seen` >> simp[] >> metis_tac[])
      >> PairCases_on `h` >> simp[Once bytecode_stack_closure_def]) >>
  rpt gen_tac >> Cases_on `todo`
  >- (simp[Once bytecode_stack_closure_def] >> strip_tac >>
      qexists_tac `bytecode_stack_seen seen` >> simp[] >> metis_tac[]) >>
  PairCases_on `h` >> rename1 `(pc,stk)::pending` >>
  simp[Once bytecode_stack_closure_def] >>
  Cases_on `bytecode_stack_seen seen (pc,stk)`
  >- (fs[GSYM bytecode_stack_seen_def] >> rpt strip_tac >>
      `!q q'. bytecode_stack_seen seen q /\
         MEM q' (bytecode_stack_successors parsed dests q) ==>
         bytecode_stack_seen seen q' \/ MEM q' pending` by metis_tac[] >>
      qpat_x_assum `!limit parsed dests todo seen. _` drule_all >> strip_tac >>
      qexists_tac `C` >> metis_tac[]) >>
  fs[GSYM bytecode_stack_seen_def] >> rpt strip_tac >>
  qpat_x_assum `!limit parsed dests todo seen. _` drule >>
  simp[bytecode_stack_seen_update, MEM_APPEND] >>
  (impl_tac >- (conj_tac >- metis_tac[] >> metis_tac[])) >>
  strip_tac >> qexists_tac `C` >> metis_tac[]
QED

Theorem bytecode_stack_check_closed:
  bytecode_stack_check fuel limit code ==>
  ?C. C (0,[]) /\
      (!pc a. C (pc,a) ==> LENGTH a <= limit) /\
      (!q q'. C q /\ MEM q' (bytecode_stack_successors
        (parse_code 0 FEMPTY code)
        (FILTER (\pc. FLOOKUP (parse_code 0 FEMPTY code) pc = SOME JumpDest)
                (GENLIST I (LENGTH code))) q) ==> C q')
Proof
  simp[bytecode_stack_check_def] >> strip_tac >>
  drule bytecode_stack_closure_invariant >>
  simp[bytecode_stack_seen_def, FORALL_PROD] >>
  metis_tac[]
QED
