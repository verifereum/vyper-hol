Theory dftOpenAdequacy
Ancestors
  dftOpenMachine gasOracleReplay venomExecSemantics venomInst stateEquiv
  dftSparseOracle list rich_list arithmetic

Definition dft_open_result_eq_def:
  dft_open_result_eq r r' <=> lift_result (=) (=) (=) r r'
End

Theorem dft_open_result_eq_OK[simp]:
  dft_open_result_eq r (OK s) <=> r = OK s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Halt[simp]:
  dft_open_result_eq r (Halt s) <=> r = Halt s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_IntRet[simp]:
  dft_open_result_eq r (IntRet ret s) <=> r = IntRet ret s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Abort[simp]:
  dft_open_result_eq r (Abort reason s) <=> r = Abort reason s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Error[simp]:
  dft_open_result_eq r (Error e) <=> ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_zero_replay_materialize:
  gas_replay_at 0 f s ==>
  dft_open_result_eq (f (dft_open_materialize xs n s))
    (dft_open_materialize_result xs n (f s))
Proof
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `DROP n xs` mp_tac) >>
  Cases_on `f s` >> Cases_on `f (s with vs_gas_readings := DROP n xs)` >>
  simp[lift_result_def, dft_open_materialize_def,
       dft_open_materialize_result_def, dft_open_result_eq_def] >>
  metis_tac[]
QED

Theorem dft_open_base_materialize:
  inst.inst_opcode <> GAS ==>
  dft_open_result_eq (step_inst_base inst (dft_open_materialize xs n s))
    (dft_open_materialize_result xs n (step_inst_base inst s))
Proof
  strip_tac >> irule dft_zero_replay_materialize >>
  simp[gas_base_non_gas]
QED

Theorem dft_open_phis_materialize:
  dft_open_result_eq (eval_phis (dft_open_materialize xs n s) insts)
    (dft_open_materialize_result xs n (eval_phis s insts))
Proof
  irule (dft_zero_replay_materialize |> SPEC_ALL |>
    Q.INST [`f` |-> `\u. eval_phis u insts`] |> BETA_RULE) >>
  simp[gas_eval_phis]
QED

Theorem dft_open_gas_materialize:
  dft_sparse_oracle a xs /\ inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  step_inst_base inst (dft_open_materialize xs n s) =
    OK (dft_open_materialize xs (SUC n) (update_var out (a n) s))
Proof
  strip_tac >>
  simp[step_inst_base_def, exec_gas_def, dft_open_materialize_def] >>
  `a n = if n < LENGTH xs then EL n xs else 0w` by
    metis_tac[dft_sparse_oracle_def] >>
  Cases_on `n < LENGTH xs`
  >- (drule DROP_CONS_EL >> disch_then SUBST1_TAC >> simp[]) >>
  `DROP n xs = [] /\ DROP (SUC n) xs = []` by simp[DROP_EQ_NIL] >>
  simp[]
QED

Theorem dft_open_bad_gas_materialize:
  inst.inst_opcode = GAS /\ (!out. inst.inst_outputs <> [out]) ==>
  step_inst_base inst (dft_open_materialize xs n s) =
    Error "read0 requires single output"
Proof
  simp[step_inst_base_def, exec_gas_def] >> rpt strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

Theorem dft_open_setup_materialize:
  setup_callee callee args (dft_open_materialize xs n s) =
    OPTION_MAP (dft_open_materialize xs n) (setup_callee callee args s)
Proof
  simp[dft_open_materialize_def, gas_setup_callee] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, dft_open_materialize_def]
QED

Theorem dft_open_return_materialize:
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret
      (merge_callee_state (dft_open_materialize xs i caller)
                          (dft_open_materialize xs n cs))) =
  OPTION_MAP (dft_open_materialize xs n)
    (bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state caller cs)))
Proof
  simp[dft_open_materialize_def, gas_merge_callee, gas_adopt_return,
       gas_bind_outputs] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM, dft_open_materialize_def]
QED

(* C3.2.6 DESIGN REPORT (specifications only, not new theorem claims).

   Use the following meta-abbreviations in the proposed contracts:
     M n s = dft_open_materialize xs n s
     MR n r = dft_open_materialize_result xs n r
     Q r r' = dft_open_result_eq r r'
     Next = dft_open_next a ctx
   All contracts have premise dft_sparse_oracle a xs.

   A segment should STOP at a relative stack boundary, before resuming the
   saved stack K.  A candidate boundary predicate for run_blocks is:
     B K c <=> ?r st m. c = DftOpen (DftDone r) st m /\
       (st = K \/ (st = [] /\
         ((?e. r = Error e) \/ (?s. r = Halt s) \/ (?z s. r = Abort z s))))
   A first-hit path to a boundary E has the exact proposed definition
     Hit E c d <=> ?k. FUNPOW Next k c = d /\ E d /\
                         !j. j < k ==> ~E (FUNPOW Next j c).
   This must not be replaced by arbitrary RTC reachability: DftDone IntRet
   at stack K is the endpoint even when K is nonempty.  The next transition
   would consume a caller continuation, and is OUTSIDE the segment.

   Forward run_blocks contract, with arbitrary counter n and saved stack K:
     run_blocks fuel ctx fn (M n s) = r ==>
     ?rr m st.
       Hit (B K) (DftOpen (DftEnter fn fuel s) K n)
                 (DftOpen (DftDone rr) st m) /\ Q (MR m rr) r
   Fatal outcomes may clear K; IntRet must preserve K at this endpoint.
   Add m >= n to every segment theorem.  run_blocks cannot return OK;
   this needs an explicit lemma, not an omitted case.

   exec_block and step_inst cannot share that boundary: their OK results
   already become a branch entry or the next instruction in this machine.
   Candidate exec boundary is B K, additionally allowing
     DftOpen (DftEnter fn budget t) K m.
   Candidate step boundary additionally allows the next DftAt at stack K,
   and branch entry at stack K.  The endpoint predicates must be first-hit
   independent of the EXPECTED result; otherwise a path could run through
   the caller until it happens to encounter that result.

   Exact forward exec_block contract:
     exec_block budget ctx bb (M n s) = r ==>
     ?rr m d. Q (MR m rr) r /\
       Hit Eblock (DftOpen (DftAt fn budget bb s) K n) d /\
       (case rr of OK t => d = DftOpen (DftEnter fn budget t) K m
        | _ => ?st. d = DftOpen (DftDone rr) st m /\ B K d)
   Here Eblock c <=> B K c \/
     (?t m. c = DftOpen (DftEnter fn budget t) K m).
   An OK result here must have ~t.vs_halted: exec_block converts a halted
   terminator to Halt, and only terminators return OK.  Prove this fact.

   Exact forward step_inst contract, given get_instruction bb s.vs_inst_idx
   = SOME inst:
     step_inst budget ctx inst (M n s) = r ==>
     ?rr m d. Q (MR m rr) r /\
       Hit Estep (DftOpen (DftAt fn budget bb s) K n) d /\
       (case rr of OK t =>
          d = DftOpen (dft_open_continue fn budget bb inst s t) K m
        | _ => ?st. d = DftOpen (DftDone rr) st m /\ B K d)
   Estep c <=> B K c \/ (?t m.
     c = DftOpen (DftEnter fn budget t) K m) \/ (?t m.
     c = DftOpen (DftAt fn budget bb t) K m /\
     t.vs_inst_idx = SUC s.vs_inst_idx).
   This is a FORWARD contract, not an iff: dft_open_continue overwrites the
   instruction index and converts OK halted terminators to Halt.  An exact
   reverse step-result theorem cannot be inferred from that endpoint.
   Reverse whole-run adequacy needs a separate machine-path soundness proof
   with a stack interpretation; constructor determinism alone is not enough.

   run_defs_ind was inspected (tool evidence in E0006 successor episode):
   P0 has just the guarded recursive callee run_blocks IH; P1 has both the
   instruction IH and the recursive nonterminator exec_block IH; P2 has
   block-execution IH and recursive next-block IH at fuel'.  Its next-block
   guard prints run_block_non_phis, not exec_block; check the wrapper equation.
   Mapping: P0/INVOKE uses push + P2 callee segment + one return-pop, binding
   through dft_open_return_materialize.  Callee Halt/Abort/Error propagates;
   callee OK requires the no-OK lemma.  P1 joins the P0 segment to the tail
   P1 segment iff OK and nonterminator; otherwise stop at Eblock (converting
   halted terminator OK to Halt).  P2 performs block lookup/phi entry and P1;
   OK nonhalt joins the next P2 segment.  Phi/fuel/lookup errors terminate
   immediately, possibly with [].  Error strings are irrelevant to Q only;
   non-Error states remain EXACT.  First-hit segment concatenation and stack
   restoration are separate proof obligations before this mutual induction.

   Raw interfaces, independently of fixed-fuel terminal adequacy:
   retain the exact state equivalence proposed in dftOpenMachine's comment.
   Prove its two implications separately with resolvable context entry,
   unique block labels in EVERY context function, and the fixed sparse a.
   Completeness strengthens to: for every q there is B such that for every
   root fuel F >= B there are steps,budget,bb,ghost,K,n with budget >= q,
   FUNPOW Next steps (DftOpen (DftEnter entry F initial) [] 0) =
     DftOpen (DftAt fn budget bb ghost) K n,
   get_instruction bb ghost.vs_inst_idx = SOME inst and observed = M n ghost.
   Soundness states that any such finite prefix implies raw_reachable for
   observed; it needs an invariant covering saved callers, not just the
   currently active fn.  No same-fuel raw equivalence is proposed.

   Concrete sufficient-root-bound recurrence for a finite raw derivation:
     entry:             B(q) = q + 1
     next with fuel f:  B(q) = Bpred(MAX q f)
     block with fuel f: B(q) = Bpred(MAX (q + 1) f)
     callee entry:      B(q) = Bpred(q + 1).
   The predecessor's universal F>=B contract is essential.  At next/block,
   fuel_mono raises successful step_inst f = OK s' to the available active
   budget; that theorem explicitly excludes ALL Error results.  Returning
   INVOKE restores the same caller budget; block/callee entry costs one.
   First prove forward step segments and monotone budget decoration of their
   endpoint counters/ghost states; do not infer counter equality from equality
   of list results (exhausted zero reads erase that information).

   Dispatch interface needed for both directions:
     ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
     ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
          get_instruction bb s.vs_inst_idx = SOME inst.
   Block-entry dispatch contract:
     ALL_DISTINCT (fn_labels fn) /\ enters_block fn s t /\
     active_inst fn inst t ==>
     ?bb sp. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       eval_phis s bb.bb_instructions = OK sp /\
       t = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
       get_instruction bb t.vs_inst_idx = SOME inst.
   This additionally needs eval_phis to preserve current_bb.  wf_function
   supplies uniqueness.  Prove dispatch separately before raw induction.

   Proposed proof leaves for strategist review (NOT executor-created PLAN):
   no-OK/exec-OK classification; unique-label dispatch; first-hit composition
   and stack propagation; forward mutual segments; stack/path soundness;
   raw completeness with the explicit bound recurrence; raw soundness.
   They depend on the already checked primitive/phi/call boundaries.  The
   proposed Hit/end predicates still require constructor validation before
   a general adequacy theorem is rated low-risk.  Uniform schedule matching
   remains entirely separate from this diagnostic.
*)

(* C3.2.7 MATCHING DESIGN CHECKPOINT -- specifications, NOT theorems.

   This report distinguishes a candidate declarative invariant from an
   executable prefix-extension construction.  The latter is still missing.
   No field below is an assumed global simulation or a theorem dependency.

   Dynamic names and records:
     activation p is a list of (block-visit-number, invoke-inst-id) edges,
       starting with []; recursively invoking the same function extends p.
     block occurrence b = (p, visit-number, block-label); visit-number counts
       ALL entries in that activation, not just entries of this static block.
     instruction occurrence u = (b, inst-id).
   Pair corresponding activations/visits, rather than requiring equality of
   their static function records. Calls must pair by u, not by stack depth
   alone. The two static instructions at u satisfy from_block, allowing the
   operand flip in the target instruction.

   A candidate per-frame record contains:
     source/target function, block and entry snapshots;
     executed sets Es,Et of u, and pending sets Ps,Pt;
     receipt tables Rs,Rt: u -> option (operand-values, result-values);
     environments Hs,Ht recording lookup_var for each captured operand;
     current effect frontier and saved caller continuation;
     a debt table for pure computations executed on only one side.
   A receipt can only be installed when eval_operands actually returns its
   recorded values; a pending instruction whose producer is also pending has
   no receipt yet. Do NOT freeze all operands at block entry. PARAM/PHI entry
   is paired before body scheduling; retain entry snapshots for PHI operands.
   Completed u never re-enters P in that visit. Ps and Es partition the source
   body occurrences, and similarly for target. The domain of each R is E.

   Candidate relation I(A,hs,ht):
     (1) stacks and block occurrences have the paired names above;
     (2) the executed/pending partitions and receipts are well formed;
     (3) shared completed producers have equal result-values (accounting for
         operand flips); captured operands of any completed consumer equal
         the corresponding producer receipt or its entry-environment value;
     (4) memory, other externally observable effect fields, and operands at
         paired effectful frontiers agree. Different variable maps are
         allowed only for defs of outstanding pure debts. Any instruction
         crossed by a debt has no conflicting defs/uses/effects;
     (5) h maps each successful GAS occurrence u to its chronological counter
         on that side, injectively. Every paired, completed GAS has equal
         values. A : num -> num option is persistent and injective on SOME;
         when both GAS receipts are present, A(hs(u)) = SOME(ht(u));
     (6) a source-only receipt carries either an unresolved obligation named
         by target u, or a FINAL erased mark with value 0w. Erasure requires
         a proof that this counterpart will never be reached in the
         unbounded target computation; finite out-of-fuel is NOT that proof.
   Clause (6) is intentionally an unresolved obligation, not a usable
   invariant field. Replacing it with a chosen value and assuming future
   compatibility would simply assume the hard matching result.

   Proposed contracts (notations: step* is a finite open-machine prefix;
   a_s n = case A n of NONE => 0w | SOME m => a_t m):
     Init: related contexts and related block entry environments imply
       I(empty, entry_s, entry_t), with empty receipt/debt tables and counters
       0. Here empty is a finite allocation fragment, NOT the final A.
     Ordinary: I(A,c,d) and a ready non-GAS/non-INVOKE step on one side
       imply finite opposite-side catch-up to I(A,c',d'), or a pure debt
       carrying its actual captured operands. No effectful step may be
       hidden as debt. Aborts need compatible stopping, not OK commutation.
     GAS: installing a paired GAS receipt extends A at hs(u) with ht(u),
       preserves old SOME entries and preserves injectivity. When only the
       source reaches u, a stream value is not yet available from this rule.
     Push: catch up to the same dynamic INVOKE occurrence with equal args;
       setup_callee creates paired child entries; save each caller's local
       partitions, receipts, environments and budget. Pure debts may stay
       with the suspended caller. Shared chronological GAS counters do NOT
       reset on push. Calls themselves must keep order.
     Return: at corresponding IntRet, merge equal callee effect fields and
       bind equal return values; restore saved partitions and environments;
       discharge newly enabled debts, without resetting GAS counters or A.
     Extract: from an unbounded coherent receipt history, obtain ONE total
       partial injection A extending all its allocation fragments. Show
       source terminations match target terminations modulo dead_result_rel
       and every target pre-memory observation has a source observation with
       equal memory and operand values. The source stream must be a_s for
       this SAME A for every fuel. dftSparseOracle supplies a finite source
       list only AFTER this contract, not its semantic proof.

   Supporting facts actually present, and limits:
     dft_block_rel_def: permutation of IDs, from_block, and must-order;
       it does not supply dynamic receipts or a coinductive matching path.
     dft_target_head_extract: finite head extraction by static ID.
     dft_ssa_inversion_pair, dft_inversion_compatible: independence and abort
       compatibility of inversions, under their SSA/wf/no-ALLOCA hypotheses.
     dft_must_order_invokes: two INVOKEs cannot be an inversion.
     eval_operand_step_pres, output_var_agree_across_independent: preservation
       of operand/output values for successful independent steps.
     independent_commute_eq: finite successful same-context non-gas swaps.
     gas_pair_commute: two SUCCESSFUL steps in reverse order supply a new
       list start state. It neither covers an open nonreturning INVOKE nor
       preserves allocations already fixed in other finite observations.
     dft_open_invoke_push, dft_open_return_resume and
       dft_open_return_materialize: single-machine call boundaries only.
   Missing semantic leaves: debt/environment preservation including operand
   flips; open-call effect-frontier alignment under distinct contexts;
   abort-compatible finite stopping; prefix-compatible GAS reservation;
   and fuel-independent extraction with raw observations. None follows by
   applying the finite successful swap lemmas to a divergent callee.

   Adversarial trace checks (symbolic traces, NOT checked counterexamples):
   A. Source G(u); CALL(v); ... and target CALL(v); G(u); ... . If v never
      returns, source u can be erased with value 0w, while callee occurrences
      pair by their own dynamic names. Independence forbids call arguments
      from depending on u. If v DOES return after k GAS reads, target u has
      index k (assuming no earlier reads); source u needs a_t(k). At source
      u, no finite open prefix reveals k, nor whether v returns at all.
      For each finite fuel cutoff v can fail before returning, even when it
      eventually returns at larger fuel. Assigning NONE/zero at that cutoff
      is not persistent: choose a_t(k) nonzero. This refutes that GREEDY
      construction, not the frozen theorem or declarative existence of A.
   B. Terminating v with callee reads t0,...,t(k-1): source indices are
      u=0 and callee j=j+1; target callee j=j and u=k. Correct allocation is
      A(0)=SOME k and A(j+1)=SOME j. Saved caller operands independent of u
      may be captured before suspension; all later consumers of u must wait
      for its receipt. gas_pair_commute supports the completed finite swap,
      but its existential alone gives no stable prefix reservation.
   C. Source G(x);G(y), target G(y);G(x): A(0)=SOME 1, A(1)=SOME 0. There
      are no GAS operands to capture; disjoint outputs give equal receipts
      after the two steps, even if values coincide or the stream is zero.
      Counters must not be identified from values. An append-only matching
      strategy by chronological index would already fail this case.
   D. Repeated block visits: source G(x);G(y) in every visit, target reversed.
      The nth visit pairs (p,n,label,x) and (p,n,label,y), not the previous
      visit's x/y. With two reads per visit A(2n)=SOME(2n+1),
      A(2n+1)=SOME(2n). Calls/branches add dynamic path edges and may add a
      variable number of intervening reads; static-ID allocation is invalid.

   Checkpoint conclusion: a literal prefix machine with concrete source
   states has no justified deterministic GAS extension in case A. A design
   must either reserve symbolic values/occurrence names until an unbounded
   target trace resolves them, with a separate realization theorem, or prove
   a non-greedy unbounded matching construction. Do not add future agreement
   as a premise. The single-machine adequacy work remains independent, but
   completing it would NOT resolve this allocation design gap. Request a
   strategist redesign/probe at this boundary before any global proof.
*)

Theorem dft_exec_block_ok_not_halted:
  !fuel ctx bb s t. exec_block fuel ctx bb s = OK t ==> ~t.vs_halted
Proof
  rpt gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block fuel ctx bb s = OK t` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rename1 `OK after` >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[]
  >- (Cases_on `after.vs_halted` >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> first_x_assum irule >>
  gvs[get_instruction_def] >> metis_tac[]
QED

Theorem dft_run_blocks_not_ok:
  !fuel ctx fn s t. run_blocks fuel ctx fn s <> OK t
Proof
  Induct >> rpt gen_tac >> simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[] >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  Cases_on `exec_block fuel ctx bb
    (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[] >>
  qmatch_goalsub_rename_tac `if after.vs_halted then _ else _` >>
  Cases_on `after.vs_halted` >> simp[]
QED

Definition dft_first_hit_def:
  dft_first_hit N E c k d <=>
    FUNPOW N k c = d /\ E d /\
    (!j. j < k ==> ~E (FUNPOW N j c))
End

Theorem dft_first_hit_one:
  ~E c /\ E (N c) ==> dft_first_hit N E c 1 (N c)
Proof
  simp[dft_first_hit_def, FUNPOW]
QED

Theorem dft_first_hit_unique:
  dft_first_hit N E c k d /\ dft_first_hit N E c l e ==>
  k = l /\ d = e
Proof
  rw[dft_first_hit_def] >>
  `k = l` by (spose_not_then assume_tac >>
              `k < l \/ l < k` by decide_tac >> metis_tac[]) >>
  gvs[]
QED

Theorem dft_first_hit_prefix:
  FUNPOW N k c = b /\ (!j. j < k ==> ~E (FUNPOW N j c)) /\
  dft_first_hit N E b l d ==>
  dft_first_hit N E c (k + l) d
Proof
  rw[dft_first_hit_def]
  >- metis_tac[FUNPOW_ADD, ADD_COMM] >>
  Cases_on `j < k` >- metis_tac[] >>
  `j = (j - k) + k /\ j - k < l` by decide_tac >>
  metis_tac[FUNPOW_ADD]
QED

Definition dft_open_run_boundary_def:
  dft_open_run_boundary stack c <=>
    ?r st m. c = DftOpen (DftDone r) st m /\
      (st = stack \/ (st = [] /\
        ((?e. r = Error e) \/ (?s. r = Halt s) \/ (?z s. r = Abort z s))))
End

Definition dft_open_inst_boundary_def:
  dft_open_inst_boundary fn budget bb stack i c <=>
    dft_open_run_boundary stack c \/
    (?t m. c = DftOpen (DftEnter fn budget t) stack m) \/
    (?t m. c = DftOpen (DftAt fn budget bb t) stack m /\ t.vs_inst_idx = SUC i)
End

Theorem dft_open_inst_boundary_initial:
  ~dft_open_inst_boundary fn budget bb stack s.vs_inst_idx
    (DftOpen (DftAt fn budget bb s) stack n)
Proof
  simp[dft_open_inst_boundary_def, dft_open_run_boundary_def]
QED

Theorem dft_open_deliver_boundary[local]:
  dft_open_inst_boundary fn budget bb stack s.vs_inst_idx
    (dft_open_deliver fn budget bb inst s stack m rr)
Proof
  Cases_on `rr` >>
  simp[dft_open_deliver_def, dft_open_continue_def,
       dft_open_inst_boundary_def, dft_open_run_boundary_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[]
QED

Theorem dft_open_non_invoke_segment:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = r ==>
  ?rr m d. n <= m /\
    dft_open_result_eq (dft_open_materialize_result xs m rr) r /\
    dft_first_hit (dft_open_next a ctx)
      (dft_open_inst_boundary fn budget bb stack s.vs_inst_idx)
      (DftOpen (DftAt fn budget bb s) stack n) 1 d /\
    (d = dft_open_deliver fn budget bb inst s stack m rr \/
     (?e. rr = Error e /\ d = DftOpen (DftDone rr) [] m))
Proof
  strip_tac >> gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `?out. inst.inst_outputs = [out]`
      >- (pop_assum strip_assume_tac >>
          drule_all dft_open_gas_materialize >> strip_tac >> gvs[] >>
          qexistsl_tac [`OK (update_var out (a n) s)`, `SUC n`,
            `dft_open_deliver fn budget bb inst s stack (SUC n)
              (OK (update_var out (a n) s))`] >>
          simp[dft_open_materialize_result_def] >>
          simp[dft_first_hit_def, dft_open_inst_boundary_initial, dft_open_next_def,
               dft_open_deliver_boundary]) >>
      `step_inst_base inst (dft_open_materialize xs n s) =
        Error "read0 requires single output"` by
        (irule dft_open_bad_gas_materialize >> metis_tac[]) >>
      gvs[] >> qexistsl_tac [`Error "read0 requires single output"`, `n`,
        `DftOpen (DftDone (Error "read0 requires single output")) [] n`] >>
      simp[dft_open_materialize_result_def] >>
      simp[dft_first_hit_def, dft_open_inst_boundary_initial, dft_open_next_def,
           dft_open_inst_boundary_def, dft_open_run_boundary_def] >>
      Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  qexistsl_tac [`step_inst_base inst s`, `n`,
    `dft_open_deliver fn budget bb inst s stack n (step_inst_base inst s)`] >>
  conj_tac >- simp[] >> conj_tac
  >- (drule dft_open_base_materialize >>
      disch_then (qspecl_then [`xs`, `s`, `n`] mp_tac) >>
      Cases_on `step_inst_base inst s` >>
      Cases_on `step_inst_base inst (dft_open_materialize xs n s)` >>
      simp[dft_open_result_eq_def, lift_result_def,
           dft_open_materialize_result_def]) >>
  simp[] >>
  simp[dft_first_hit_def, dft_open_inst_boundary_initial, dft_open_next_def,
       dft_open_deliver_boundary]
QED

Theorem dft_open_inst_boundary_pushed_entry:
  ~dft_open_inst_boundary fn budget bb stack i
    (DftOpen (DftEnter callee fuel t) (frame::stack) n)
Proof
  simp[dft_open_inst_boundary_def, dft_open_run_boundary_def] >>
  strip_tac >>
  `LENGTH (frame::stack) = LENGTH stack` by simp[] >> gvs[]
QED

Definition dft_open_stack_exit_def:
  dft_open_stack_exit bst c <=>
    (?r n. c = DftOpen (DftDone r) bst n) \/
    (?r n. c = DftOpen (DftDone r) [] n)
End

Definition dft_open_stack_extends_def:
  dft_open_stack_extends bst (DftOpen control stack n) <=>
    ?prefix. stack = prefix ++ bst
End

Theorem dft_open_deliver_stack[local]:
  dft_open_stack_extends bst (DftOpen control stack n) ==>
  dft_open_stack_extends bst
    (dft_open_deliver fn budget bb inst before stack m result)
Proof
  Cases_on `result` >>
  simp[dft_open_deliver_def, dft_open_stack_extends_def]
QED

Theorem dft_open_stack_step:
  dft_open_stack_extends bst c /\ ~dft_open_stack_exit bst c ==>
  dft_open_stack_extends bst (dft_open_next a ctx c) \/
  dft_open_stack_exit bst (dft_open_next a ctx c)
Proof
  Cases_on `c` >> rename1 `DftOpen control stack n` >>
  simp[dft_open_stack_extends_def] >> strip_tac >>
  Cases_on `control`
  >- (rename1 `DftEnter fn fuel s` >>
      Cases_on `fuel` >> simp[dft_open_next_def, dft_open_stack_exit_def] >>
      Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >>
      simp[dft_open_stack_exit_def] >>
      rename1 `SOME bb` >> Cases_on `eval_phis s bb.bb_instructions` >>
      simp[dft_open_stack_extends_def, dft_open_stack_exit_def])
  >- (rename1 `DftAt fn budget bb s` >>
      simp[dft_open_next_def] >> Cases_on `get_instruction bb s.vs_inst_idx`
      >- simp[dft_open_stack_exit_def] >>
      rename1 `SOME inst` >> Cases_on `inst.inst_opcode = INVOKE`
      >- (simp[dft_open_invoke_def] >>
          Cases_on `decode_invoke inst` >> simp[dft_open_stack_exit_def] >>
          rename1 `SOME p` >> PairCases_on `p` >> simp[] >>
          Cases_on `lookup_function p0 ctx.ctx_functions` >>
          simp[dft_open_stack_exit_def] >> rename1 `SOME callee` >>
          Cases_on `eval_operands p1 s` >> simp[dft_open_stack_exit_def] >>
          rename1 `SOME args` >> Cases_on `setup_callee callee args s` >>
          simp[dft_open_stack_extends_def, dft_open_stack_exit_def] >>
          qexists_tac `DftCaller fn budget bb inst s :: prefix` >> simp[]) >>
      Cases_on `inst.inst_opcode = GAS` >> simp[]
      >- (Cases_on `inst.inst_outputs` >> simp[dft_open_stack_exit_def] >>
          Cases_on `t` >> simp[dft_open_stack_exit_def] >>
          disj1_tac >> irule dft_open_deliver_stack >>
          simp[dft_open_stack_extends_def]) >>
      disj1_tac >> irule dft_open_deliver_stack >>
      simp[dft_open_stack_extends_def]) >>
  gvs[dft_open_next_def] >> Cases_on `prefix`
  >- gvs[dft_open_stack_exit_def] >>
  Cases_on `h` >> Cases_on `e` >>
  simp[dft_open_return_def, dft_open_stack_exit_def] >>
  Cases_on `bind_outputs i0.inst_outputs i'.iret_values
    (adopt_return_fmp i' (merge_callee_state v v'))` >> simp[] >>
  disj1_tac >> irule dft_open_deliver_stack >>
  simp[dft_open_stack_extends_def]
QED

Theorem dft_open_stack_iterate:
  !k c. dft_open_stack_extends bst c /\
    (!j. j < k ==> ~dft_open_stack_exit bst (FUNPOW (dft_open_next a ctx) j c)) ==>
    dft_open_stack_extends bst (FUNPOW (dft_open_next a ctx) k c) \/
    dft_open_stack_exit bst (FUNPOW (dft_open_next a ctx) k c)
Proof
  Induct_on `k` >- simp[] >> rpt strip_tac >>
  `dft_open_stack_extends bst (FUNPOW (dft_open_next a ctx) k c)` by
    (first_x_assum (qspec_then `c` mp_tac) >>
     impl_tac >- (conj_tac >- simp[] >> rpt strip_tac >>
                   `j < SUC k` by decide_tac >> metis_tac[]) >>
     `k < SUC k` by decide_tac >> metis_tac[]) >>
  simp[FUNPOW_SUC] >> irule dft_open_stack_step >>
  `k < SUC k` by decide_tac >> metis_tac[]
QED

Theorem dft_open_stack_confinement:
  dft_open_stack_extends bst c /\
  (!j. j < k ==> ~dft_open_stack_exit bst (FUNPOW (dft_open_next a ctx) j c)) ==>
  !j. j <= k ==>
    dft_open_stack_extends bst (FUNPOW (dft_open_next a ctx) j c) \/
    dft_open_stack_exit bst (FUNPOW (dft_open_next a ctx) j c)
Proof
  rpt strip_tac >> irule dft_open_stack_iterate >>
  conj_tac >- simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem dft_open_stack_boundary_separation:
  dft_open_stack_extends (frame::stack) c /\
  ~dft_open_stack_exit (frame::stack) c ==>
  ~dft_open_inst_boundary fn budget bb stack i c
Proof
  Cases_on `c` >> rename1 `DftOpen control st n` >>
  simp[dft_open_stack_extends_def] >> strip_tac >>
  `LENGTH stack < LENGTH (prefix ++ frame::stack)` by simp[] >>
  gvs[dft_open_inst_boundary_def, dft_open_run_boundary_def,
      dft_open_stack_exit_def] >>
  strip_tac >> gvs[]
QED

Theorem dft_open_callee_boundary_avoidance:
  dft_open_stack_extends (frame::stack) c /\
  (!j. j < k ==> ~dft_open_stack_exit (frame::stack)
    (FUNPOW (dft_open_next a ctx) j c)) ==>
  !j. j < k ==> ~dft_open_inst_boundary fn budget bb stack i
    (FUNPOW (dft_open_next a ctx) j c)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
  irule dft_open_stack_boundary_separation >>
  `j <= k` by decide_tac >>
  drule_all dft_open_stack_confinement >> metis_tac[]
QED

Theorem dft_open_invoke_bad_decode:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = NONE ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error "invoke: bad operand format")) [] n
Proof
  simp[dft_open_next_def, dft_open_invoke_def]
QED

Theorem dft_open_invoke_no_callee:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = NONE ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error "invoke: function not found")) [] n
Proof
  simp[dft_open_next_def, dft_open_invoke_def]
QED

Theorem dft_open_invoke_bad_args:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = NONE ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error "invoke: undefined argument")) [] n
Proof
  simp[dft_open_next_def, dft_open_invoke_def]
QED

Theorem dft_open_invoke_bad_setup:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = NONE ==>
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error "invoke: empty function")) [] n
Proof
  simp[dft_open_next_def, dft_open_invoke_def]
QED

Theorem dft_open_error_boundary:
  dft_open_inst_boundary fn budget bb stack i
    (DftOpen (DftDone (Error e)) [] n)
Proof
  simp[dft_open_inst_boundary_def, dft_open_run_boundary_def]
QED

Theorem dft_open_error_segment:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error e)) [] n ==>
  dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_boundary fn budget bb stack s.vs_inst_idx)
    (DftOpen (DftAt fn budget bb s) stack n) 1
    (DftOpen (DftDone (Error e)) [] n)
Proof
  simp[dft_first_hit_def, dft_open_inst_boundary_initial, dft_open_error_boundary]
QED

Theorem dft_open_invoke_push_not_boundary:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  ~dft_open_inst_boundary fn budget bb stack s.vs_inst_idx
    (dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n))
Proof
  strip_tac >> drule_all dft_open_invoke_push >>
  simp[dft_open_inst_boundary_pushed_entry]
QED

Theorem dft_open_return_bad_arity:
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = NONE ==>
  dft_open_next a ctx
    (DftOpen (DftDone (IntRet ret cs))
      (DftCaller fn budget bb inst caller::rest) n) =
    DftOpen (DftDone (Error "invoke: return arity mismatch")) [] n
Proof
  simp[dft_open_next_def, dft_open_return_def]
QED

Theorem dft_open_return_deliver:
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs)) = SOME after ==>
  dft_open_next a ctx
    (DftOpen (DftDone (IntRet ret cs))
      (DftCaller fn budget bb inst caller::rest) n) =
    dft_open_deliver fn budget bb inst caller rest n (OK after)
Proof
  simp[dft_open_next_def, dft_open_return_def]
QED

Theorem dft_open_return_boundary:
  dft_open_inst_boundary fn budget bb rest caller.vs_inst_idx
    (dft_open_next a ctx
      (DftOpen (DftDone (IntRet ret cs))
        (DftCaller fn budget bb inst caller::rest) n))
Proof
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller cs))` >>
  simp[dft_open_next_def, dft_open_return_def,
       dft_open_error_boundary, dft_open_deliver_boundary]
QED

Theorem dft_open_return_pre_pop_not_boundary:
  ~dft_open_inst_boundary fn budget bb rest i
    (DftOpen (DftDone (IntRet ret cs)) (frame::rest) n)
Proof
  simp[dft_open_inst_boundary_def, dft_open_run_boundary_def] >>
  strip_tac >> `LENGTH (frame::rest) = LENGTH rest` by simp[] >> gvs[]
QED

Theorem dft_open_propagate_endpoint:
  ((?e. r = Error e) \/ (?s. r = Halt s) \/ (?z s. r = Abort z s)) ==>
  dft_open_next a ctx (DftOpen (DftDone r) (frame::rest) n) =
    DftOpen (DftDone r) [] n /\
  dft_open_inst_boundary fn budget bb rest i (DftOpen (DftDone r) [] n)
Proof
  strip_tac >>
  simp[dft_open_next_def, dft_open_return_def,
       dft_open_inst_boundary_def, dft_open_run_boundary_def]
QED

(* Structural first-exit predicates for the recursion-aligned certificates.
   Classified endpoints, not these predicates, justify stack clearing. *)
Definition dft_open_fatal_def:
  dft_open_fatal r <=>
    (?e. r = Error e) \/ (?s. r = Halt s) \/ (?z s. r = Abort z s)
End

Definition dft_open_classified_exit_def:
  dft_open_classified_exit stack rr d m <=>
    ?st. d = DftOpen (DftDone rr) st m /\
      (st = stack \/ (st = [] /\ dft_open_fatal rr))
End

Definition dft_open_block_exit_def:
  dft_open_block_exit fn budget stack c <=>
    dft_open_stack_exit stack c \/
    (?t m. c = DftOpen (DftEnter fn budget t) stack m)
End

Definition dft_open_inst_exit_def:
  dft_open_inst_exit fn budget bb stack i c <=>
    dft_open_block_exit fn budget stack c \/
    (?t m. c = DftOpen (DftAt fn budget bb t) stack m /\ t.vs_inst_idx = SUC i)
End

Definition dft_open_step_segment_def:
  dft_open_step_segment a xs ctx fn budget bb inst s stack n r <=>
    ?rr m k d. n <= m /\ 0 < k /\
      dft_open_result_eq (dft_open_materialize_result xs m rr) r /\
      dft_first_hit (dft_open_next a ctx)
        (dft_open_inst_exit fn budget bb stack s.vs_inst_idx)
        (DftOpen (DftAt fn budget bb s) stack n) k d /\
      (case rr of
         OK t => d = dft_open_deliver fn budget bb inst s stack m rr
       | _ => dft_open_classified_exit stack rr d m)
End

Definition dft_open_block_segment_def:
  dft_open_block_segment a xs ctx fn budget bb s stack n r <=>
    ?rr m k d. n <= m /\ 0 < k /\
      dft_open_result_eq (dft_open_materialize_result xs m rr) r /\
      dft_first_hit (dft_open_next a ctx)
        (dft_open_block_exit fn budget stack)
        (DftOpen (DftAt fn budget bb s) stack n) k d /\
      (case rr of
         OK t => ~t.vs_halted /\ d = DftOpen (DftEnter fn budget t) stack m
       | _ => dft_open_classified_exit stack rr d m)
End

Definition dft_open_run_segment_def:
  dft_open_run_segment a xs ctx fn fuel s stack n r <=>
    ?rr m k d. n <= m /\ 0 < k /\
      dft_open_result_eq (dft_open_materialize_result xs m rr) r /\
      (!t. rr <> OK t) /\
      dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit stack)
        (DftOpen (DftEnter fn fuel s) stack n) k d /\
      dft_open_classified_exit stack rr d m
End

Theorem dft_open_inst_exit_initial:
  ~dft_open_inst_exit fn budget bb stack s.vs_inst_idx
    (DftOpen (DftAt fn budget bb s) stack n)
Proof
  simp[dft_open_inst_exit_def, dft_open_block_exit_def, dft_open_stack_exit_def]
QED

Theorem dft_open_boundary_is_exit:
  dft_open_inst_boundary fn budget bb stack i c ==>
  dft_open_inst_exit fn budget bb stack i c
Proof
  simp[dft_open_inst_boundary_def, dft_open_run_boundary_def,
       dft_open_inst_exit_def, dft_open_block_exit_def, dft_open_stack_exit_def] >>
  metis_tac[]
QED

Theorem dft_open_deliver_classified[local]:
  case rr of
    OK t => T
  | _ => dft_open_classified_exit stack rr
      (dft_open_deliver fn budget bb inst s stack m rr) m
Proof
  Cases_on `rr` >> simp[dft_open_classified_exit_def, dft_open_deliver_def]
QED

Theorem dft_open_non_invoke_forward:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = r ==>
  dft_open_step_segment a xs ctx fn budget bb inst s stack n r
Proof
  strip_tac >> drule_all dft_open_non_invoke_segment >>
  disch_then (qspecl_then [`stack`, `fn`] strip_assume_tac) >>
  `dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_exit fn budget bb stack s.vs_inst_idx)
    (DftOpen (DftAt fn budget bb s) stack n) 1 d` by
    (gvs[dft_first_hit_def] >>
     metis_tac[dft_open_boundary_is_exit, dft_open_inst_exit_initial]) >>
  simp[dft_open_step_segment_def] >> qexistsl_tac [`rr`, `m`, `1`, `d`] >>
  simp[] >> Cases_on `rr` >>
  gvs[dft_open_deliver_def, dft_open_classified_exit_def, dft_open_fatal_def]
QED

Definition dft_open_step_forward_def:
  dft_open_step_forward a xs budget ctx inst u <=>
    !s n fn bb stack.
      u = dft_open_materialize xs n s /\
      get_instruction bb s.vs_inst_idx = SOME inst ==>
      dft_open_step_segment a xs ctx fn budget bb inst s stack n
        (step_inst budget ctx inst u)
End

Definition dft_open_block_forward_def:
  dft_open_block_forward a xs budget ctx bb u <=>
    !s n fn stack.
      u = dft_open_materialize xs n s ==>
      dft_open_block_segment a xs ctx fn budget bb s stack n
        (exec_block budget ctx bb u)
End

Definition dft_open_run_forward_def:
  dft_open_run_forward a xs fuel ctx fn u <=>
    !s n stack.
      u = dft_open_materialize xs n s ==>
      dft_open_run_segment a xs ctx fn fuel s stack n
        (run_blocks fuel ctx fn u)
End

Theorem dft_open_step_forward_non_invoke:
  dft_sparse_oracle a xs /\ inst.inst_opcode <> INVOKE ==>
  dft_open_step_forward a xs budget ctx inst u
Proof
  simp[dft_open_step_forward_def] >> rpt strip_tac >>
  irule dft_open_non_invoke_forward >> simp[]
QED

Theorem dft_open_stack_inst_exit_separation:
  dft_open_stack_extends (frame::stack) c /\
  ~dft_open_stack_exit (frame::stack) c ==>
  ~dft_open_inst_exit fn budget bb stack i c
Proof
  Cases_on `c` >> rename1 `DftOpen control st n` >>
  simp[dft_open_stack_extends_def] >> strip_tac >>
  `LENGTH stack < LENGTH (prefix ++ frame::stack)` by simp[] >>
  gvs[dft_open_inst_exit_def, dft_open_block_exit_def, dft_open_stack_exit_def] >>
  strip_tac >> gvs[]
QED

Theorem dft_open_callee_inst_exit_avoidance:
  dft_open_stack_extends (frame::stack) c /\
  (!j. j < k ==> ~dft_open_stack_exit (frame::stack)
    (FUNPOW (dft_open_next a ctx) j c)) ==>
  !j. j < k ==> ~dft_open_inst_exit fn budget bb stack i
    (FUNPOW (dft_open_next a ctx) j c)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> disch_tac >>
  irule dft_open_stack_inst_exit_separation >>
  `j <= k` by decide_tac >>
  drule_all dft_open_stack_confinement >> metis_tac[]
QED

Theorem dft_open_step_error_segment[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error e)) [] n ==>
  dft_open_step_segment a xs ctx fn budget bb inst s stack n (Error e')
Proof
  strip_tac >> simp[dft_open_step_segment_def] >>
  qexistsl_tac [`Error e`, `n`, `1`, `DftOpen (DftDone (Error e)) [] n`] >>
  simp[dft_open_materialize_result_def, dft_open_classified_exit_def,
       dft_open_fatal_def] >>
  simp[dft_first_hit_def, dft_open_inst_exit_initial,
       dft_open_inst_exit_def, dft_open_block_exit_def, dft_open_stack_exit_def]
QED

Theorem dft_first_hit_change_exit[local]:
  dft_first_hit N B c k d /\
  (!j. j < k ==> ~E (FUNPOW N j c)) /\ E d ==>
  dft_first_hit N E c k d
Proof
  simp[dft_first_hit_def]
QED

Theorem dft_first_hit_change_exit_next[local]:
  dft_first_hit N B c k d /\
  (!j. j < k ==> ~E (FUNPOW N j c)) /\ ~E d /\ E (N d) ==>
  dft_first_hit N E c (k + 1) (N d)
Proof
  strip_tac >> irule dft_first_hit_prefix >> conj_tac >- simp[] >>
  qexists_tac `d` >> gvs[dft_first_hit_def, dft_first_hit_one]
QED

Theorem dft_open_call_prefix[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftEnter callee budget cs) (frame::stack) n /\
  dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit (frame::stack))
    (DftOpen (DftEnter callee budget cs) (frame::stack) n) k d ==>
  FUNPOW (dft_open_next a ctx) (1 + k)
    (DftOpen (DftAt fn budget bb s) stack n) = d /\
  (!j. j < 1 + k ==> ~dft_open_inst_exit fn budget bb stack s.vs_inst_idx
    (FUNPOW (dft_open_next a ctx) j (DftOpen (DftAt fn budget bb s) stack n)))
Proof
  strip_tac >> conj_tac
  >- (gvs[dft_first_hit_def] >> simp[Once ADD_COMM, FUNPOW_ADD]) >>
  gen_tac >> strip_tac >> Cases_on `j = 0`
  >- simp[dft_open_inst_exit_initial] >>
  `j = (j - 1) + 1 /\ j - 1 < k` by decide_tac >>
  `~dft_open_inst_exit fn budget bb stack s.vs_inst_idx
    (FUNPOW (dft_open_next a ctx) (j - 1)
      (DftOpen (DftEnter callee budget cs) (frame::stack) n))` by
    (irule dft_open_callee_inst_exit_avoidance >>
     simp[dft_open_stack_extends_def] >>
     gvs[dft_first_hit_def] >> qexists_tac `k` >> simp[] >> decide_tac) >>
  metis_tac[FUNPOW_ADD, FUNPOW_1]
QED

Theorem dft_open_result_eq_refl[simp]:
  dft_open_result_eq r r
Proof
  Cases_on `r` >> simp[]
QED

Theorem dft_open_call_fatal_segment[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftEnter callee budget cs) (frame::stack) n /\
  dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit (frame::stack))
    (DftOpen (DftEnter callee budget cs) (frame::stack) n) k d /\
  dft_open_classified_exit (frame::stack) rr d m /\
  dft_open_fatal rr /\ n <= m /\
  dft_open_result_eq (dft_open_materialize_result xs m rr) r ==>
  dft_open_step_segment a xs ctx fn budget bb inst s stack n r
Proof
  strip_tac >> drule_all dft_open_call_prefix >> strip_tac >>
  gvs[dft_open_classified_exit_def] >-
    (simp[dft_open_step_segment_def] >>
     qexistsl_tac [`rr`, `m`, `1 + k + 1`, `DftOpen (DftDone rr) [] m`] >>
     simp[] >> conj_tac
     >- (`dft_open_next a ctx (DftOpen (DftDone rr) (frame::stack) m) =
           DftOpen (DftDone rr) [] m` by
           gvs[dft_open_fatal_def, dft_open_next_def, dft_open_return_def] >>
         `~dft_open_inst_exit fn budget bb stack s.vs_inst_idx
           (DftOpen (DftDone rr) (frame::stack) m)` by
           (simp[dft_open_inst_exit_def, dft_open_block_exit_def,
                 dft_open_stack_exit_def] >>
            strip_tac >> `LENGTH stack = LENGTH (frame::stack)` by metis_tac[] >> gvs[]) >>
         simp[dft_first_hit_def] >> conj_tac
         >- (`k + 2 = SUC (k + 1)` by decide_tac >> metis_tac[FUNPOW_SUC]) >>
         conj_tac >- simp[dft_open_inst_exit_def, dft_open_block_exit_def,
                               dft_open_stack_exit_def] >>
         rpt strip_tac >> Cases_on `j < k + 1` >- metis_tac[] >>
         `j = k + 1` by decide_tac >> metis_tac[]) >>
     Cases_on `rr` >> gvs[dft_open_fatal_def, dft_open_classified_exit_def]) >>
  simp[dft_open_step_segment_def] >>
  qexistsl_tac [`rr`, `m`, `1 + k`, `DftOpen (DftDone rr) [] m`] >>
  simp[] >> conj_tac
  >- simp[dft_first_hit_def, dft_open_inst_exit_def,
          dft_open_block_exit_def, dft_open_stack_exit_def] >>
  Cases_on `rr` >> gvs[dft_open_fatal_def, dft_open_classified_exit_def]
QED

Theorem dft_first_hit_tail[local]:
  FUNPOW N k c = d /\ (!j. j < k ==> ~E (FUNPOW N j c)) /\
  ~E d /\ E (N d) ==>
  dft_first_hit N E c (SUC k) (N d)
Proof
  strip_tac >> simp[dft_first_hit_def, FUNPOW_SUC] >>
  rpt strip_tac >> Cases_on `j < k` >- metis_tac[] >>
  `j = k` by decide_tac >> gvs[]
QED

Theorem dft_open_call_tail[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftEnter callee budget cs) (frame::stack) n /\
  dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit (frame::stack))
    (DftOpen (DftEnter callee budget cs) (frame::stack) n) k d /\
  ~dft_open_inst_exit fn budget bb stack s.vs_inst_idx d /\
  dft_open_inst_exit fn budget bb stack s.vs_inst_idx (dft_open_next a ctx d) ==>
  dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_exit fn budget bb stack s.vs_inst_idx)
    (DftOpen (DftAt fn budget bb s) stack n) (SUC (1 + k))
    (dft_open_next a ctx d)
Proof
  strip_tac >> drule_all dft_open_call_prefix >> strip_tac >>
  irule dft_first_hit_tail >> simp[]
QED

Theorem dft_open_call_return_segment[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftEnter callee budget cs)
      (DftCaller fn budget bb inst s::stack) n /\
  dft_first_hit (dft_open_next a ctx)
    (dft_open_stack_exit (DftCaller fn budget bb inst s::stack))
    (DftOpen (DftEnter callee budget cs)
      (DftCaller fn budget bb inst s::stack) n) k
    (DftOpen (DftDone (IntRet ret after))
      (DftCaller fn budget bb inst s::stack) m) /\ n <= m ==>
  dft_open_step_segment a xs ctx fn budget bb inst s stack n
    (case bind_outputs inst.inst_outputs ret.iret_values
       (adopt_return_fmp ret (merge_callee_state s after)) of
       NONE => Error "invoke: return arity mismatch"
     | SOME t => OK (dft_open_materialize xs m t))
Proof
  strip_tac >>
  `~dft_open_inst_exit fn budget bb stack s.vs_inst_idx
    (DftOpen (DftDone (IntRet ret after))
      (DftCaller fn budget bb inst s::stack) m)` by
    (simp[dft_open_inst_exit_def, dft_open_block_exit_def,
          dft_open_stack_exit_def] >>
     strip_tac >> `LENGTH stack = SUC (LENGTH stack)` by metis_tac[] >> gvs[]) >>
  `dft_open_inst_exit fn budget bb stack s.vs_inst_idx
    (dft_open_next a ctx (DftOpen (DftDone (IntRet ret after))
      (DftCaller fn budget bb inst s::stack) m))` by
    metis_tac[dft_open_return_boundary, dft_open_boundary_is_exit] >>
  drule_all dft_open_call_tail >> strip_tac >>
  Cases_on `bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s after))`
  >- (simp[dft_open_step_segment_def] >>
      qexistsl_tac [`Error "invoke: return arity mismatch"`, `m`, `SUC (1+k)`,
        `DftOpen (DftDone (Error "invoke: return arity mismatch")) [] m`] >>
      gvs[dft_open_next_def, dft_open_return_def,
          dft_open_materialize_result_def, dft_open_classified_exit_def,
          dft_open_fatal_def]) >>
  simp[dft_open_step_segment_def] >>
  qexistsl_tac [`OK x`, `m`, `SUC (1+k)`,
    `dft_open_deliver fn budget bb inst s stack m (OK x)`] >>
  gvs[dft_open_next_def, dft_open_return_def, dft_open_materialize_result_def]
QED

Theorem dft_open_step_forward_invoke[local]:
  dft_sparse_oracle a xs /\
  (!pair nm ops callee args u'.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME pair /\
    pair = (nm,ops) /\ lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops u = SOME args /\ setup_callee callee args u = SOME u' ==>
    dft_open_run_forward a xs budget ctx callee u') ==>
  dft_open_step_forward a xs budget ctx inst u
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[dft_open_step_forward_def] >> rpt strip_tac >>
      Cases_on `decode_invoke inst`
      >- (simp[Once step_inst_def] >> irule dft_open_step_error_segment >>
          simp[dft_open_next_def, dft_open_invoke_def]) >>
      PairCases_on `x` >>
      Cases_on `lookup_function x0 ctx.ctx_functions`
      >- (simp[Once step_inst_def] >> irule dft_open_step_error_segment >>
          simp[dft_open_next_def, dft_open_invoke_def]) >>
      rename1 `lookup_function x0 ctx.ctx_functions = SOME callee` >>
      Cases_on `eval_operands x1 s`
      >- (simp[Once step_inst_def, dft_open_materialize_def] >>
          irule dft_open_step_error_segment >>
          simp[dft_open_next_def, dft_open_invoke_def]) >>
      rename1 `eval_operands x1 s = SOME args` >>
      Cases_on `setup_callee callee args s`
      >- (simp[Once step_inst_def, dft_open_setup_materialize,
               dft_open_materialize_def] >>
          irule dft_open_step_error_segment >>
          simp[dft_open_next_def, dft_open_invoke_def]) >>
      rename1 `setup_callee callee args s = SOME cs` >>
      `dft_open_run_forward a xs budget ctx callee
        (dft_open_materialize xs n cs)` by
        (first_x_assum irule >>
         simp[dft_open_setup_materialize, dft_open_materialize_def, gas_setup_callee] >>
         metis_tac[]) >>
      qpat_x_assum `dft_open_run_forward _ _ _ _ _ _` mp_tac >>
      simp[dft_open_run_forward_def] >>
      disch_then (qspecl_then [`cs`, `n`, `DftCaller fn budget bb inst s::stack`]
        mp_tac) >> simp[dft_open_run_segment_def] >> strip_tac >>
      `dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
        DftOpen (DftEnter callee budget cs) (DftCaller fn budget bb inst s::stack) n`
        by (irule dft_open_invoke_push >> simp[] >> metis_tac[]) >>
      `eval_operands x1 (dft_open_materialize xs n s) = SOME args` by
        simp[dft_open_materialize_def] >>
      `setup_callee callee args (dft_open_materialize xs n s) =
        SOME (dft_open_materialize xs n cs)` by simp[dft_open_setup_materialize] >>
      Cases_on `rr` >>
      Cases_on `run_blocks budget ctx callee (dft_open_materialize xs n cs)` >>
      gvs[dft_open_materialize_result_def] >>
      simp[Once step_inst_def]
      >~ [`dft_open_classified_exit _ (IntRet ret after) _ _`]
      >- (gvs[dft_open_classified_exit_def, dft_open_fatal_def] >>
          simp[dft_open_return_materialize] >>
          drule_all dft_open_call_return_segment >>
          disch_then (qspec_then `xs` mp_tac) >>
          Cases_on `bind_outputs inst.inst_outputs ret.iret_values
            (adopt_return_fmp ret (merge_callee_state s after))` >> simp[]) >>
      irule dft_open_call_fatal_segment >>
      first_assum (irule_at (Pat `dft_open_classified_exit _ _ _ _`)) >>
      simp[dft_open_fatal_def, dft_open_materialize_result_def] >>
      qexists_tac `k` >> simp[]) >>
  irule dft_open_step_forward_non_invoke >> simp[]
QED

Theorem dft_open_classified_block_exit[local]:
  dft_open_classified_exit stack rr d m ==>
  dft_open_block_exit fn budget stack d
Proof
  simp[dft_open_classified_exit_def, dft_open_block_exit_def,
       dft_open_stack_exit_def] >> metis_tac[]
QED

Theorem dft_open_step_hit_block[local]:
  dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_exit fn budget bb stack i) c k d /\
  dft_open_block_exit fn budget stack d ==>
  dft_first_hit (dft_open_next a ctx)
    (dft_open_block_exit fn budget stack) c k d
Proof
  simp[dft_first_hit_def, dft_open_inst_exit_def] >> metis_tac[]
QED

Theorem dft_open_non_ok_step_block[local]:
  dft_open_step_segment a xs ctx fn budget bb inst s stack n r /\
  (!t. r <> OK t) ==>
  dft_open_block_segment a xs ctx fn budget bb s stack n r
Proof
  simp[dft_open_step_segment_def] >> strip_tac >>
  `!t. rr <> OK t` by
    (Cases_on `rr` >> Cases_on `r` >>
     gvs[dft_open_materialize_result_def]) >>
  `dft_open_classified_exit stack rr d m` by (Cases_on `rr` >> gvs[]) >>
  simp[dft_open_block_segment_def] >>
  qexistsl_tac [`rr`, `m`, `k`, `d`] >> simp[] >> conj_tac
  >- (irule dft_open_step_hit_block >> simp[] >>
      metis_tac[dft_open_classified_block_exit]) >>
  Cases_on `rr` >> gvs[]
QED

Theorem dft_open_terminator_step_block[local]:
  dft_open_step_segment a xs ctx fn budget bb inst s stack n (OK after) /\
  is_terminator inst.inst_opcode ==>
  dft_open_block_segment a xs ctx fn budget bb s stack n
    (if after.vs_halted then Halt after else OK after)
Proof
  simp[dft_open_step_segment_def] >> strip_tac >>
  Cases_on `rr` >> gvs[dft_open_materialize_result_def] >>
  rename1 `OK (dft_open_materialize xs m t)` >>
  Cases_on `t.vs_halted` >>
  gvs[dft_open_deliver_def, dft_open_continue_def,
      dft_open_materialize_def] >>
  simp[dft_open_block_segment_def]
  >- (qexistsl_tac [`Halt t`, `m`, `k`,
        `DftOpen (DftDone (Halt t)) stack m`] >>
      simp[dft_open_materialize_result_def, dft_open_materialize_def,
           dft_open_classified_exit_def] >>
      irule dft_open_step_hit_block >>
      simp[dft_open_block_exit_def, dft_open_stack_exit_def] >>
      qexistsl_tac [`bb`, `s.vs_inst_idx`] >> simp[]) >>
  qexistsl_tac [`OK t`, `m`, `k`, `DftOpen (DftEnter fn budget t) stack m`] >>
  simp[dft_open_materialize_result_def, dft_open_materialize_def] >>
  irule dft_open_step_hit_block >> simp[dft_open_block_exit_def] >>
  qexistsl_tac [`bb`, `s.vs_inst_idx`] >> simp[]
QED

Theorem dft_open_step_block_prefix[local]:
  dft_first_hit (dft_open_next a ctx)
    (dft_open_inst_exit fn budget bb stack i) c k d ==>
  FUNPOW (dft_open_next a ctx) k c = d /\
  (!j. j < k ==> ~dft_open_block_exit fn budget stack
    (FUNPOW (dft_open_next a ctx) j c))
Proof
  simp[dft_first_hit_def, dft_open_inst_exit_def] >> metis_tac[]
QED

Theorem dft_open_sequential_step_block[local]:
  dft_open_step_segment a xs ctx fn budget bb inst s stack n (OK after) /\
  ~is_terminator inst.inst_opcode /\
  dft_open_block_forward a xs budget ctx bb
    (after with vs_inst_idx := SUC s.vs_inst_idx) ==>
  dft_open_block_segment a xs ctx fn budget bb s stack n
    (exec_block budget ctx bb (after with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  simp[dft_open_step_segment_def] >> strip_tac >>
  Cases_on `rr` >> gvs[dft_open_materialize_result_def] >>
  rename1 `dft_open_deliver fn budget bb inst s stack m (OK t)` >>
  gvs[dft_open_deliver_def, dft_open_continue_def] >>
  drule_all dft_open_step_block_prefix >> strip_tac >>
  qpat_x_assum `dft_open_block_forward _ _ _ _ _ _` mp_tac >>
  simp[dft_open_block_forward_def] >>
  disch_then (qspecl_then [`t with vs_inst_idx := SUC s.vs_inst_idx`,
    `m`, `fn`, `stack`] mp_tac) >>
  simp[dft_open_materialize_def, dft_open_block_segment_def] >> strip_tac >>
  qexistsl_tac [`rr`, `m'`, `k + k'`, `d`] >> simp[] >>
  irule dft_first_hit_prefix >> conj_tac >- simp[] >>
  qexists_tac `DftOpen (DftAt fn budget bb
    (t with vs_inst_idx := SUC s.vs_inst_idx)) stack m` >> simp[]
QED

Theorem dft_open_block_error_segment[local]:
  dft_open_next a ctx (DftOpen (DftAt fn budget bb s) stack n) =
    DftOpen (DftDone (Error e)) [] n ==>
  dft_open_block_segment a xs ctx fn budget bb s stack n (Error e')
Proof
  strip_tac >> simp[dft_open_block_segment_def] >>
  qexistsl_tac [`Error e`, `n`, `1`, `DftOpen (DftDone (Error e)) [] n`] >>
  simp[dft_open_materialize_result_def, dft_open_classified_exit_def,
       dft_open_fatal_def, dft_first_hit_def,
       dft_open_block_exit_def, dft_open_stack_exit_def]
QED

Theorem dft_open_materialize_idx[simp]:
  (dft_open_materialize xs n s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[dft_open_materialize_def]
QED

Theorem dft_open_block_forward_step[local]:
  (!inst after. get_instruction bb u.vs_inst_idx = SOME inst /\
    step_inst budget ctx inst u = OK after /\ ~is_terminator inst.inst_opcode ==>
    dft_open_block_forward a xs budget ctx bb
      (after with vs_inst_idx := SUC u.vs_inst_idx)) /\
  (!inst. get_instruction bb u.vs_inst_idx = SOME inst ==>
    dft_open_step_forward a xs budget ctx inst u) ==>
  dft_open_block_forward a xs budget ctx bb u
Proof
  strip_tac >> simp[dft_open_block_forward_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (simp[Once exec_block_def] >>
      irule dft_open_block_error_segment >> simp[dft_open_next_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `dft_open_step_forward a xs budget ctx inst (dft_open_materialize xs n s)` by
    (first_x_assum irule >> simp[]) >>
  `dft_open_step_segment a xs ctx fn budget bb inst s stack n
    (step_inst budget ctx inst (dft_open_materialize xs n s))` by
    (gvs[dft_open_step_forward_def]) >>
  Cases_on `?after. step_inst budget ctx inst (dft_open_materialize xs n s) = OK after`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (simp[Once exec_block_def] >>
          irule dft_open_terminator_step_block >> simp[] >> metis_tac[]) >>
      simp[Once exec_block_def] >>
      irule dft_open_sequential_step_block >> simp[] >>
      qexists_tac `inst` >> simp[]) >>
  `exec_block budget ctx bb (dft_open_materialize xs n s) =
    step_inst budget ctx inst (dft_open_materialize xs n s)` by
    (simp[Once exec_block_def] >>
     Cases_on `step_inst budget ctx inst (dft_open_materialize xs n s)` >> gvs[]) >>
  simp[] >> irule dft_open_non_ok_step_block >> simp[] >> metis_tac[]
QED

Theorem dft_first_hit_prefix_step[local]:
  N c = b /\ ~E c /\ dft_first_hit N B b k d /\
  (!x. E x ==> B x) ==>
  FUNPOW N (SUC k) c = d /\
  (!j. j < SUC k ==> ~E (FUNPOW N j c))
Proof
  simp[dft_first_hit_def] >> strip_tac >> conj_tac
  >- simp[FUNPOW] >> rpt strip_tac >> Cases_on `j` >- gvs[] >>
  gvs[FUNPOW] >> metis_tac[]
QED

Theorem dft_open_block_run_prefix[local]:
  dft_open_next a ctx (DftOpen (DftEnter fn fuel s) stack n) =
    DftOpen (DftAt fn budget bb sp) stack n /\
  dft_first_hit (dft_open_next a ctx) (dft_open_block_exit fn budget stack)
    (DftOpen (DftAt fn budget bb sp) stack n) k d ==>
  FUNPOW (dft_open_next a ctx) (SUC k)
    (DftOpen (DftEnter fn fuel s) stack n) = d /\
  (!j. j < SUC k ==> ~dft_open_stack_exit stack
    (FUNPOW (dft_open_next a ctx) j (DftOpen (DftEnter fn fuel s) stack n)))
Proof
  strip_tac >> irule dft_first_hit_prefix_step >>
  simp[dft_open_stack_exit_def] >>
  qexists_tac `dft_open_block_exit fn budget stack` >>
  simp[dft_open_block_exit_def, dft_open_stack_exit_def] >> metis_tac[]
QED

Theorem dft_open_non_ok_block_run[local]:
  dft_open_next a ctx (DftOpen (DftEnter fn fuel s) stack n) =
    DftOpen (DftAt fn budget bb sp) stack n /\
  dft_open_block_segment a xs ctx fn budget bb sp stack n r /\
  (!t. r <> OK t) ==>
  dft_open_run_segment a xs ctx fn fuel s stack n r
Proof
  simp[dft_open_block_segment_def] >> strip_tac >>
  `!t. rr <> OK t` by
    (Cases_on `rr` >> Cases_on `r` >> gvs[dft_open_materialize_result_def]) >>
  `dft_open_classified_exit stack rr d m` by (Cases_on `rr` >> gvs[]) >>
  drule_all dft_open_block_run_prefix >> strip_tac >>
  simp[dft_open_run_segment_def] >>
  qexistsl_tac [`rr`, `m`, `SUC k`, `d`] >> simp[dft_first_hit_def] >>
  gvs[dft_open_classified_exit_def, dft_open_stack_exit_def] >> metis_tac[]
QED

Theorem dft_open_ok_block_run[local]:
  dft_open_next a ctx (DftOpen (DftEnter fn fuel s) stack n) =
    DftOpen (DftAt fn budget bb sp) stack n /\
  dft_open_block_segment a xs ctx fn budget bb sp stack n (OK after) /\
  dft_open_run_forward a xs budget ctx fn after ==>
  dft_open_run_segment a xs ctx fn fuel s stack n
    (run_blocks budget ctx fn after)
Proof
  simp[dft_open_block_segment_def] >> strip_tac >>
  Cases_on `rr` >> gvs[dft_open_materialize_result_def] >>
  rename1 `DftOpen (DftEnter fn budget t) stack m` >>
  drule_all dft_open_block_run_prefix >> strip_tac >>
  qpat_x_assum `dft_open_run_forward _ _ _ _ _ _` mp_tac >>
  simp[dft_open_run_forward_def] >>
  disch_then (qspecl_then [`t`, `m`, `stack`] mp_tac) >>
  simp[dft_open_run_segment_def] >> strip_tac >>
  qexistsl_tac [`rr`, `m'`, `SUC k + k'`, `d`] >> simp[] >>
  drule_all dft_first_hit_prefix >> simp[]
QED

Theorem dft_open_run_error_segment[local]:
  dft_open_next a ctx (DftOpen (DftEnter fn fuel s) stack n) =
    DftOpen (DftDone (Error e)) st n /\ (st = stack \/ st = []) ==>
  dft_open_run_segment a xs ctx fn fuel s stack n (Error e')
Proof
  strip_tac >> simp[dft_open_run_segment_def] >>
  qexistsl_tac [`Error e`, `n`, `1`, `DftOpen (DftDone (Error e)) st n`] >>
  simp[dft_open_materialize_result_def, dft_open_classified_exit_def,
       dft_open_fatal_def, dft_first_hit_def, dft_open_stack_exit_def]
QED

Theorem dft_open_materialize_fields[simp]:
  (dft_open_materialize xs n s).vs_current_bb = s.vs_current_bb /\
  (dft_open_materialize xs n s).vs_halted = s.vs_halted /\
  (dft_open_materialize xs n s with vs_inst_idx := i) =
    dft_open_materialize xs n (s with vs_inst_idx := i)
Proof
  simp[dft_open_materialize_def]
QED

Theorem dft_open_run_forward_step[local]:
  (!budget bb sp after.
    fuel = SUC budget /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis u bb.bb_instructions = OK sp /\
    exec_block budget ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK after /\
    ~after.vs_halted ==> dft_open_run_forward a xs budget ctx fn after) /\
  (!budget bb sp.
    fuel = SUC budget /\ lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis u bb.bb_instructions = OK sp ==>
    dft_open_block_forward a xs budget ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) ==>
  dft_open_run_forward a xs fuel ctx fn u
Proof
  strip_tac >> simp[dft_open_run_forward_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `fuel`
  >- (simp[Once run_blocks_def] >> irule dft_open_run_error_segment >>
      simp[dft_open_next_def]) >>
  rename1 `SUC budget` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (simp[Once run_blocks_def] >> irule dft_open_run_error_segment >>
      simp[dft_open_next_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  reverse (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs)
  >- (mp_tac (Q.INST [`insts` |-> `bb.bb_instructions`] dft_open_phis_materialize) >>
      simp[dft_open_materialize_result_def] >> strip_tac >>
      simp[Once run_blocks_def] >> irule dft_open_run_error_segment >>
      simp[dft_open_next_def]) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `eval_phis (dft_open_materialize xs n s) bb.bb_instructions =
    OK (dft_open_materialize xs n sp)` by
    (mp_tac (Q.INST [`insts` |-> `bb.bb_instructions`] dft_open_phis_materialize) >>
     simp[dft_open_materialize_result_def]) >>
  `dft_open_block_forward a xs budget ctx bb
    (dft_open_materialize xs n
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    gvs[] >>
  qpat_x_assum `dft_open_block_forward _ _ _ _ _ _` mp_tac >>
  simp[dft_open_block_forward_def] >>
  disch_then (qspecl_then [`sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `n`, `fn`, `stack`] mp_tac) >> simp[] >> strip_tac >>
  `dft_open_next a ctx (DftOpen (DftEnter fn (SUC budget) s) stack n) =
    DftOpen (DftAt fn budget bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) stack n` by
      (irule dft_open_block_entry >> simp[]) >>
  Cases_on `?after. exec_block budget ctx bb
    (dft_open_materialize xs n
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) = OK after`
  >- (pop_assum strip_assume_tac >>
      `~after.vs_halted` by metis_tac[dft_exec_block_ok_not_halted] >>
      gvs[] >> simp[Once run_blocks_def] >>
      irule dft_open_ok_block_run >>
      first_assum (irule_at (Pat `dft_open_block_segment _ _ _ _ _ _ _ _ _ _`)) >>
      simp[]) >>
  `run_blocks (SUC budget) ctx fn (dft_open_materialize xs n s) =
    exec_block budget ctx bb (dft_open_materialize xs n
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (simp[Once run_blocks_def] >>
     Cases_on `exec_block budget ctx bb (dft_open_materialize xs n
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions))` >> gvs[]) >>
  simp[] >> irule dft_open_non_ok_block_run >>
  first_assum (irule_at (Pat `dft_open_block_segment _ _ _ _ _ _ _ _ _ _`)) >>
  metis_tac[]
QED

Theorem dft_open_forward_segments:
  dft_sparse_oracle a xs ==>
  (!budget ctx inst u. dft_open_step_forward a xs budget ctx inst u) /\
  (!budget ctx bb u. dft_open_block_forward a xs budget ctx bb u) /\
  (!fuel ctx fn u. dft_open_run_forward a xs fuel ctx fn u)
Proof
  strip_tac >> ho_match_mp_tac run_defs_ind >> conj_tac
  >- (rpt strip_tac >> irule dft_open_step_forward_invoke >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule dft_open_block_forward_step >> simp[]) >>
  rpt strip_tac >> irule dft_open_run_forward_step >> simp[]
QED

Theorem dft_open_step_forward_segment:
  dft_sparse_oracle a xs /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst budget ctx inst (dft_open_materialize xs n s) = r ==>
  dft_open_step_segment a xs ctx fn budget bb inst s stack n r
Proof
  strip_tac >>
  drule (cj 1 dft_open_forward_segments) >>
  simp[dft_open_step_forward_def] >> metis_tac[]
QED

Theorem dft_open_block_forward_segment:
  dft_sparse_oracle a xs /\
  exec_block budget ctx bb (dft_open_materialize xs n s) = r ==>
  dft_open_block_segment a xs ctx fn budget bb s stack n r
Proof
  strip_tac >>
  drule (cj 2 dft_open_forward_segments) >>
  simp[dft_open_block_forward_def] >> metis_tac[]
QED

Theorem dft_open_run_forward_segment:
  dft_sparse_oracle a xs /\
  run_blocks fuel ctx fn (dft_open_materialize xs n s) = r ==>
  dft_open_run_segment a xs ctx fn fuel s stack n r
Proof
  strip_tac >>
  drule (cj 3 dft_open_forward_segments) >>
  simp[dft_open_run_forward_def] >> metis_tac[]
QED

Theorem dft_open_result_eq_sym[local]:
  dft_open_result_eq x y <=> dft_open_result_eq y x
Proof
  Cases_on `x` >> Cases_on `y` >>
  simp[dft_open_result_eq_def, lift_result_def, EQ_SYM_EQ]
QED

Theorem dft_open_result_eq_trans[local]:
  dft_open_result_eq x y /\ dft_open_result_eq y z ==>
  dft_open_result_eq x z
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >>
  simp[dft_open_result_eq_def, lift_result_def]
QED

Theorem dft_open_run_segment_unique[local]:
  dft_open_run_segment a xs ctx fn fuel s stack n r /\
  dft_open_run_segment a xs ctx fn fuel s stack n r' ==>
  dft_open_result_eq r r'
Proof
  pure_rewrite_tac[dft_open_run_segment_def] >> rpt strip_tac >>
  `d = d'` by metis_tac[dft_first_hit_unique] >>
  gvs[dft_open_classified_exit_def] >>
  metis_tac[dft_open_result_eq_sym, dft_open_result_eq_trans]
QED

Theorem dft_open_run_segment_cong[local]:
  dft_open_run_segment a xs ctx fn fuel s stack n r /\
  dft_open_result_eq r r' ==>
  dft_open_run_segment a xs ctx fn fuel s stack n r'
Proof
  pure_rewrite_tac[dft_open_run_segment_def] >> rpt strip_tac >>
  qexistsl_tac [`rr`, `m`, `k`, `d`] >>
  simp[] >> metis_tac[dft_open_result_eq_trans]
QED

Theorem dft_open_run_segment_reflect:
  dft_sparse_oracle a xs /\
  dft_open_run_segment a xs ctx fn fuel s stack n r ==>
  dft_open_result_eq
    (run_blocks fuel ctx fn (dft_open_materialize xs n s)) r
Proof
  strip_tac >>
  `dft_open_run_segment a xs ctx fn fuel s stack n
     (run_blocks fuel ctx fn (dft_open_materialize xs n s))`
    by (irule dft_open_run_forward_segment >> simp[]) >>
  metis_tac[dft_open_run_segment_unique]
QED

Theorem dft_open_run_segment_iff:
  dft_sparse_oracle a xs ==>
  (dft_open_run_segment a xs ctx fn fuel s stack n r <=>
   dft_open_result_eq
     (run_blocks fuel ctx fn (dft_open_materialize xs n s)) r)
Proof
  strip_tac >> eq_tac
  >- (metis_tac[dft_open_run_segment_reflect]) >>
  strip_tac >> irule dft_open_run_segment_cong >>
  qexists_tac `run_blocks fuel ctx fn (dft_open_materialize xs n s)` >>
  simp[] >> irule dft_open_run_forward_segment >> simp[]
QED
