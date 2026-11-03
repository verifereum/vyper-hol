Theory dftOpenAdequacy
Ancestors
  dftOpenMachine gasOracleReplay venomExecSemantics venomInst stateEquiv
  dftSparseOracle list rich_list

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
