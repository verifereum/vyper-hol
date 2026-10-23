(* CREATE's shared oracle boundary.  This relates interfaces, not arbitrary
   concrete EVM executions or arbitrary expression compilation. *)
Theory createRequestCorrespondence
Ancestors
  createOracleExecution vyperCallOutcome callTrace venomCallOracleDefs
  venomState vyperState extCallOracle

Definition create_world_rel_def:
  create_world_rel st s <=>
    st.accounts = s.vs_accounts /\ st.tStorage = s.vs_transient /\
    st.logs = s.vs_logs /\ st.pending_deletions = s.vs_toDelete /\
    st.outcomes = SOME s.vs_outcomes /\ st.requests = s.vs_requests
End

Theorem source_venom_create_request:
  st.accounts = s.vs_accounts /\ st.tStorage = s.vs_transient /\
  initcode = read_memory (w2n off) (w2n sz) s ==>
  create_outcome_request
    (case salt of NONE => CreateCall | SOME x => Create2Call x)
    (w2n value) initcode st = venom_create_request s value off sz salt
Proof
  simp[create_outcome_request_def, venom_create_request_def]
QED

(* A head is consumed even when the source runtime-account guard rejects it.
   The guard is NOT an assumption that the EVM creation succeeded. *)
Theorem source_venom_create_take:
  create_world_rel st s /\ s.vs_outcomes = outcome::rest /\
  initcode = read_memory (w2n off) (w2n sz) s ==>
  take_create_outcome
    (case salt of NONE => CreateCall | SOME x => Create2Call x)
    (w2n value) initcode st =
    (if accounts_runtime_well_typed outcome.co_accounts
     then INL (venom_create_request s value off sz salt, outcome)
     else INR (Error (RuntimeError "create outcome accounts")),
     st with <|outcomes := SOME rest;
       requests := st.requests ++ [venom_create_request s value off sz salt]|>)
Proof
  strip_tac >> fs[create_world_rel_def] >>
  simp[take_create_outcome_def, take_outcome_def, record_request_def] >>
  Cases_on `accounts_runtime_well_typed outcome.co_accounts` >>
  simp[create_outcome_request_def, venom_create_request_def]
QED

Theorem source_venom_create_adopt:
  create_world_rel st s /\ s.vs_outcomes = outcome::rest /\
  initcode = read_memory (w2n off) (w2n sz) s ==>
  create_world_rel
    (SND (adopt_call_outcome
      (create_outcome_request
        (case salt of NONE => CreateCall | SOME x => Create2Call x)
        (w2n value) initcode st) outcome
      (st with <|outcomes := SOME rest;
        requests := st.requests ++ [venom_create_request s value off sz salt]|>)))
    (SND (consume_create_outcome (venom_create_request s value off sz salt) s))
Proof
  strip_tac >> drule consume_create_head >> disch_then assume_tac >>
  Cases_on `salt` >>
  simp[adopt_create_outcome_equation, create_world_rel_def] >>
  gvs[create_world_rel_def]
QED

(* The returned address and exact failure bytes are independent of the
   runtime-account guard.  Source clients apply their guard before adoption
   and their revert-on-failure policy after it. *)
Theorem source_venom_create_result:
  s.vs_outcomes = outcome::rest ==>
  FST (consume_create_outcome (venom_create_request s value off sz salt) s) =
    (if outcome.co_success then w2w outcome.co_created else 0w) /\
  (SND (consume_create_outcome (venom_create_request s value off sz salt) s)).vs_returndata =
    outcome.co_returnData
Proof
  strip_tac >> drule consume_create_head >> simp[]
QED
Theorem create_read_memory_padding:
  read_memory off sz s = vfmTypes$take_pad_0 sz (DROP off s.vs_memory)
Proof
  simp[read_memory_def, vfmTypesTheory.take_pad_0_def,
       listTheory.PAD_RIGHT, rich_listTheory.TAKE_APPEND,
       rich_listTheory.REPLICATE_GENLIST, listTheory.TAKE_GENLIST] >>
  Cases_on `sz <= LENGTH (DROP off s.vs_memory)`
  >- (gvs[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP] >>
      `sz - (LENGTH s.vs_memory - off) = 0` by decide_tac >> simp[]) >>
  gvs[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP] >>
  AP_TERM_TAC >> simp[arithmeticTheory.MIN_DEF]
QED

(* Actual frame requests agree with Venom's memory-slice boundary.  These
   hypotheses relate the operand values and live world, not execution success. *)
Theorem venom_observed_create_request:
  (FST (HD es.contexts)).stack = value::off::sz::tail /\
  next_opcode (FST (HD es.contexts)) = SOME Create /\
  (FST (HD es.contexts)).memory = s.vs_memory /\
  es.rollback.accounts = s.vs_accounts /\
  es.rollback.tStorage = s.vs_transient ==>
  request_of es = venom_create_request s value off sz NONE
Proof
  strip_tac >>
  simp[request_of_def, venom_create_request_def,
       create_read_memory_padding, vfmTypesTheory.LENGTH_take_pad_0]
QED

Theorem venom_observed_create2_request:
  (FST (HD es.contexts)).stack = value::off::sz::salt::tail /\
  next_opcode (FST (HD es.contexts)) = SOME Create2 /\
  (FST (HD es.contexts)).memory = s.vs_memory /\
  es.rollback.accounts = s.vs_accounts /\
  es.rollback.tStorage = s.vs_transient ==>
  request_of es = venom_create_request s value off sz (SOME salt)
Proof
  strip_tac >>
  simp[request_of_def, venom_create_request_def,
       create_read_memory_padding, vfmTypesTheory.LENGTH_take_pad_0]
QED


Theorem source_observed_create_request:
  create_world_rel st s /\
  initcode = read_memory (w2n off) (w2n sz) s /\
  (FST (HD es.contexts)).stack = value::off::sz::
    (case salt of NONE => tail | SOME x => x::tail) /\
  next_opcode (FST (HD es.contexts)) =
    SOME (case salt of NONE => Create | SOME x => Create2) /\
  (FST (HD es.contexts)).memory = s.vs_memory /\
  es.rollback.accounts = s.vs_accounts /\
  es.rollback.tStorage = s.vs_transient ==>
  request_of es = create_outcome_request
    (case salt of NONE => CreateCall | SOME x => Create2Call x)
    (w2n value) initcode st
Proof
  strip_tac >>
  `create_outcome_request
     (case salt of NONE => CreateCall | SOME x => Create2Call x)
     (w2n value) initcode st = venom_create_request s value off sz salt` by
    (irule source_venom_create_request >> fs[create_world_rel_def]) >>
  Cases_on `salt` >> gvs[] >>
  metis_tac[venom_observed_create_request, venom_observed_create2_request]
QED

(* This packages the source guard, shared adoption and returned machine word.
   A rejected account snapshot has still consumed precisely the head entry;
   only a guard-passing source state is permitted to adopt it. *)
Theorem source_venom_create_boundary:
  create_world_rel st s /\ s.vs_outcomes = outcome::rest /\
  initcode = read_memory (w2n off) (w2n sz) s /\
  accounts_runtime_well_typed outcome.co_accounts ==>
  let rq = venom_create_request s value off sz salt;
      st1 = st with <|outcomes := SOME rest; requests := st.requests ++ [rq]|>;
      source_post = SND (adopt_call_outcome rq outcome st1);
      machine_post = SND (consume_create_outcome rq s)
  in take_create_outcome
       (case salt of NONE => CreateCall | SOME x => Create2Call x)
       (w2n value) initcode st = (INL (rq,outcome),st1) /\
     create_world_rel source_post machine_post /\
     FST (consume_create_outcome rq s) =
       (if outcome.co_success then w2w outcome.co_created else 0w) /\
     machine_post.vs_returndata = outcome.co_returnData
Proof
  strip_tac >>
  `create_outcome_request
     (case salt of NONE => CreateCall | SOME x => Create2Call x)
     (w2n value) initcode st = venom_create_request s value off sz salt` by
    (irule source_venom_create_request >> fs[create_world_rel_def]) >>
  drule_all source_venom_create_take >> disch_then assume_tac >>
  drule_all source_venom_create_adopt >> disch_then assume_tac >>
  drule source_venom_create_result >> disch_then assume_tac >>
  pure_rewrite_tac[LET_THM] >> metis_tac[]
QED

(* In particular, pre-entry failures are ordinary failed outcomes, not empty
   oracles.  The adopted account snapshot includes the creator nonce when the
   observer recorded it; logs and deletion queues are not adopted on failure. *)
Theorem observed_failed_create_adoption:
  kind <> MessageCall /\
  HD (FST (HD post.contexts)).stack = 0w ==>
  let rq = create_outcome_request kind value initcode st;
      outcome = outcome_of kind post n;
      st' = SND (adopt_call_outcome rq outcome st)
  in st'.accounts = post.rollback.accounts /\
     st'.tStorage = post.rollback.tStorage /\
     st'.logs = st.logs /\ st'.pending_deletions = st.pending_deletions /\
     outcome.co_returnData = (FST (HD post.contexts)).returnData /\
     ~outcome.co_success
Proof
  strip_tac >> simp[adopt_create_outcome_equation, outcome_of_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles andalso null axioms
     then () else raise Fail ("Incomplete CREATE correspondence: " ^ name)
  end) (DB.thms "createRequestCorrespondence");
