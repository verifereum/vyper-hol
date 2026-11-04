(* Accounting probes and a proposed consumer contract.  No class transport
   theorem is asserted here.  In particular clock equality is NOT a clause. *)
Theory dftTransportAccounting
Ancestors
  dftMixedCrossing dftPendingSuspension dftMixedResidualProbe
  dftOccurrenceTerminal dftOccurrenceFreshness dftOccurrenceReplay
  dftOccurrenceMachine dftOpenMachine dftOpenErase dftOpenAdequacy
  venomExecSemantics venomInst venomState unitMemInv list arithmetic

Definition dft_transport_terminal_def:
  dft_transport_terminal R w CL CR l r <=>
    !j rr n. ((?s. rr = Halt s) \/ (?a s. rr = Abort a s)) /\
      (FUNPOW (dft_occ_oracle_next w CL) j l).dft_occ_core =
        DftOpen (DftDone rr) [] n ==>
      ?k rr' m. R rr rr' /\
        ((?s. rr' = Halt s) \/ (?a s. rr' = Abort a s)) /\
        (FUNPOW (dft_occ_oracle_next w CR) k r).dft_occ_core =
          DftOpen (DftDone rr') [] m
End

Definition dft_transport_observe_def:
  dft_transport_observe FR w CL CR l r <=>
    !j fnR instR sR.
      dft_open_observe fnR instR sR
        (FUNPOW (dft_occ_oracle_next w CR) j r).dft_occ_core /\
      inst_mem_ranges instR sR <> [] ==>
      ?k fnL instL sL. FR fnL fnR /\
        dft_open_observe fnL instL sL
          (FUNPOW (dft_occ_oracle_next w CL) k l).dft_occ_core /\
        sL.vs_memory = sR.vs_memory /\ sL.vs_alloca_next = sR.vs_alloca_next /\
        inst_mem_ranges instL sL = inst_mem_ranges instR sR
End

(* Nonzero source reads must have a target occurrence with the SAME address.
   Extra source reads absent from the target are allowed, but receive zero.
   Event uniqueness is a separate unary invariant, not an injectivity guess. *)
Definition dft_transport_read_support_def:
  dft_transport_read_support w CL CR l r <=>
    !j inst addr. dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w CL) j l) /\ w addr <> 0w ==>
      ?k inst'. dft_occ_gas_event inst' addr
        (FUNPOW (dft_occ_oracle_next w CR) k r)
End

(* Replay/adequacy is unary and conditional on numeric compatibility.  This
   universal-prefix clause fixes ONE numeric oracle before ALL fuel queries.
   It does not identify the two native fuels or instruction-step counts. *)
Definition dft_transport_replay_def:
  dft_transport_replay w a C c <=>
    !j. dft_occ_prefix_compatible w a C c j
End

Definition dft_fixed_oracle_transport_def:
  dft_fixed_oracle_transport R FR w aL aR CL CR l r <=>
    dft_transport_terminal R w CL CR l r /\
    dft_transport_observe FR w CL CR l r /\
    dft_transport_read_support w CL CR l r /\
    dft_transport_replay w aL CL l /\ dft_transport_replay w aR CR r
End

(* Concrete stopping instructions with symbolic surrounding states. *)
Theorem dft_stopping_clock_probe:
  let gas = mk_inst 0 GAS [] ["g"];
      stop = mk_inst 1 ASSERT [Lit 0w] [];
      s0 = s with vs_inst_idx := 0;
      bL = bb with bb_instructions := [gas;stop];
      bR = bb with bb_instructions := [stop;gas];
      l = dft_occ_init (DftOpen (DftAt fn 0 bL s0) [] n);
      r = dft_occ_init (DftOpen (DftAt fn 0 bR s0) [] n) in
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = SUC n /\
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 1 r) = n
Proof
  EVAL_TAC
QED

(* The callee loops: the saved caller's pending ASSIGN is not a reason to
   demand that a return be reached.  Two versus one instruction steps do
   not consume different block budgets. *)
Definition dft_account_call_def:
  dft_account_call = mk_inst 1 INVOKE [Label "callee"] []
End
Definition dft_account_bb_def:
  dft_account_bb left = <|bb_label := "entry"; bb_instructions :=
    if left then [mk_inst 0 ASSIGN [Lit 7w] ["x"]; dft_account_call]
    else [dft_account_call; mk_inst 0 ASSIGN [Lit 7w] ["x"]]|>
End
Definition dft_account_fn_def:
  dft_account_fn left = mk_raw_function "main" [dft_account_bb left]
End
Definition dft_account_callee_def:
  dft_account_callee = mk_raw_function "callee"
    [<|bb_label := "loop"; bb_instructions :=
       [mk_inst 2 JMP [Label "loop"] []]|>]
End
Definition dft_account_ctx_def:
  dft_account_ctx = mk_venom_context [dft_account_callee] (SOME "main")
End
Definition dft_account_start_def:
  dft_account_start left = dft_occ_init
    (DftOpen (DftAt (dft_account_fn left) 0 (dft_account_bb left)
      (init_venom_state "entry")) [] 0)
End

Theorem dft_assign_invoke_suspended_probe:
  let l = FUNPOW (dft_occ_oracle_next w dft_account_ctx) 2 (dft_account_start T);
      r = FUNPOW (dft_occ_oracle_next w dft_account_ctx) 1 (dft_account_start F) in
  ?ctl sL sR.
    l.dft_occ_core = DftOpen ctl
      [DftCaller (dft_account_fn T) 0 (dft_account_bb T) dft_account_call sL] 0 /\
    r.dft_occ_core = DftOpen ctl
      [DftCaller (dft_account_fn F) 0 (dft_account_bb F) dft_account_call sR] 0 /\
    lookup_var "x" sL = SOME 7w /\ lookup_var "x" sR = NONE /\
    l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* A unary all-prefix replay contract is sufficient for existential native
   fuel adequacy.  There is intentionally no equality with source fuel. *)
Theorem dft_transport_replay_native:
  dft_transport_replay w a ctx (dft_occ_start entry lbl vs0) /\
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  ((?t. rr = Halt t) \/ (?z t. rr = Abort z t)) /\
  (FUNPOW (dft_occ_oracle_next w ctx) j
    (dft_occ_start entry lbl vs0)).dft_occ_core = DftOpen (DftDone rr) [] n ==>
  ?fuel. run_context fuel ctx vs0 =
    dft_open_materialize_result vs0.vs_gas_readings n rr
Proof
  simp[dft_transport_replay_def] >> rpt strip_tac >>
  irule dft_occ_terminal_realize >> metis_tac[]
QED

(* Accounting inventory for the orbit consumer (not class theorems).

   terminal:
     Ordinary: dft_original_ordinary_root_transport supplies conditional
     terminal transport through ordinary orbits.
     GAS/GAS: dft_gas_edit_rel_terminal plus init_iterate supplies the
     same result and count at corresponding prefixes.
     GAS/INVOKE: dft_mixed_source_terminal / target_terminal supplies the
     same result at existential prefixes, hiding the two final counts.
     GAS/ordinary and ordinary/INVOKE: dftMixedCrossing gives local squares,
     stopping, restore and observation boundaries, not whole-run transport.
     Their orbit/trace lifts remain unproved.

   backward nonempty-memory observations:
     Ordinary: dft_original_orbit_observe.
     GAS/GAS: dft_gas_edit_rel_observe.
     GAS/INVOKE: dftOccurrenceCallObserve's trace observation boundary.
     Mixed local evidence: dft_gas_ordinary_observation_pair and
     dft_invoke_partner_no_observations; dft_pending_suspended_observe
     covers arbitrary finite hidden-caller prefixes.  These still need
     the mixed orbit consumers, not an assumption of eventual return.

   address and nonzero read support:
     dft_occ_init_gas_event_unique is unary uniqueness, NOT cross-schedule
     support. dft_pending_suspended_address identifies active addresses
     while the caller is hidden.  A successful paired GAS uses its own
     instruction id, path and visit, not its current numeric read ordinal.
     Each class still needs an event-matching extension over its trace
     relation (including the synchronized parts), followed by composition.
     The GAS/ASSERT probe forbids obtaining this from final count equality.
     Unmatched source reads before an abort/divergent call must be assigned
     zero by the global target-support oracle, not matched to future reads
     that the target never makes.  No class support theorem is asserted.

   replay and native fuel:
     dft_transport_replay_native consumes all-prefix numeric compatibility
     and sparse realization for ONE fixed list. dft_occ_terminal_extract
     supplies the reverse native-to-occurrence direction; both use unary
     adequacy, not equality of source and target instruction-step counts.
     dftOccurrenceFreshness and dftSparseOracle supply unary uniqueness and
     finite support tools. C3.3 must still construct source numeric
     compatibility from the global event matching and finite target list.
     No per-fuel witness, all-orbit no-Error premise, or terminating-callee
     premise is justified by these probes.
     Exact same-fuel dft_run_block_gas is a distinct frozen obligation;
     existential native fuel realization above does not prove it. It needs
     a budgeted block/callee argument, not a clock-equality inference.

   Hence the proposed conjunction is an explicit consumer contract only.
   None of the missing extensions may be inferred merely from its definition.
*)
