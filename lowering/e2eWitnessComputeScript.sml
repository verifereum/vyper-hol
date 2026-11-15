(* Concrete compilation and deploy/get runs for p23_imm_uint256.
 * TOP-LEVEL: p23_compile, p23_dep_run, p23_call_run, p23_load,
 * p23_source_call_42, p23_evm_return_42, p23_deploy_entry_no_calls,
 * p23_call_entry_no_calls, p23_deploy_source_calls_within,
 * p23_source_calls_within.
 * Helpers: the concrete p23 states and the quiet-frame trace observer.
 *)
Theory e2eWitnessCompute
Ancestors
  compileVyper venomPipelineDriver asmOptimizer supportedProgram
  concretizeMemLocDefs codegenReadyCompute alist integer_word option
  e2eDefs sourceCallCount callTrace frameOutcome
  vyperInterpreter vfmCompute
Libs
  memoryStoreWitnessLib finite_mapLib cv_transLib computeLib wordsLib BasicProvers

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["../bytecode/immutables/oracle"]

(* The compset the repo's compile tests evaluate compile_vyper with
   (tests/create/createRawCompileTestScript.sml). *)
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos])

(* ===== The fixture and its compilation ===== *)

val p23_tops_tm = memoryStoreWitnessLib.program
  "../bytecode/immutables/oracle" "p23_imm_uint256"

Definition p23_tops_def:
  p23_tops = ^p23_tops_tm
End

(* Evaluated once outside any proof step, on the literal program as the
   compile tests do, then folded back onto p23_tops. *)
val p23_compile_eval =
  REWRITE_RULE [GSYM p23_tops_def]
    (EVAL ``compile_vyper (K SOME) (o1_policy all_capabilities) ^p23_tops_tm``);

val (p23_deploy_bytes, p23_runtime_bytes) =
  pairSyntax.dest_pair (optionSyntax.dest_some (rhs (concl p23_compile_eval)));

Definition p23_deploy_bc_def:
  p23_deploy_bc : word8 list = ^p23_deploy_bytes
End

Definition p23_runtime_bc_def:
  p23_runtime_bc : word8 list = ^p23_runtime_bytes
End

Theorem p23_compile:
  compile_vyper (K SOME) (o1_policy all_capabilities) p23_tops =
    SOME (p23_deploy_bc, p23_runtime_bc)
Proof
  PURE_REWRITE_TAC [p23_compile_eval, p23_deploy_bc_def, p23_runtime_bc_def] >>
  REFL_TAC
QED

(* ===== Concrete transactions and EVM states ===== *)

Definition p23_deploy_tx_def:
  p23_deploy_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "__init__";
       code := p23_deploy_bc;
       block_number := 1; block_hashes := [0w] |>
End

val p23_get_calldata_eval =
  EVAL ``function_selector "get" [] ++ enc (Tuple []) (ListV [])``;

Definition p23_get_calldata_def:
  p23_get_calldata : word8 list = ^(rhs (concl p23_get_calldata_eval))
End

Theorem p23_get_calldata_encodes:
  p23_get_calldata = function_selector "get" [] ++ enc (Tuple []) (ListV [])
Proof
  REWRITE_TAC [p23_get_calldata_eval, p23_get_calldata_def]
QED

Definition p23_call_tx_def:
  p23_call_tx = empty_call_txn with
    <| target := 2w; sender := 1w; function_name := "get";
       calldata := p23_get_calldata;
       code := p23_runtime_bc ++ word_to_bytes (42w : bytes32) T;
       block_number := 1; block_hashes := [0w] |>
End

(* The block fields both transactions read: tx_block_fields_rel. *)
Definition p23_tx_params_def:
  p23_tx_params =
    <| origin := 0w; gasPrice := 0; baseFeePerGas := 0;
       baseFeePerBlobGas := 0; blockNumber := 1; blockTimeStamp := 0;
       blockCoinBase := 0w; blockGasLimit := 0; prevRandao := 0w;
       prevHashes := [0w]; blobHashes := []; chainId := 0;
       authRefund := 0 |>
End

Definition p23_frame_def:
  p23_frame code data out =
    <| stack := []; memory := empty_buffer; pc := 0; jumpDest := NONE;
       returnData := []; gasUsed := 0; addRefund := 0; subRefund := 0;
       logs := [];
       msgParams :=
         <| caller := 1w; callee := 2w; code := code;
            parsed := parse_code 0 FEMPTY code; value := 0;
            gasLimit := 1000000; data := buffer_of_list data;
            static := F; outputTo := out |> |>
End

Definition p23_dep_rollback_def:
  p23_dep_rollback =
    <| accounts := empty_accounts; tStorage := empty_transient_storage;
       accesses := <| addresses := fEMPTY; storageKeys := fEMPTY |>;
       toDelete := [] |>
End

(* One creation frame running the deploy code at the empty address 2w. *)
Definition p23_es_dep_def:
  p23_es_dep =
    <| contexts := [(p23_frame p23_deploy_bc [] (Code 2w), p23_dep_rollback)];
       txParams := p23_tx_params; rollback := p23_dep_rollback;
       originalAccounts := empty_accounts;
       msdomain := Collect empty_domain |>
End

(* The call frame after deployment es': the committed accounts (pending
 * deletions processed, target code installed), fresh transient storage. *)
Definition p23_es_call_of_def:
  p23_es_call_of es' =
    let accts = process_deletions es'.rollback.toDelete es'.rollback.accounts in
    let rb = es'.rollback with
               <| accounts := accts; tStorage := empty_transient_storage;
                  toDelete := [] |> in
      <| contexts :=
           [(p23_frame (lookup_account 2w accts).code p23_get_calldata
               (Memory <| offset := 0; size := 0 |>), rb)];
         txParams := p23_tx_params; rollback := rb;
         originalAccounts := accts;
         msdomain := Collect empty_domain |>
End

Definition p23_es_call_def:
  p23_es_call =
    case run_call p23_es_dep of
      SOME (r, es') => p23_es_call_of es'
    | NONE => p23_es_dep
End

(* ===== The observed call trace and gas readings, by cv evaluation ===== *)

(* frame_obs's observers read HD/EL of contexts and stacks, so its cv
   translation carries side conditions that hold only by EVM step facts.
   Instead, frame_quiet_tr walks the same steps as frame_obs_tr and checks
   that no step at the frame's own depth is a GAS read or an observable
   call: then the observer never records anything (frame_quiet_tr_obs). It
   is total, so cv evaluates it on the concrete runs. *)
Definition frame_quiet_tr_def:
  frame_quiet_tr d s (r, s') <=>
    (ISR r \/
     case s.contexts of
       [] => F
     | (c, rb) :: rest =>
         LENGTH s.contexts <> d \/
         (next_opcode c <> SOME Gas /\ ~observable_call c)) /\
    (if ISR r \/ LENGTH s'.contexts < d then T
     else frame_quiet_tr d s' (step s'))
Termination
  WF_REL_TAC `inv_image ($< LEX ($< LEX $<))
    (\(d, s, (r, s')).
      if ISR r \/ LENGTH s'.contexts < d then ((0:num), (0, 0))
      else (1, vfmDecreasesGas$contexts_weight 0 s'.contexts))` >>
  rpt gen_tac >>
  rename1 `step post` >>
  mp_tac (Q.SPEC `post` (REWRITE_RULE [vfmDecreasesGasTheory.decreases_gas_cred_def]
    vfmDecreasesGasTheory.decreases_gas_cred_step)) >>
  IF_CASES_TAC >- (
    rw[vfmDecreasesGasTheory.contexts_weight_def,
       vfmExecutionPropTheory.unused_gas_def] >>
    gvs[vfmExecutionTheory.step_def, vfmExecutionTheory.handle_def,
        vfmExecutionTheory.get_current_context_def,
        vfmExecutionTheory.bind_def, vfmExecutionTheory.fail_def] >>
    gvs[vfmExecutionTheory.handle_step_def, vfmExecutionTheory.reraise_def]) >>
  rw[] >> fs[pairTheory.LEX_DEF, pairTheory.UNCURRY] >>
  metis_tac[sumTheory.sum_CASES, sumTheory.ISL, sumTheory.ISR]
End

Theorem observe_quiet[local]:
  (ISR r \/
   case s.contexts of
     [] => F
   | (c, rb) :: rest =>
       LENGTH s.contexts <> d \/
       (next_opcode c <> SOME Gas /\ ~observable_call c)) /\
  obs.pending = NONE ==>
  observe d s (r, s') obs = obs
Proof
  Cases_on `r` >> simp[observe_def] >>
  Cases_on `s.contexts` >> simp[] >>
  PairCases_on `h` >> rw[] >> gvs[]
QED

Theorem frame_quiet_tr_obs:
  !d s x obs.
    frame_quiet_tr d s x /\ obs.pending = NONE ==>
    frame_obs_tr d obs s x = obs
Proof
  simp[pairTheory.FORALL_PROD] >>
  recInduct frame_quiet_tr_ind >> rpt gen_tac >> strip_tac >>
  gen_tac >> strip_tac >>
  `observe d s (r,s') obs = obs` by (
    irule observe_quiet >> asm_rewrite_tac[] >>
    qpat_x_assum `frame_quiet_tr _ _ _` mp_tac >>
    PURE_ONCE_REWRITE_TAC [frame_quiet_tr_def] >>
    rpt strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `frame_quiet_tr _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC [frame_quiet_tr_def] >>
  strip_tac >>
  PURE_ONCE_REWRITE_TAC [frame_obs_tr_def] >>
  asm_simp_tac std_ss [LET_THM] >>
  Cases_on `ISR r \/ LENGTH s'.contexts < d` >> gvs[]
QED

Theorem frame_quiet_obs:
  frame_quiet_tr (LENGTH es.contexts) es (step es) ==>
  gas_readings es = [] /\ call_trace es = []
Proof
  strip_tac >>
  `frame_obs es = <| entries := []; readings := []; pending := NONE |>`
    by (simp[frame_obs_def] >> irule frame_quiet_tr_obs >> simp[]) >>
  simp[gas_readings_def, call_trace_def]
QED

val () = cv_auto_trans next_opcode_def;
val () = cv_auto_trans observable_call_def;
(* The precondition only records the recursion; it holds by its induction,
   as vfmCompute's run_call_tr_pre. *)
val frame_quiet_tr_pre_def = cv_trans_pre "frame_quiet_tr_pre" frame_quiet_tr_def;

Theorem frame_quiet_tr_pre[cv_pre]:
  !d s x. frame_quiet_tr_pre d s x
Proof
  simp[pairTheory.FORALL_PROD] >>
  recInduct frame_quiet_tr_ind >> rw[] >>
  rw[Once frame_quiet_tr_pre_def]
QED

val () = cv_auto_trans p23_deploy_bc_def;
val () = cv_auto_trans p23_runtime_bc_def;
val () = cv_auto_trans p23_tx_params_def;
val () = cv_auto_trans p23_frame_def;
val () = cv_auto_trans p23_dep_rollback_def;
val () = cv_auto_trans p23_es_dep_def;
val () = cv_auto_trans p23_get_calldata_def;
val () = cv_auto_trans p23_es_call_of_def;
val () = cv_auto_trans p23_es_call_def;

(* ===== The concrete runs, evaluated once at top level ===== *)

val p23_dep_run_eval = cv_eval ``run_call p23_es_dep``;

Definition p23_es_dep_post_def:
  p23_es_dep_post =
    ^(snd (pairSyntax.dest_pair
            (optionSyntax.dest_some (rhs (concl p23_dep_run_eval)))))
End

Theorem p23_dep_run:
  run_call p23_es_dep = SOME (INR NONE, p23_es_dep_post)
Proof
  PURE_REWRITE_TAC [p23_dep_run_eval, p23_es_dep_post_def] >> REFL_TAC
QED

Theorem p23_es_call_from_post:
  p23_es_call = p23_es_call_of p23_es_dep_post
Proof
  simp[p23_es_call_def, p23_dep_run]
QED

val p23_call_run_eval = cv_eval ``run_call p23_es_call``;

Definition p23_es_call_post_def:
  p23_es_call_post =
    ^(snd (pairSyntax.dest_pair
            (optionSyntax.dest_some (rhs (concl p23_call_run_eval)))))
End

Theorem p23_call_run:
  run_call p23_es_call = SOME (INR NONE, p23_es_call_post)
Proof
  PURE_REWRITE_TAC [p23_call_run_eval, p23_es_call_post_def] >> REFL_TAC
QED

val p23_dep_quiet = cv_eval
  ``frame_quiet_tr (LENGTH p23_es_dep.contexts) p23_es_dep (step p23_es_dep)``;
val p23_call_quiet = cv_eval
  ``frame_quiet_tr (LENGTH p23_es_call.contexts) p23_es_call (step p23_es_call)``;

Theorem p23_dep_trace:
  gas_readings p23_es_dep = [] /\ call_trace p23_es_dep = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM p23_dep_quiet)
QED

Theorem p23_call_trace:
  gas_readings p23_es_call = [] /\ call_trace p23_es_call = []
Proof
  irule frame_quiet_obs >> ACCEPT_TAC (EQT_ELIM p23_call_quiet)
QED

(* The source deployment, on the deploy frame's (empty) callee outcomes,
   never reads its gas list (no msg.gas). *)
val p23_load_eval = EVAL
  ``load_contract (SOME []) gs initial_machine_state p23_deploy_tx
      [(NONE, p23_tops)] []``;

Definition p23_am_dep_post_def:
  p23_am_dep_post =
    ^(fst (pairSyntax.dest_pair
            (fst (sumSyntax.dest_inl (rhs (concl p23_load_eval))))))
End

Theorem p23_load:
  !gs. load_contract (SOME []) gs initial_machine_state p23_deploy_tx
         [(NONE, p23_tops)] [] = INL (p23_am_dep_post, [])
Proof
  gen_tac >> PURE_REWRITE_TAC [p23_load_eval, p23_am_dep_post_def] >>
  REFL_TAC
QED

(* The source machine the call starts from. *)
Definition p23_am_call_def:
  p23_am_call = next_source_machine p23_am_dep_post p23_es_dep_post
End

val p23_src_call_42 = EVAL
  ``FST (call_external (SOME []) [] p23_am_call p23_call_tx) = INL (IntV 42)``;

val p23_return_42 = EVAL
  ``(FST (HD p23_es_call_post.contexts)).returnData =
    word_to_bytes (42w : bytes32) T``;

Theorem p23_source_call_42:
  FST (call_external (SOME []) [] p23_am_call p23_call_tx) = INL (IntV 42)
Proof
  ACCEPT_TAC (EQT_ELIM p23_src_call_42)
QED

Theorem p23_evm_return_42:
  (FST (HD p23_es_call_post.contexts)).returnData =
    word_to_bytes (42w : bytes32) T
Proof
  ACCEPT_TAC (EQT_ELIM p23_return_42)
QED

Theorem p23_call_data:
  buffer_to_list (FST (HD p23_es_call.contexts)).msgParams.data =
    p23_get_calldata
Proof
  simp[p23_es_call_from_post, p23_es_call_of_def, p23_frame_def]
QED

(* These evaluations leave both oracle lists symbolic. Empty EVM traces
   alone would not establish a bound on source execution. *)
val p23_deploy_entry_eval = EVAL
  ``case deploy_entry_run os obs p23_tops initial_machine_state p23_deploy_tx of
      NONE => F
    | SOME (res, st) => st.outcomes = SOME os /\ st.requests = []``;

Theorem p23_deploy_entry_no_calls:
  !os obs.
    case deploy_entry_run os obs p23_tops initial_machine_state p23_deploy_tx of
      NONE => F
    | SOME (res, st) => st.outcomes = SOME os /\ st.requests = []
Proof
  REWRITE_TAC [p23_deploy_entry_eval]
QED

val p23_call_entry_eval = EVAL
  ``case call_entry_run os obs p23_am_call p23_call_tx of
      NONE => F
    | SOME (res, st) => st.outcomes = SOME os /\ st.requests = []``;

Theorem p23_call_entry_no_calls:
  !os obs.
    case call_entry_run os obs p23_am_call p23_call_tx of
      NONE => F
    | SOME (res, st) => st.outcomes = SOME os /\ st.requests = []
Proof
  REWRITE_TAC [p23_call_entry_eval]
QED

Theorem p23_deploy_source_calls_within:
  !obs. deploy_source_calls_within (2 ** 64) p23_tops initial_machine_state
          p23_deploy_tx (MAP SND (call_trace p23_es_dep)) obs
Proof
  gen_tac >>
  `?k. 2 ** 64 = SUC k` by
    (qexists_tac `2 ** 64 - 1` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[p23_dep_trace, deploy_source_calls_within_def,
    entry_calls_within_def] >>
  PURE_ONCE_REWRITE_TAC [entry_calls_within_from_def] >> simp[] >>
  mp_tac (Q.SPECL [`[probe_failed_outcome]`, `obs`]
    p23_deploy_entry_no_calls) >>
  every_case_tac >> gvs[]
QED

Theorem p23_source_calls_within:
  !obs. source_calls_within (2 ** 64) p23_am_call p23_call_tx
          (MAP SND (call_trace p23_es_call)) obs
Proof
  gen_tac >>
  `?k. 2 ** 64 = SUC k` by
    (qexists_tac `2 ** 64 - 1` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[p23_call_trace, source_calls_within_def,
    entry_calls_within_def] >>
  PURE_ONCE_REWRITE_TAC [entry_calls_within_from_def] >> simp[] >>
  mp_tac (Q.SPECL [`[probe_failed_outcome]`, `obs`]
    p23_call_entry_no_calls) >>
  every_case_tac >> gvs[]
QED
