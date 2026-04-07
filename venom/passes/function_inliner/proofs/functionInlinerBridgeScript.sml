(*
 * Function Inliner — Bridge Lemma Infrastructure
 *
 * Connects INVOKE post-state to clone_execution_sim output state.
 * Key results:
 *   - step_inst/run_block/run_function preserve context fields
 *   - setup_callee/bind_outputs/merge_callee_state field lemmas
 *)

Theory functionInlinerBridge
Ancestors
  functionInlinerCallSimHelpers functionInlinerCloneExec
  functionInlinerSuffixSim
  venomExecSemantics venomInst venomWf stateEquiv stateEquivProps
  execEquivProps venomExecProps venomInstProps

open stringTheory rich_listTheory listTheory venomStateTheory
     finite_mapTheory pairTheory pred_setTheory

open functionInlinerDefsTheory functionInlinerCallSimHelpersTheory
     functionInlinerCalleeSimTheory functionInlinerCloneExecTheory
     functionInlinerSuffixSimTheory
     venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory stateEquivTheory stateEquivPropsTheory
     execEquivPropsTheory venomExecPropsTheory venomInstPropsTheory

(* ================================================================
   Context field preservation predicates
   ================================================================ *)

Definition ctx_fields_match_def:
  ctx_fields_match (s1:venom_state) (s2:venom_state) <=>
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_code = s2.vs_code /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End

Triviality ctx_fields_match_refl[simp]:
  !s. ctx_fields_match s s
Proof
  rw[ctx_fields_match_def]
QED

Triviality ctx_fields_match_sym[local]:
  !s1 s2. ctx_fields_match s1 s2 ==> ctx_fields_match s2 s1
Proof
  rw[ctx_fields_match_def]
QED

Triviality ctx_fields_match_trans[local]:
  !s1 s2 s3. ctx_fields_match s1 s2 /\ ctx_fields_match s2 s3 ==>
              ctx_fields_match s1 s3
Proof
  rw[ctx_fields_match_def]
QED

(* ================================================================
   Section 1: Component lemmas
   ================================================================ *)

(* jump_to preserves all context fields *)
Triviality jump_to_ctx_fields[local,simp]:
  !lbl s. ctx_fields_match (jump_to lbl s) s
Proof
  rw[ctx_fields_match_def, jump_to_def]
QED

(* FOLDL update_var preserves ALL non-vs_vars fields.
   update_var only modifies vs_vars, so FOLDL of it preserves everything else. *)
Triviality foldl_update_var_fields[local]:
  !pairs (s:venom_state).
    let s' = FOLDL (\s' (out,val). update_var out val s') s pairs in
    s'.vs_memory = s.vs_memory /\ s'.vs_transient = s.vs_transient /\
    s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\ s'.vs_returndata = s.vs_returndata /\
    (s'.vs_halted <=> s.vs_halted) /\ s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\ s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\ s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\ s'.vs_code = s.vs_code /\
    s'.vs_params = s.vs_params /\ s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  Induct >- simp[] >>
  qx_gen_tac `p` >> PairCases_on `p` >> rpt strip_tac >>
  simp[Once listTheory.FOLDL, LET_THM] >>
  first_x_assum (qspec_then `update_var p0 p1 s` mp_tac) >>
  simp[update_var_def]
QED

(* bind_outputs preserves ALL non-vs_vars fields *)
Theorem bind_outputs_fields[local]:
  !outs vals (s:venom_state) s'.
    bind_outputs outs vals s = SOME s' ==>
    s'.vs_memory = s.vs_memory /\ s'.vs_transient = s.vs_transient /\
    s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\ s'.vs_returndata = s.vs_returndata /\
    (s'.vs_halted <=> s.vs_halted) /\ s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\ s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\ s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\ s'.vs_code = s.vs_code /\
    s'.vs_params = s.vs_params /\ s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  rw[bind_outputs_def] >> Cases_on `LENGTH outs = LENGTH vals` >> gvs[] >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM] foldl_update_var_fields) >>
  metis_tac[]
QED

(* Derived: bind_outputs preserves ctx_fields (for backward compat) *)
Triviality bind_outputs_ctx_fields[local]:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >> imp_res_tac bind_outputs_fields >>
  simp[ctx_fields_match_def]
QED

(* merge_callee_state preserves caller's context fields *)
Triviality merge_callee_ctx_fields[local,simp]:
  !caller callee. ctx_fields_match (merge_callee_state caller callee) caller
Proof
  rw[ctx_fields_match_def, merge_callee_state_def]
QED

(* setup_callee preserves context fields *)
Theorem setup_callee_ctx_fields:
  !fn args s s'.
    setup_callee fn args s = SOME s' ==>
    ctx_fields_match s' s
Proof
  rw[setup_callee_def, ctx_fields_match_def] >>
  Cases_on `fn.fn_blocks` >> gvs[]
QED

(* with inst_idx preserves ctx fields *)
Triviality with_inst_idx_ctx_fields[local,simp]:
  !s n. ctx_fields_match (s with vs_inst_idx := n) s
Proof
  rw[ctx_fields_match_def]
QED

(* ================================================================
   Section 2: step_inst preserves context fields (ALL opcodes)

   We use precomputed conditional rewrites for step_inst_base
   to avoid the 500-line definition expansion at proof time.
   ================================================================ *)

(* Precompute step_inst_base for specific opcodes *)
val inst_eq_lemma = prove(
  ``inst.inst_opcode = (opc:opcode) ==> inst = inst with inst_opcode := opc``,
  simp[instruction_component_equality]);

fun mk_sib opc_tm =
  let
    val uncond = SIMP_CONV (srw_ss()) [step_inst_base_def]
      (``step_inst_base (inst with inst_opcode := ^opc_tm) (ss:venom_state)``)
    val inst_eq = UNDISCH (INST [``opc:opcode`` |-> opc_tm] inst_eq_lemma)
  in DISCH (mk_eq(``(inst:instruction).inst_opcode``, opc_tm))
           (REWRITE_RULE [SYM inst_eq] uncond) end;

val _ = print "Pre-computing SIB for bridge opcodes...\n";
val sib_JMP = mk_sib ``JMP``;
val sib_JNZ = mk_sib ``JNZ``;
val sib_DJMP = mk_sib ``DJMP``;
val sib_RET = mk_sib ``RET``;
val sib_STOP = mk_sib ``STOP``;
val sib_RETURN = mk_sib ``RETURN``;
val sib_REVERT = mk_sib ``REVERT``;
val sib_SINK = mk_sib ``SINK``;
val sib_SELFDESTRUCT = mk_sib ``SELFDESTRUCT``;
val sib_INVALID = mk_sib ``INVALID``;
val _ = print "Done.\n";

(* JMP/JNZ/DJMP return OK (jump_to) → ctx fields preserved *)
(* Per-terminator helpers using precomputed SIBs.
   Use fs[sib_*] to rewrite in assumptions (not goals). *)

Triviality step_inst_base_jmp_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ inst.inst_opcode = JMP ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >> fs[sib_JMP] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[ctx_fields_match_def, jump_to_def]
QED

Triviality step_inst_base_jnz_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ inst.inst_opcode = JNZ ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >> fs[sib_JNZ] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[ctx_fields_match_def, jump_to_def]
QED

Triviality step_inst_base_djmp_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ inst.inst_opcode = DJMP ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >> fs[sib_DJMP, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[ctx_fields_match_def, jump_to_def]
QED

(* RET/STOP/RETURN/REVERT never return OK *)
(* Terminators RET/STOP/RETURN/REVERT never return OK from step_inst_base *)
Triviality step_inst_base_ret_not_ok[local]:
  !inst s s'. inst.inst_opcode = RET ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_RET] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Triviality step_inst_base_stop_not_ok[local]:
  !inst s s'. inst.inst_opcode = STOP ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_STOP]
QED

Triviality step_inst_base_return_not_ok[local]:
  !inst s s'. inst.inst_opcode = RETURN ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_RETURN, LET_THM] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Triviality step_inst_base_revert_not_ok[local]:
  !inst s s'. inst.inst_opcode = REVERT ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_REVERT, LET_THM] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Triviality step_inst_base_sink_not_ok[local]:
  !inst s s'. inst.inst_opcode = SINK ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_SINK]
QED

Triviality step_inst_base_selfdestruct_not_ok[local]:
  !inst s s'. inst.inst_opcode = SELFDESTRUCT ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_SELFDESTRUCT, LET_THM] >> rpt strip_tac >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

Triviality step_inst_base_invalid_not_ok[local]:
  !inst s s'. inst.inst_opcode = INVALID ==> step_inst_base inst s <> OK s'
Proof
  simp[sib_INVALID, LET_THM]
QED

(* Main theorem: step_inst OK preserves ctx fields for ALL opcodes *)
Theorem step_inst_ok_ctx_fields:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst.inst_opcode = INVOKE`) >- (
    (* Non-INVOKE: step_inst = step_inst_base *)
    fs[step_inst_def] >>
    Cases_on `is_terminator inst.inst_opcode` >| [
      (* Terminator cases: only JMP/JNZ/DJMP return OK *)
      Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
      metis_tac[step_inst_base_jmp_ctx, step_inst_base_jnz_ctx,
                step_inst_base_djmp_ctx, step_inst_base_ret_not_ok,
                step_inst_base_stop_not_ok, step_inst_base_return_not_ok,
                step_inst_base_revert_not_ok, step_inst_base_sink_not_ok,
                step_inst_base_selfdestruct_not_ok,
                step_inst_base_invalid_not_ok],
      (* Non-terminator, non-INVOKE: step_preserves_* apply *)
      (SUBGOAL_THEN ``step_inst fuel ctx inst s = OK s'``
         ASSUME_TAC >- simp[step_inst_def]) >>
      simp[ctx_fields_match_def] >>
      metis_tac[step_preserves_call_ctx, step_preserves_tx_ctx,
                step_preserves_block_ctx, step_preserves_code,
                step_preserves_data_section, step_preserves_labels,
                step_preserves_prev_hashes]
    ]
  ) >>
  (* INVOKE case *)
  fs[step_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  imp_res_tac bind_outputs_ctx_fields >>
  metis_tac[merge_callee_ctx_fields, ctx_fields_match_trans]
QED

(* step_inst_base IntRet preserves ctx_fields.
   Only RET returns IntRet (with s unchanged), all others produce OK/Error/Halt/Abort.
   AllCaseEqs() normalizes the case expression to a disjunction; only RET gives IntRet. *)
Triviality step_inst_base_intret_ctx_fields[local]:
  !inst s vals s'.
    step_inst_base inst s = IntRet vals s' ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >>
  gvs[step_inst_base_def, AllCaseEqs(),
      exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, exec_alloca_def,
      extract_venom_result_def]
QED

(* step_inst IntRet preserves ctx fields.
   - INVOKE maps callee IntRet to OK, never returns IntRet itself.
   - Non-INVOKE: step_inst = step_inst_base → use helper above. *)
Theorem step_inst_intret_ctx_fields:
  !fuel ctx inst s vals s'.
    step_inst fuel ctx inst s = IntRet vals s' ==>
    ctx_fields_match s' s
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst.inst_opcode = INVOKE`) >- (
    fs[step_inst_def] >>
    metis_tac[step_inst_base_intret_ctx_fields]
  ) >>
  (* INVOKE: never returns IntRet *)
  fs[step_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* ================================================================
   Section 3: run_block preserves context fields
   ================================================================ *)

(* run_block OK or IntRet preserves ctx fields.
   Proof: measure induction on LENGTH insts - inst_idx.
   Keep conjunction intact to avoid eall issues with >|. *)
Theorem run_block_ctx_fields:
  !fuel ctx bb s.
    (!s'. run_block fuel ctx bb s = OK s' ==>
          ctx_fields_match s' s) /\
    (!vals s'. run_block fuel ctx bb s = IntRet vals s' ==>
               ctx_fields_match s' s)
Proof
  gen_tac >> gen_tac >> gen_tac >>
  `!n s. n = LENGTH bb.bb_instructions - s.vs_inst_idx ==>
     (!s'. run_block fuel ctx bb s = OK s' ==>
           ctx_fields_match s' s) /\
     (!vals s'. run_block fuel ctx bb s = IntRet vals s' ==>
                ctx_fields_match s' s)` suffices_by metis_tac[] >>
  Induct_on `n` >- (
    (* Base: inst_idx >= LENGTH instructions — run_block returns Error *)
    rpt gen_tac >> strip_tac >> CONJ_TAC >> rpt strip_tac >>
    pop_assum mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[get_instruction_def]
  ) >>
  (* Step: n = SUC n'. Handle OK and IntRet conjuncts separately. *)
  rpt gen_tac >> strip_tac >> CONJ_TAC >- (
    (* OK conjunct: 2 goals after gvs[] *)
    rpt strip_tac >> pop_assum mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
    >- imp_res_tac step_inst_ok_ctx_fields
    >> (imp_res_tac step_inst_ok_ctx_fields >>
        first_x_assum (qspec_then `s'' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
        (impl_tac >- (simp[] >> fs[get_instruction_def] >> decide_tac)) >>
        strip_tac >>
        metis_tac[with_inst_idx_ctx_fields, ctx_fields_match_trans])
  ) >> (
    (* IntRet conjunct: 2 goals after gvs[] *)
    rpt strip_tac >> pop_assum mp_tac >>
    ONCE_REWRITE_TAC[run_block_def] >>
    simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
    >- (* Non-term, recursive IntRet *)
       (imp_res_tac step_inst_ok_ctx_fields >>
        first_x_assum (qspec_then `s'' with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
        (impl_tac >- (simp[] >> fs[get_instruction_def] >> decide_tac)) >>
        strip_tac >>
        metis_tac[with_inst_idx_ctx_fields, ctx_fields_match_trans])
    >> (* Direct IntRet from step_inst *)
       metis_tac[step_inst_intret_ctx_fields]
  )
QED

(* ================================================================
   Section 4: run_function preserves context fields
   ================================================================ *)

Theorem run_function_ctx_fields:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    ctx_fields_match s' s
Proof
  Induct_on `fuel` >- (
    ONCE_REWRITE_TAC[run_function_def] >> simp[]
  ) >>
  rpt strip_tac >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  Cases_on `run_block fuel ctx x s` >> simp[] >- (
    (* run_block OK *)
    Cases_on `v.vs_halted` >> simp[] >>
    strip_tac >>
    `ctx_fields_match v s` by metis_tac[run_block_ctx_fields] >>
    `ctx_fields_match s' v` by metis_tac[] >>
    metis_tac[ctx_fields_match_trans]
  ) >>
  (* run_block IntRet *)
  strip_tac >> gvs[] >>
  metis_tac[run_block_ctx_fields]
QED

(* Individual field accessors *)
Theorem run_function_preserves_call_ctx:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_tx_ctx:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_block_ctx:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_code:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_code = s.vs_code
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_data_section:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_data_section = s.vs_data_section
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_labels:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_labels = s.vs_labels
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

Theorem run_function_preserves_prev_hashes:
  !fuel ctx fn s vals s'.
    run_function fuel ctx fn s = IntRet vals s' ==>
    s'.vs_prev_hashes = s.vs_prev_hashes
Proof
  metis_tac[run_function_ctx_fields, ctx_fields_match_def]
QED

(* ================================================================
   Bridge lemma: connect INVOKE post-state to clone output state.

   After INVOKE returns IntRet vals callee_s', the post-INVOKE state
   (merge + bind_outputs) is execution_equiv with the clone's s_at_ret,
   given that:
   - s_pre1 and s_clone are execution_equiv (from prefix execution)
   - callee_s' and s_at_ret agree on globals (shared_globals_np)
   - callee preserves ctx_fields from s_pre1 (setup_callee + run_function)
   - output vars match, frame vars preserved
   ================================================================ *)

(* Helper: merge_callee_state preserves vs_params *)
Triviality merge_callee_state_params[local,simp]:
  !s1 s2. (merge_callee_state s1 s2).vs_params = s1.vs_params
Proof
  simp[merge_callee_state_def]
QED

(* Helper: merge_callee_state preserves vs_halted *)
Triviality merge_callee_state_halted[local,simp]:
  !s1 s2. (merge_callee_state s1 s2).vs_halted = s1.vs_halted
Proof
  simp[merge_callee_state_def]
QED

(* bind_outputs through merge: s_post fields come from merge input,
   which gets ctx_fields from s_pre (caller) and globals from callee_s.
   Proof: bind_outputs_fields says s_post.f = (merge s_pre callee_s).f,
   then merge_callee_state_def resolves which original state each field comes from. *)
Triviality bind_outputs_merge_fields[local]:
  !outs vals s_pre callee_s s_post.
    bind_outputs outs vals (merge_callee_state s_pre callee_s) = SOME s_post ==>
    (* ctx_fields from s_pre *)
    s_post.vs_call_ctx = s_pre.vs_call_ctx /\
    s_post.vs_tx_ctx = s_pre.vs_tx_ctx /\
    s_post.vs_block_ctx = s_pre.vs_block_ctx /\
    s_post.vs_code = s_pre.vs_code /\
    s_post.vs_data_section = s_pre.vs_data_section /\
    s_post.vs_labels = s_pre.vs_labels /\
    s_post.vs_prev_hashes = s_pre.vs_prev_hashes /\
    (* globals from callee_s *)
    s_post.vs_memory = callee_s.vs_memory /\
    s_post.vs_transient = callee_s.vs_transient /\
    s_post.vs_accounts = callee_s.vs_accounts /\
    s_post.vs_returndata = callee_s.vs_returndata /\
    s_post.vs_logs = callee_s.vs_logs /\
    s_post.vs_immutables = callee_s.vs_immutables /\
    s_post.vs_allocas = s_pre.vs_allocas /\
    s_post.vs_alloca_next = callee_s.vs_alloca_next /\
    (* non-var scalar fields from s_pre *)
    s_post.vs_params = s_pre.vs_params /\
    (s_post.vs_halted <=> s_pre.vs_halted)
Proof
  rpt strip_tac >> imp_res_tac bind_outputs_fields >>
  fs[merge_callee_state_def]
QED

(* FOLDL update_var preserves non-updated vars *)
Triviality foldl_update_var_non_mem[local]:
  !pairs (acc:venom_state) v.
    ~MEM v (MAP FST pairs) ==>
    lookup_var v (FOLDL (\s' (out,val). update_var out val s') acc pairs) =
    lookup_var v acc
Proof
  Induct >> simp[] >> Cases >> simp[] >> rpt strip_tac >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* FOLDL update_var binds output vars to their values (ALL_DISTINCT) *)
Triviality foldl_update_var_el[local]:
  !pairs (acc:venom_state) i.
    ALL_DISTINCT (MAP FST pairs) /\ i < LENGTH pairs ==>
    lookup_var (FST (EL i pairs)) (FOLDL (\s' (out,val). update_var out val s') acc pairs) =
    SOME (SND (EL i pairs))
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[] >> strip_tac >>
  Cases_on `i` >> fs[] >>
  `~MEM h0 (MAP FST pairs)` by (fs[MEM_MAP, MEM_EL] >> metis_tac[FST]) >>
  mp_tac (Q.SPECL [`pairs`, `update_var h0 h1 acc`, `h0`] foldl_update_var_non_mem) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* lookup_var through merge_callee_state + bind_outputs: non-output *)
Theorem merge_bind_lookup_var:
  !outs vals s_pre callee_s s_post v.
    bind_outputs outs vals (merge_callee_state s_pre callee_s) = SOME s_post /\
    ~MEM v outs ==>
    lookup_var v s_post = lookup_var v s_pre
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  `lookup_var v (FOLDL (\s' (out,val). update_var out val s')
     (merge_callee_state s_pre callee_s) (ZIP (outs,vals))) =
   lookup_var v (merge_callee_state s_pre callee_s)` by (
    irule foldl_update_var_non_mem >> simp[MAP_ZIP]) >>
  simp[merge_callee_state_def, lookup_var_def]
QED

(* lookup_var through bind_outputs: output var at index i *)
Theorem bind_outputs_lookup_var_el:
  !outs vals s s' i.
    bind_outputs outs vals s = SOME s' /\
    ALL_DISTINCT outs /\ i < LENGTH outs /\ i < LENGTH vals ==>
    lookup_var (EL i outs) s' = SOME (EL i vals)
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`ZIP (outs,vals)`, `s`, `i`] foldl_update_var_el) >>
  simp[MAP_ZIP, EL_ZIP, LENGTH_ZIP]
QED

(* The bridge lemma: after INVOKE returns IntRet, the post-INVOKE state
   (merge + bind_outputs) is execution_equiv with clone's s_at_ret,
   assuming prefix execution produced execution_equiv states and
   clone_execution_sim properties hold. *)
Theorem invoke_clone_bridge:
  !excl_vars s_pre1 s_clone callee_s' s_post s_at_ret
   outs vals.
    (* States before INVOKE / clone are execution_equiv *)
    execution_equiv excl_vars s_pre1 s_clone /\
    (* INVOKE side: merge + bind_outputs *)
    bind_outputs outs vals (merge_callee_state s_pre1 callee_s') = SOME s_post /\
    ALL_DISTINCT outs /\ LENGTH outs = LENGTH vals /\
    (* Clone side properties (from clone_execution_sim IntRet) *)
    shared_globals_np callee_s' s_at_ret /\
    s_at_ret.vs_params = s_clone.vs_params /\
    ~s_at_ret.vs_halted /\
    (!v. v NOTIN excl_vars /\ ~MEM v outs ==>
         lookup_var v s_at_ret = lookup_var v s_clone) /\
    (!i. i < LENGTH vals /\ i < LENGTH outs ==>
         lookup_var (EL i outs) s_at_ret = SOME (EL i vals)) /\
    (* Callee preserves ctx_fields from caller *)
    ctx_fields_match s_pre1 callee_s' /\
    (* Clone preserves allocas (vs_allocas is write-only, no ALLOCA in clone) *)
    s_at_ret.vs_allocas = s_clone.vs_allocas /\
    (* Pre-INVOKE state not halted *)
    ~s_pre1.vs_halted ==>
    execution_equiv excl_vars s_post s_at_ret
Proof
  rpt strip_tac >>
  imp_res_tac bind_outputs_merge_fields >>
  fs[shared_globals_np_def, ctx_fields_match_def, execution_equiv_def] >>
  (* Remaining: vars clause *)
  rpt strip_tac >>
  Cases_on `MEM v outs`
  >- (
    (* v is an output — both sides bound to same value *)
    gvs[MEM_EL] >>
    imp_res_tac bind_outputs_lookup_var_el >> fs[]
  )
  >- (
    (* v not an output — chain: s_post -> s_pre1 -> s_clone -> s_at_ret *)
    imp_res_tac merge_bind_lookup_var >> fs[]
  )
QED

val _ = export_theory();
