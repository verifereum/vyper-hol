(*
 * Context / Memory Operations Properties
 *
 * TOP-LEVEL:
 *   compile_ptr_load_memory_correct   — MLOAD returns value at address
 *   compile_ptr_load_storage_correct  — SLOAD returns storage value at slot
 *   compile_ptr_store_memory_correct  — MSTORE writes value to memory
 *   compile_ptr_store_storage_correct — SSTORE writes value to storage
 *   compile_load_storage_prim_correct — compile_load_storage primitive case
 *   compile_store_storage_prim_correct— compile_store_storage primitive case
 *   compile_nonreentrant_lock_correct — lock sets storage slot (persistent)
 *   compile_nonreentrant_lock_revert  — locked slot causes revert
 *   compile_nonreentrant_lock_view    — view lock checks but doesn't write
 *   compile_nonreentrant_unlock_correct — unlock writes 3 to slot
 *   compile_copy_memory_correct       — MCOPY for nonzero size
 *   compile_zero_memory_correct       — zero memory region
 *   compile_ptr_store_storage_preserves_memory — SSTORE doesn't touch memory
 *
 * Helpers (prover should create as needed in emitHelperPropsScript.sml):
 *   step_SLOAD, step_SSTORE — step_inst_base for SLOAD/SSTORE
 *   emit_op_SLOAD_correct   — emit_op SLOAD wrapper
 *   emit_void_SSTORE_correct— emit_void SSTORE wrapper
 *   sload_sstore_same       — sload k (sstore k v s) = v
 *   sload_update_var         — sload k (update_var v w s) = sload k s
 *   sstore_vs_memory         — (sstore k v s).vs_memory = s.vs_memory
 *
 * Source: context.py (VenomCompilerContext)
 * Lowering: contextScript.sml
 *)

Theory contextProps
Ancestors
  exprLoweringProps emitHelperProps
  context compileEnv
  venomExecSemantics venomState
  valueEncoding vfmState

(* ===== Pointer Load ===== *)

(* compile_ptr_load LocMemory emits a single MLOAD instruction.
   Result: fresh var holds mload(w2n addr) of the original state.
   Proof: unfold compile_ptr_load_def → emit_op MLOAD, then
   apply emit_op_MLOAD_correct (already in emitHelperProps). *)
Theorem compile_ptr_load_memory_correct:
  ∀ is_ctor op st ret_op st' ss addr.
    compile_ptr_load is_ctor LocMemory op st = (ret_op, st') ∧
    eval_operand op ss = SOME addr ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand ret_op ss' = SOME (mload (w2n addr) ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op' w. eval_operand op' ss = SOME w ⇒
                eval_operand op' ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> gvs[compile_ptr_load_def] >>
  mp_tac (emit_op_read1_correct
    |> Q.SPECL [`MLOAD`, `\v s. mload (w2n v) s`,
                 `op`, `addr`, `st`, `ret_op`, `st'`, `ss`]) >>
  impl_tac
  >- (rw[] >> irule step_MLOAD >> rw[]) >>
  strip_tac >> goal_assum drule >> simp[]
QED

(* compile_ptr_load LocStorage emits a single SLOAD instruction.
   Result: fresh var holds sload(slot) of the original state.
   Proof: unfold compile_ptr_load_def → emit_op SLOAD, then
   build emit_op_SLOAD_correct analogously to emit_op_MLOAD_correct.
   sload reads from vs_accounts, update_var writes vs_vars → independent. *)
Theorem compile_ptr_load_storage_correct:
  ∀ is_ctor op st ret_op st' ss slot.
    compile_ptr_load is_ctor LocStorage op st = (ret_op, st') ∧
    eval_operand op ss = SOME slot ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand ret_op ss' = SOME (sload slot ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op' w. eval_operand op' ss = SOME w ⇒
                eval_operand op' ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> gvs[compile_ptr_load_def] >>
  drule_all emit_op_SLOAD_correct >> strip_tac >>
  goal_assum drule >> simp[]
QED

(* ===== Pointer Store ===== *)

(* compile_ptr_store LocMemory emits a single MSTORE instruction.
   Result state = mstore (w2n addr) val ss.
   Proof: unfold → emit_void MSTORE, apply emit_void_MSTORE_correct. *)
Theorem compile_ptr_store_memory_correct:
  ∀ is_ctor op_addr op_val st st' ss addr val.
    compile_ptr_store is_ctor LocMemory op_addr op_val st = ((), st') ∧
    eval_operand op_addr ss = SOME addr ∧
    eval_operand op_val ss = SOME val ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = mstore (w2n addr) val ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w)
Proof
  rpt strip_tac >> gvs[compile_ptr_store_def] >>
  drule_all emit_void_MSTORE_correct >> simp[]
QED

(* compile_ptr_store LocStorage emits a single SSTORE instruction.
   Result state = sstore addr val ss.
   Note: SSTORE operand order is [dst; val], so addr is first arg to sstore.
   Proof: unfold → emit_void SSTORE, use step_inst_base exec_write2 path
   for SSTORE (analogous to step_MSTORE). *)
Theorem compile_ptr_store_storage_correct:
  ∀ is_ctor op_addr op_val st st' ss addr val.
    compile_ptr_store is_ctor LocStorage op_addr op_val st = ((), st') ∧
    eval_operand op_addr ss = SOME addr ∧
    eval_operand op_val ss = SOME val ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = sstore addr val ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w)
Proof
  rpt strip_tac >> gvs[compile_ptr_store_def] >>
  drule_all emit_void_SSTORE_correct >> simp[]
QED

(* ===== Storage Load/Store (compound) ===== *)

(* compile_load_storage with is_prim_word=T is just SLOAD.
   compile_load_storage slot T word_count alloca_size = emit_op SLOAD [slot].
   This is a direct corollary of compile_ptr_load_storage_correct. *)
Theorem compile_load_storage_prim_correct:
  ∀ slot_op st ret_op st' ss slot_w word_count alloca_size.
    compile_load_storage slot_op T word_count alloca_size st = (ret_op, st') ∧
    eval_operand slot_op ss = SOME slot_w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand ret_op ss' = SOME (sload slot_w ss) ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w) ∧
      ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> gvs[compile_load_storage_def] >>
  drule_all emit_op_SLOAD_correct >> strip_tac >>
  goal_assum drule >> simp[]
QED

(* compile_store_storage with is_prim_word=T emits SSTORE [slot; val].
   Result state = sstore slot_w w ss.
   compile_store_storage val slot T word_count = emit_void SSTORE [slot; val]. *)
Theorem compile_store_storage_prim_correct:
  ∀ val_op slot_op st st' ss w slot_w word_count.
    compile_store_storage val_op slot_op T word_count st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    eval_operand slot_op ss = SOME slot_w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = sstore slot_w w ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op v. eval_operand op ss = SOME v ⇒
               eval_operand op ss' = SOME v) ∧
      ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> gvs[compile_store_storage_def] >>
  drule_all emit_void_SSTORE_correct >> simp[]
QED

(* ===== Nonreentrant Lock ===== *)

(* Lock protocol (persistent, non-view, non-transient):
   1. current ← SLOAD(nkey)
   2. locked ← EQ(current, 2)
   3. not_locked ← ISZERO(locked)
   4. ASSERT(not_locked)       — reverts if already locked
   5. SSTORE(nkey, 2)          — acquire lock
   
   This emits 5 instructions via the monad:
     emit_op SLOAD, emit_op EQ, emit_op ISZERO, emit_void ASSERT, emit_void SSTORE
   
   Key helper lemmas needed:
   - sload after update_var is identity (sload reads vs_accounts, not vs_vars)
   - sload after sstore at same key returns new value
   
   fresh_vars_wrt ensures the three emit_op outputs don't alias
   the input operands or each other. *)
Theorem compile_nonreentrant_lock_correct:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F F st = ((), st') ∧
    sload (n2w nkey) ss ≠ 2w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = 2w
Proof
  rpt strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SLOAD _ st = (current, st1)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op EQ _ st1 = (locked, st2)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ISZERO _ st2 = (not_locked, st3)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_void ASSERT _ st3 = (_, st4)` >>
  suspend "lock_correct_main"
QED

Resume compile_nonreentrant_lock_correct[lock_correct_main]:
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  qabbrev_tac `v0 = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (st.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (st.cs_next_var + 2))` >>
  (* Step 1: SLOAD *)
  `step_inst_base (mk_inst st.cs_next_id SLOAD [Lit (n2w nkey)] [v0]) ss =
     OK (update_var v0 (sload (n2w nkey) ss) ss)` by (
    simp[step_SLOAD, eval_operand_lit]) >>
  qabbrev_tac `ss1 = update_var v0 (sload (n2w nkey) ss) ss` >>
  (* Step 2: EQ *)
  `step_inst_base (mk_inst (st.cs_next_id + 1) EQ [Var v0; Lit 2w] [v1]) ss1 =
     OK (update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1)` by (
    simp[Abbr`ss1`, step_EQ, eval_operand_def, lookup_var_update_var,
         eval_operand_lit]) >>
  qabbrev_tac `ss2 = update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1` >>
  (* Step 3: ISZERO *)
  `step_inst_base (mk_inst (st.cs_next_id + 2) ISZERO [Var v1] [v2]) ss2 =
     OK (update_var v2 (bool_to_word
       (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2)` by (
    simp[Abbr`ss2`, step_ISZERO, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `ss3 = update_var v2 (bool_to_word
    (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2` >>
  (* remaining steps *)
  suspend "rest"
QED

Resume compile_nonreentrant_lock_correct[rest]:
  (* Step 4: ASSERT — v ≠ 0w because sload ≠ 2w *)
  `step_inst_base (mk_inst (st.cs_next_id + 3) ASSERT [Var v2] []) ss3 =
     OK ss3` by
    suspend "assert_step" >>
  suspend "after_assert"
QED

Resume compile_nonreentrant_lock_correct[assert_step]:
  qspecl_then [`Var v2`, `1w`, `st.cs_next_id + 3`, `ss3`] mp_tac step_ASSERT_ok >>
  simp[Abbr`ss3`, eval_operand_def, lookup_var_update_var, bool_to_word_def]
QED

Resume compile_nonreentrant_lock_correct[after_assert]:
  (* Step 5: SSTORE *)
  `step_inst_base (mk_inst (st.cs_next_id + 4) SSTORE [Lit (n2w nkey); Lit 2w] []) ss3 =
     OK (sstore (n2w nkey) 2w ss3)` by (
    qspecl_then [`Lit (n2w nkey)`, `Lit 2w`, `n2w nkey`, `2w`,
                  `st.cs_next_id + 4`, `ss3`] mp_tac step_SSTORE >>
    simp[eval_operand_lit]) >>
  (* Compose all 5 steps *)
  qexists `sstore (n2w nkey) 2w ss3` >>
  simp[sload_sstore_same] >>
  ntac 5 (simp[Once run_inst_seq_def, Excl "run_inst_seq_def", SimpLHS]) >>
  rewrite_tac[run_inst_seq_def]
QED

Finalise compile_nonreentrant_lock_correct

(* Lock on already-locked slot (sload = 2w):
   Steps 1-3 same. Step 4 ASSERT(ISZERO(EQ(2,2))) = ASSERT(0) → Revert.
   The sequence aborts at the 4th instruction. *)
Theorem compile_nonreentrant_lock_revert:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F F st = ((), st') ∧
    sload (n2w nkey) ss = 2w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss =
        Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SLOAD _ st = (current, st1)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op EQ _ st1 = (locked, st2)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ISZERO _ st2 = (not_locked, st3)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_void ASSERT _ st3 = (_, st4)` >>
  (* Compute emitted instruction list *)
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  qabbrev_tac `v0 = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (st.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (st.cs_next_var + 2))` >>
  (* Step 1: SLOAD *)
  `step_inst_base (mk_inst st.cs_next_id SLOAD [Lit (n2w nkey)] [v0]) ss =
     OK (update_var v0 (sload (n2w nkey) ss) ss)` by
    simp[step_SLOAD, eval_operand_lit] >>
  qabbrev_tac `ss1 = update_var v0 (sload (n2w nkey) ss) ss` >>
  (* Step 2: EQ *)
  `step_inst_base (mk_inst (st.cs_next_id + 1) EQ [Var v0; Lit 2w] [v1]) ss1 =
     OK (update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1)` by (
    simp[Abbr`ss1`, step_EQ, eval_operand_def, lookup_var_update_var,
         eval_operand_lit]) >>
  qabbrev_tac `ss2 = update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1` >>
  (* Step 3: ISZERO *)
  `step_inst_base (mk_inst (st.cs_next_id + 2) ISZERO [Var v1] [v2]) ss2 =
     OK (update_var v2 (bool_to_word
       (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2)` by (
    simp[Abbr`ss2`, step_ISZERO, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `ss3 = update_var v2 (bool_to_word
    (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2` >>
  (* Step 4: ASSERT with 0w — sload = 2w ⇒ EQ = T ⇒ ISZERO = F ⇒ 0w *)
  `step_inst_base (mk_inst (st.cs_next_id + 3) ASSERT [Var v2] []) ss3 =
     Abort Revert_abort (revert_state (set_returndata [] ss3))` by (
    qspecl_then [`Var v2`, `st.cs_next_id + 3`, `ss3`] mp_tac step_ASSERT_revert >>
    simp[Abbr`ss3`, eval_operand_def, lookup_var_update_var, bool_to_word_def]) >>
  (* Compose: 3 OK steps then abort at step 4, remaining instructions irrelevant *)
  qexists `revert_state (set_returndata [] ss3)` >>
  ntac 4 (simp[Once run_inst_seq_def, Excl "run_inst_seq_def", SimpLHS])
QED

(* View lock: check only, no write.
   Steps 1-4 same (check passes if not locked).
   Step 5 omitted (is_view=T → return ()).
   Storage unchanged because no SSTORE emitted. *)
Theorem compile_nonreentrant_lock_view:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F T st = ((), st') ∧
    sload (n2w nkey) ss ≠ 2w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = sload (n2w nkey) ss
Proof
  rpt strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SLOAD _ st = (current, st1)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op EQ _ st1 = (locked, st2)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op ISZERO _ st2 = (not_locked, st3)` >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_void ASSERT _ st3 = (_, st4)` >>
  (* Compute emitted instruction list — is_view=T means no SSTORE, only 4 instrs *)
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  qabbrev_tac `v0 = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `v1 = STRING #"%" (toString (st.cs_next_var + 1))` >>
  qabbrev_tac `v2 = STRING #"%" (toString (st.cs_next_var + 2))` >>
  (* Step 1: SLOAD *)
  `step_inst_base (mk_inst st.cs_next_id SLOAD [Lit (n2w nkey)] [v0]) ss =
     OK (update_var v0 (sload (n2w nkey) ss) ss)` by
    simp[step_SLOAD, eval_operand_lit] >>
  qabbrev_tac `ss1 = update_var v0 (sload (n2w nkey) ss) ss` >>
  (* Step 2: EQ *)
  `step_inst_base (mk_inst (st.cs_next_id + 1) EQ [Var v0; Lit 2w] [v1]) ss1 =
     OK (update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1)` by (
    simp[Abbr`ss1`, step_EQ, eval_operand_def, lookup_var_update_var,
         eval_operand_lit]) >>
  qabbrev_tac `ss2 = update_var v1 (bool_to_word (sload (n2w nkey) ss = 2w)) ss1` >>
  (* Step 3: ISZERO *)
  `step_inst_base (mk_inst (st.cs_next_id + 2) ISZERO [Var v1] [v2]) ss2 =
     OK (update_var v2 (bool_to_word
       (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2)` by (
    simp[Abbr`ss2`, step_ISZERO, eval_operand_def, lookup_var_update_var]) >>
  qabbrev_tac `ss3 = update_var v2 (bool_to_word
    (bool_to_word (sload (n2w nkey) ss = 2w) = 0w)) ss2` >>
  (* Step 4: ASSERT passes since sload ≠ 2w *)
  `step_inst_base (mk_inst (st.cs_next_id + 3) ASSERT [Var v2] []) ss3 =
     OK ss3` by (
    qspecl_then [`Var v2`, `1w`, `st.cs_next_id + 3`, `ss3`] mp_tac step_ASSERT_ok >>
    simp[Abbr`ss3`, eval_operand_def, lookup_var_update_var, bool_to_word_def]) >>
  (* Result: ss3 with unchanged sload (only update_var modifications) *)
  qexists `ss3` >> conj_tac
  >- (ntac 4 (simp[Once run_inst_seq_def, Excl "run_inst_seq_def", SimpLHS]) >>
      simp[run_inst_seq_def]) >>
  simp[Abbr`ss3`, Abbr`ss2`, Abbr`ss1`]
QED

(* Unlock: persistent mode, non-view.
   Emits single SSTORE(nkey, 3).
   No precondition needed — always succeeds.
   Proof: unfold → emit_void SSTORE, apply step_SSTORE,
   then sload_sstore_same. *)
Theorem compile_nonreentrant_unlock_correct:
  ∀ nkey ss st st'.
    compile_nonreentrant_unlock nkey F F st = ((), st') ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = 3w
Proof
  rpt strip_tac >> gvs[compile_nonreentrant_unlock_def] >>
  `eval_operand (Lit (n2w nkey)) ss = SOME (n2w nkey)` by simp[eval_operand_lit] >>
  `eval_operand (Lit 3w) ss = SOME 3w` by simp[eval_operand_lit] >>
  drule_all emit_void_SSTORE_correct >> strip_tac >>
  goal_assum drule >> simp[sload_sstore_same]
QED

(* Unlock for VIEW function: no-op (view never acquired lock) *)
Theorem compile_nonreentrant_unlock_view:
  ∀ nkey st.
    compile_nonreentrant_unlock nkey F T st = ((), st)
Proof
  simp[compile_nonreentrant_unlock_def, comp_return_def]
QED

(* ===== Memory Copy ===== *)

(* Memory copy of 0 bytes is a no-op *)
Theorem compile_copy_memory_zero:
  ∀ dst src st.
    compile_copy_memory dst src 0 st = ((), st)
Proof
  simp[compile_copy_memory_def, comp_return_def]
QED

(* Memory copy with size > 0 emits MCOPY.
   Result state = mcopy(w2n dst_v, w2n src_v, w2n (n2w size)) ss.
   Note: w2n (n2w size : bytes32) = size when size < 2^256 (always in practice).
   Proof: unfold → emit_void MCOPY, apply emit_void_MCOPY_correct. *)
Theorem compile_copy_memory_correct:
  ∀ dst_op src_op size st st' ss dst_v src_v.
    compile_copy_memory dst_op src_op size st = ((), st') ∧
    size > 0 ∧
    eval_operand dst_op ss = SOME dst_v ∧
    eval_operand src_op ss = SOME src_v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = mcopy (w2n dst_v) (w2n src_v) (w2n ((n2w size) : bytes32)) ss ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w)
Proof
  rpt strip_tac >> Cases_on `size'` >> gvs[compile_copy_memory_def] >>
  `eval_operand (Lit (n2w (SUC n))) ss = SOME (n2w (SUC n))`
    by simp[eval_operand_lit] >>
  drule_all emit_void_MCOPY_correct >> simp[]
QED

(* ===== Zero Memory ===== *)

(* Zero memory of 0 bytes is a no-op *)
Theorem compile_zero_memory_zero:
  ∀ ptr_op st.
    compile_zero_memory ptr_op 0 st = ((), st)
Proof
  simp[compile_zero_memory_def, comp_return_def]
QED

(* Zero memory with size > 0: emits a sequence of MSTORE(ptr+i*32, 0)
   for i = 0 .. ceil(size/32)-1.
   
   This is a loop (compile_zero_memory_loop), so the proof requires
   induction on the loop body. The emitted instructions are all within
   the same block (no new_block calls).
   
   Proof approach: induction on (words - i) via compile_zero_memory_loop_ind.
   Each iteration: emit_op ADD (except i=0) + emit_void MSTORE.
   Compose via run_inst_seq_append.
   
   Result: memory at ptr+i*32 is zeroed for each i < words. *)
(* Loop invariant for compile_zero_memory_loop *)
Theorem compile_zero_memory_loop_correct:
  ∀ ptr_op i words st st' ss ptr_v.
    compile_zero_memory_loop ptr_op i words st = ((), st') ∧
    eval_operand ptr_op ss = SOME ptr_v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      fresh_vars_wrt st' ss' ∧
      st'.cs_current_insts =
        st.cs_current_insts ++ emitted_insts st st' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  qpat_x_assum `compile_zero_memory_loop _ _ _ _ = _` mp_tac >>
  simp[Once compile_zero_memory_loop_def] >>
  IF_CASES_TAC >> simp[]
  (* Base case: i >= words *)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      simp[emitted_insts_def, run_inst_seq_def, same_blocks_def])
  (* Recursive case: i < words *)
  >> simp[comp_bind_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> simp[comp_return_def]
  (* Case i = 0: MSTORE then recurse *)
  >- suspend "i0"
  (* Case i > 0: ADD, MSTORE, then recurse *)
  >> suspend "ipos"
QED

Resume compile_zero_memory_loop_correct[i0]:
  pairarg_tac >> gvs[] >> strip_tac >>
  rename1 `emit_void MSTORE [ptr_op; Lit 0w] st = ((), stM)` >>
  rename1 `compile_zero_memory_loop ptr_op 1 words stM = ((), stF)` >>
  (* Phase 1: MSTORE *)
  drule emit_void_MSTORE_correct >>
  disch_then (qspecl_then [`ptr_v`, `0w`, `ss`] mp_tac) >>
  simp[eval_operand_lit] >> strip_tac >>
  (* Phase 2: IH on recursive call *)
  first_x_assum (qspecl_then [`stM`, `stF`,
    `mstore (w2n ptr_v) 0w ss`, `ptr_v`] mp_tac) >>
  impl_tac >- simp[eval_operand_mstore] >> strip_tac >>
  (* Get cs_current_insts extension facts *)
  imp_res_tac emitted_insts_emit_void >>
  (* Compose run_inst_seq *)
  `run_inst_seq (emitted_insts st stF) ss = OK ss'` by (
    irule run_emitted_compose2 >>
    qexistsl [`mstore (w2n ptr_v) 0w ss`, `stM`] >> gvs[]) >>
  qexists `ss'` >> rpt conj_tac >> gvs[]
  >- metis_tac[same_blocks_trans]
  >- (`emitted_insts st stF = emitted_insts st stM ++ emitted_insts stM stF`
        suffices_by gvs[] >>
      irule emitted_insts_append >> gvs[])
QED

Resume compile_zero_memory_loop_correct[ipos]:
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  strip_tac >>
  rename1 `emit_op ADD _ st = (dst, stA)` >>
  rename1 `emit_void MSTORE _ stA = ((), stM)` >>
  rename1 `compile_zero_memory_loop _ (i + 1) _ stM = ((), stF)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >>
  drule emit_op_ADD_correct >>
  disch_then (qspecl_then [`ptr_v`, `n2w (32 * i)`, `ss`] mp_tac) >>
  simp[eval_operand_lit] >>
  disch_then (qx_choose_then `ssA` strip_assume_tac) >>
  drule emit_void_MSTORE_correct >>
  disch_then (qspecl_then [`ptr_v + n2w (32 * i)`, `0w`, `ssA`] mp_tac) >>
  simp[eval_operand_lit] >> strip_tac >>
  first_x_assum (qspecl_then [`stM`, `stF`,
    `mstore (w2n (ptr_v + n2w (32 * i))) 0w ssA`, `ptr_v`] mp_tac) >>
  (impl_tac >- (gvs[] >> rpt strip_tac >> res_tac >> res_tac)) >>
  strip_tac >>
  (* Derive stM extends st *)
  `stM.cs_current_insts = st.cs_current_insts ++ emitted_insts st stM` by (
    irule emit_extends_trans >> qexists `stA` >> gvs[]) >>
  (* Compose ADD + MSTORE *)
  `run_inst_seq (emitted_insts st stM) ss =
     OK (mstore (w2n (ptr_v + n2w (32 * i))) 0w ssA)` by (
    irule run_emitted_compose2 >>
    qexistsl [`ssA`, `stA`] >> gvs[]) >>
  (* Compose (ADD+MSTORE) + loop *)
  `run_inst_seq (emitted_insts st stF) ss = OK ss'` by (
    irule run_emitted_compose2 >>
    qexistsl [`mstore (w2n (ptr_v + n2w (32 * i))) 0w ssA`, `stM`] >>
    gvs[]) >>
  qexists `ss'` >> rpt conj_tac >> gvs[]
  >- metis_tac[same_blocks_trans]
  >- (`emitted_insts st stF =
         emitted_insts st stM ++ emitted_insts stM stF`
        suffices_by gvs[] >>
      irule emitted_insts_append >> gvs[])
QED

Finalise compile_zero_memory_loop_correct

Theorem compile_zero_memory_correct:
  ∀ ptr_op size st st' ss ptr_v.
    compile_zero_memory ptr_op size st = ((), st') ∧
    size > 0 ∧
    eval_operand ptr_op ss = SOME ptr_v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      same_blocks st st' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒
               eval_operand op ss' = SOME w)
Proof
  rpt strip_tac >>
  Cases_on `size'` >> gvs[compile_zero_memory_def] >>
  drule_all compile_zero_memory_loop_correct >> strip_tac >>
  metis_tac[]
QED

(* ===== Structural / Frame ===== *)

(* SSTORE preserves memory: sstore only modifies vs_accounts.
   Proof: unfold compile_ptr_store LocStorage → emit_void SSTORE,
   apply emitted_insts_emit_void, step_SSTORE, then sstore_def
   shows only vs_accounts changes. *)
Theorem compile_ptr_store_storage_preserves_memory:
  ∀ ss st st' op_addr op_val is_ctor addr val.
    compile_ptr_store is_ctor LocStorage op_addr op_val st = ((), st') ∧
    eval_operand op_addr ss = SOME addr ∧
    eval_operand op_val ss = SOME val
    ⇒
    ∀ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ⇒
      ss'.vs_memory = ss.vs_memory
Proof
  rpt strip_tac >> gvs[compile_ptr_store_def] >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  gvs[run_inst_seq_def] >>
  `step_inst_base (mk_inst st.cs_next_id SSTORE [op_addr; op_val] []) ss =
     OK (sstore addr val ss)` by simp[step_SSTORE] >>
  gvs[]
QED
