(*
 * Context / Memory Operations Properties
 *
 * TOP-LEVEL:
 *   compile_ptr_load_memory_correct   — MLOAD returns encoded value
 *   compile_ptr_store_memory_correct  — MSTORE updates memory correctly
 *   compile_load_storage_prim_correct — SLOAD retrieves storage value
 *   compile_store_storage_prim_correct — SSTORE updates storage value
 *   compile_nonreentrant_lock_correct — lock sets storage slot
 *   compile_nonreentrant_unlock_correct — unlock resets storage slot
 *   compile_copy_memory_zero          — 0-byte copy is no-op
 *   compile_zero_memory_zero          — 0-byte zero is no-op
 *
 * Source: context.py (VenomCompilerContext)
 * Lowering: contextScript.sml
 *)

Theory contextProps
Ancestors
  exprLoweringProps
  context compileEnv
  venomExecSemantics venomState
  valueEncoding

(* ===== Pointer Load/Store ===== *)

(* Loading a word from memory produces the stored value *)
Theorem compile_ptr_load_memory_correct:
  ∀ ss st op st' offset v is_ctor.
    compile_ptr_load is_ctor LocMemory (Lit (n2w offset)) st = (op, st') ∧
    mload offset ss = val_to_w256 v
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v)
Proof
  cheat
QED

(* Loading a word from storage *)
Theorem compile_ptr_load_storage_correct:
  ∀ ss st op st' slot is_ctor.
    compile_ptr_load is_ctor LocStorage (Lit slot) st = (op, st') ∧
    sload slot ss = w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  cheat
QED

(* Storing a word to memory *)
Theorem compile_ptr_store_memory_correct:
  ∀ ss st st' op_addr op_val offset v is_ctor.
    compile_ptr_store is_ctor LocMemory op_addr op_val st = ((), st') ∧
    eval_operand op_addr ss = SOME (n2w offset) ∧
    eval_operand op_val ss = SOME (val_to_w256 v)
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      mload offset ss' = val_to_w256 v
Proof
  cheat
QED

(* ===== Storage Load/Store ===== *)

(* Primitive storage load via SLOAD *)
Theorem compile_load_storage_prim_correct:
  ∀ slot_op ss st op st'.
    compile_load_storage slot_op T 1 32 st = (op, st') ∧
    eval_operand slot_op ss = SOME slot_w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (sload slot_w ss)
Proof
  cheat
QED

(* Primitive storage store via SSTORE *)
Theorem compile_store_storage_prim_correct:
  ∀ val_op slot_op ss st st'.
    compile_store_storage val_op slot_op T 1 st = ((), st') ∧
    eval_operand val_op ss = SOME w ∧
    eval_operand slot_op ss = SOME slot_w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      ss' = sstore slot_w w ss
Proof
  cheat
QED

(* ===== Nonreentrant Lock ===== *)

(* Lock: persistent mode, non-view.
   Checks slot ≠ 2 (not already locked), then writes 2.
   Reentrancy protocol: 1=unlocked(initial), 2=locked, 3=unlocked(post-call). *)
Theorem compile_nonreentrant_lock_correct:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F F st = ((), st') ∧
    sload (n2w nkey) ss ≠ 2w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = 2w
Proof
  cheat
QED

(* Lock on already-locked slot (value = 2) reverts *)
Theorem compile_nonreentrant_lock_revert:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F F st = ((), st') ∧
    sload (n2w nkey) ss = 2w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss =
        Abort Revert_abort ss'
Proof
  cheat
QED

(* Lock for VIEW function: checks slot ≠ 2 but doesn't write *)
Theorem compile_nonreentrant_lock_view:
  ∀ nkey ss st st'.
    compile_nonreentrant_lock nkey F T st = ((), st') ∧
    sload (n2w nkey) ss ≠ 2w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = sload (n2w nkey) ss
Proof
  cheat
QED

(* Unlock: persistent mode, non-view. Writes 3 (unlocked post-call). *)
Theorem compile_nonreentrant_unlock_correct:
  ∀ nkey ss st st'.
    compile_nonreentrant_unlock nkey F F st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      sload (n2w nkey) ss' = 3w
Proof
  cheat
QED

(* Unlock for VIEW function: no-op (view never acquired lock) *)
Theorem compile_nonreentrant_unlock_view:
  ∀ nkey st.
    compile_nonreentrant_unlock nkey F T st = ((), st)
Proof
  simp[compile_nonreentrant_unlock_def]
QED

(* ===== Memory Copy ===== *)

(* Memory copy of 0 bytes is a no-op *)
Theorem compile_copy_memory_zero:
  ∀ dst src st.
    compile_copy_memory dst src 0 st = ((), st)
Proof
  simp[compile_copy_memory_def]
QED

(* Memory copy correctness *)
Theorem compile_copy_memory_correct:
  ∀ dst_op src_op size ss st st'.
    compile_copy_memory dst_op src_op size st = ((), st') ∧
    size > 0
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* ===== Zero Memory ===== *)

(* Zero memory of 0 bytes is a no-op *)
Theorem compile_zero_memory_zero:
  ∀ ptr_op st.
    compile_zero_memory ptr_op 0 st = ((), st)
Proof
  simp[compile_zero_memory_def]
QED

(* Zero memory correctness *)
Theorem compile_zero_memory_correct:
  ∀ ptr_op size ss st st'.
    compile_zero_memory ptr_op size st = ((), st') ∧
    size > 0
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* ===== Structural ===== *)

(* SSTORE preserves memory *)
Theorem compile_ptr_store_storage_preserves_memory:
  ∀ ss st st' op_addr op_val is_ctor.
    compile_ptr_store is_ctor LocStorage op_addr op_val st = ((), st') ⇒
    ∀ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ⇒
      ss'.vs_memory = ss.vs_memory
Proof
  cheat
QED
