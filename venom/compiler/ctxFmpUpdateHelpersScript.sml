(* Computational interface for replacing the three free-memory-pointer fields.
   No execution relation is defined here; consumers use explicit record updates.
   Result mapping is owned by instIdxIndep (exec_result_map_def). *)
Theory ctxFmpUpdateHelpers
Ancestors
  instIdxIndep venomExecSemantics venomState
Libs
  listTheory

Theorem eval_operand_fmp_update:
  !op s p i c.
    eval_operand op
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_fmp_update:
  !ops s p i c.
    eval_operands ops
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, eval_operand_fmp_update]
QED

Theorem update_var_fmp_update:
  !x v s p i c.
    update_var x v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (update_var x v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[update_var_def]
QED

Theorem read_memory_fmp_update:
  !off sz s p i c.
    read_memory off sz
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    read_memory off sz s
Proof
  simp[read_memory_def]
QED

Theorem write_memory_fmp_update:
  !off bytes s p i c.
    write_memory off bytes
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (write_memory off bytes s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[write_memory_def]
QED

Theorem write_memory_with_expansion_fmp_update:
  !off bytes s p i c.
    write_memory_with_expansion off bytes
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (write_memory_with_expansion off bytes s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem mload_fmp_update:
  !off s p i c.
    mload off
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    mload off s
Proof
  simp[mload_def]
QED

Theorem mstore_fmp_update:
  !off v s p i c.
    mstore off v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (mstore off v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[mstore_def]
QED

Theorem mstore8_fmp_update:
  !off v s p i c.
    mstore8 off v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (mstore8 off v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[mstore8_def]
QED

Theorem istore_fmp_update:
  !off v s p i c.
    istore off v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (istore off v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[istore_def, mstore_fmp_update]
QED

Theorem mcopy_fmp_update:
  !dst src sz s p i c.
    mcopy dst src sz
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (mcopy dst src sz s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[mcopy_def, write_memory_with_expansion_fmp_update]
QED

Theorem sload_fmp_update:
  !k s p i c.
    sload k
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    sload k s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_fmp_update:
  !k s p i c.
    tload k
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    tload k s
Proof
  simp[tload_def, contract_transient_def]
QED

Theorem sstore_fmp_update:
  !k v s p i c.
    sstore k v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (sstore k v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[sstore_def]
QED

Theorem tstore_fmp_update:
  !k v s p i c.
    tstore k v
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (tstore k v s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[tstore_def]
QED

Theorem jump_to_fmp_update:
  !lbl s p i c.
    jump_to lbl
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (jump_to lbl s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[jump_to_def]
QED

Theorem next_inst_fmp_update:
  !s p i c.
    next_inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (next_inst s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[next_inst_def]
QED

Theorem halt_state_fmp_update:
  !s p i c.
    halt_state
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (halt_state s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[halt_state_def]
QED

Theorem revert_state_fmp_update:
  !s p i c.
    revert_state
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (revert_state s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[revert_state_def]
QED

Theorem set_returndata_fmp_update:
  !rd s p i c.
    set_returndata rd
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
    (set_returndata rd s) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[set_returndata_def]
QED

Theorem foldl_update_var_fmp_update:
  !kvs s p i c.
    FOLDL (\s (k,v). update_var k v s)
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) kvs =
    (FOLDL (\s (k,v). update_var k v s) s kvs) with
      <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  Induct >> simp[] >> Cases_on `h` >> rpt gen_tac >>
  first_x_assum (qspecl_then [`update_var q r s`, `p`, `i`, `c`] mp_tac) >>
  simp[update_var_def]
QED
