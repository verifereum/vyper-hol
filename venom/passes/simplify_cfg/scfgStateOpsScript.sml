(* 
 * Simplify-CFG State Operation Lemmas
 *
 * State-operation preservation for state_equiv_cfg.
 *)

Theory scfgStateOps
Ancestors
  scfgDefs stateEquiv venomState finite_map

(* ===== State Operations Preserve state_equiv_cfg ===== *)

Theorem update_var_state_equiv_cfg:
  !x v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem update_var_state_equiv_cfg_eq:
  !x v1 v2 s1 s2.
    state_equiv_cfg s1 s2 /\ v1 = v2 ==>
    state_equiv_cfg (update_var x v1 s1) (update_var x v2 s2)
Proof
  rpt strip_tac >> gvs[] >> irule update_var_state_equiv_cfg >> simp[]
QED

Theorem memory_length_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    LENGTH s1.vs_memory = LENGTH s2.vs_memory
Proof
  rw[state_equiv_cfg_def]
QED

Theorem msize_val_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    n2w (32 * ((LENGTH s1.vs_memory + 31) DIV 32)) =
    n2w (32 * ((LENGTH s2.vs_memory + 31) DIV 32))
Proof
  rw[state_equiv_cfg_def]
QED

Theorem msize_update_var_state_equiv_cfg:
  !out s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out (n2w (32 * ((LENGTH s1.vs_memory + 31) DIV 32))) s1)
      (update_var out (n2w (32 * ((LENGTH s2.vs_memory + 31) DIV 32))) s2)
Proof
  rpt strip_tac >>
  irule update_var_state_equiv_cfg_eq >>
  simp[msize_val_state_equiv_cfg]
QED

Theorem returndata_length_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    LENGTH s1.vs_returndata = LENGTH s2.vs_returndata
Proof
  rw[state_equiv_cfg_def]
QED

Theorem call_ctx_state_equiv_cfg:
  !s1 s2. state_equiv_cfg s1 s2 ==> s1.vs_call_ctx = s2.vs_call_ctx
Proof
  rw[state_equiv_cfg_def]
QED

Theorem call_ctx_caller_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    w2w s1.vs_call_ctx.cc_caller = w2w s2.vs_call_ctx.cc_caller
Proof
  rw[state_equiv_cfg_def]
QED

Theorem call_ctx_address_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    w2w s1.vs_call_ctx.cc_address = w2w s2.vs_call_ctx.cc_address
Proof
  rw[state_equiv_cfg_def]
QED

Theorem call_ctx_callvalue_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_call_ctx.cc_callvalue = s2.vs_call_ctx.cc_callvalue
Proof
  rw[state_equiv_cfg_def]
QED

Theorem call_ctx_gas_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    n2w s1.vs_call_ctx.cc_gas = n2w s2.vs_call_ctx.cc_gas
Proof
  rw[state_equiv_cfg_def]
QED

Theorem calldata_length_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    LENGTH s1.vs_call_ctx.cc_calldata = LENGTH s2.vs_call_ctx.cc_calldata
Proof
  rw[state_equiv_cfg_def]
QED

Theorem calldata_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_call_ctx.cc_calldata = s2.vs_call_ctx.cc_calldata
Proof
  rw[state_equiv_cfg_def]
QED

Theorem calldataload_val_state_equiv_cfg:
  !offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    word_of_bytes T 0w
      (TAKE 32
        (DROP (w2n offset) s1.vs_call_ctx.cc_calldata ⧺ REPLICATE 32 0w)) =
    word_of_bytes T 0w
      (TAKE 32
        (DROP (w2n offset) s2.vs_call_ctx.cc_calldata ⧺ REPLICATE 32 0w))
Proof
  rw[state_equiv_cfg_def]
QED

Theorem calldataload_update_var_state_equiv_cfg:
  !out offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out
        (word_of_bytes T 0w
          (TAKE 32
            (DROP (w2n offset) s1.vs_call_ctx.cc_calldata ⧺ REPLICATE 32 0w))) s1)
      (update_var out
        (word_of_bytes T 0w
          (TAKE 32
            (DROP (w2n offset) s2.vs_call_ctx.cc_calldata ⧺ REPLICATE 32 0w))) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE]
QED

Theorem calldatacopy_state_equiv_cfg:
  !destOffset size_val offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (write_memory_with_expansion (w2n destOffset)
        (TAKE (w2n size_val)
          (DROP (w2n offset) s1.vs_call_ctx.cc_calldata ⧺
           REPLICATE (w2n size_val) 0w)) s1)
      (write_memory_with_expansion (w2n destOffset)
        (TAKE (w2n size_val)
          (DROP (w2n offset) s2.vs_call_ctx.cc_calldata ⧺
           REPLICATE (w2n size_val) 0w)) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, write_memory_with_expansion_def,
     lookup_var_def]
QED

Theorem update_var_call_ctx_state_equiv_cfg:
  !out f s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var out (f s1.vs_call_ctx) s1)
                    (update_var out (f s2.vs_call_ctx) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem tx_ctx_state_equiv_cfg:
  !s1 s2. state_equiv_cfg s1 s2 ==> s1.vs_tx_ctx = s2.vs_tx_ctx
Proof
  rw[state_equiv_cfg_def]
QED

Theorem tx_ctx_origin_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    w2w s1.vs_tx_ctx.tc_origin = w2w s2.vs_tx_ctx.tc_origin
Proof
  rw[state_equiv_cfg_def]
QED

Theorem tx_ctx_gasprice_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_tx_ctx.tc_gasprice = s2.vs_tx_ctx.tc_gasprice
Proof
  rw[state_equiv_cfg_def]
QED

Theorem tx_ctx_chainid_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_tx_ctx.tc_chainid = s2.vs_tx_ctx.tc_chainid
Proof
  rw[state_equiv_cfg_def]
QED

Theorem update_var_tx_ctx_state_equiv_cfg:
  !out f s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var out (f s1.vs_tx_ctx) s1)
                    (update_var out (f s2.vs_tx_ctx) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem block_ctx_state_equiv_cfg:
  !s1 s2. state_equiv_cfg s1 s2 ==> s1.vs_block_ctx = s2.vs_block_ctx
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_coinbase_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    w2w s1.vs_block_ctx.bc_coinbase = w2w s2.vs_block_ctx.bc_coinbase
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_timestamp_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_timestamp = s2.vs_block_ctx.bc_timestamp
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_number_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_number = s2.vs_block_ctx.bc_number
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_prevrandao_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_prevrandao = s2.vs_block_ctx.bc_prevrandao
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_gaslimit_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_gaslimit = s2.vs_block_ctx.bc_gaslimit
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_basefee_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_basefee = s2.vs_block_ctx.bc_basefee
Proof
  rw[state_equiv_cfg_def]
QED

Theorem block_ctx_blobbasefee_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    s1.vs_block_ctx.bc_blobbasefee = s2.vs_block_ctx.bc_blobbasefee
Proof
  rw[state_equiv_cfg_def]
QED

Theorem update_var_block_ctx_state_equiv_cfg:
  !out f s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (update_var out (f s1.vs_block_ctx) s1)
                    (update_var out (f s2.vs_block_ctx) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem accounts_state_equiv_cfg:
  !s1 s2. state_equiv_cfg s1 s2 ==> s1.vs_accounts = s2.vs_accounts
Proof
  rw[state_equiv_cfg_def]
QED

Theorem selfbalance_update_var_state_equiv_cfg:
  !out s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out
        (n2w (lookup_account s1.vs_call_ctx.cc_address s1.vs_accounts).balance) s1)
      (update_var out
        (n2w (lookup_account s2.vs_call_ctx.cc_address s2.vs_accounts).balance) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE]
QED

Theorem balance_update_var_state_equiv_cfg:
  !out addr s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out
        (n2w (lookup_account (w2w addr) s1.vs_accounts).balance) s1)
      (update_var out
        (n2w (lookup_account (w2w addr) s2.vs_accounts).balance) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE]
QED

Theorem blockhash_update_var_state_equiv_cfg:
  !out blocknum s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out (s1.vs_block_ctx.bc_blockhash (w2n blocknum)) s1)
      (update_var out (s2.vs_block_ctx.bc_blockhash (w2n blocknum)) s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE]
QED

Theorem returndata_state_equiv_cfg:
  !s1 s2. state_equiv_cfg s1 s2 ==> s1.vs_returndata = s2.vs_returndata
Proof
  rw[state_equiv_cfg_def]
QED

Theorem returndatasize_update_var_state_equiv_cfg:
  !out s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg
      (update_var out (n2w (LENGTH s1.vs_returndata)) s1)
      (update_var out (n2w (LENGTH s2.vs_returndata)) s2)
Proof
  rpt strip_tac >>
  drule_all returndata_length_state_equiv_cfg >> strip_tac >>
  simp[] >>
  irule update_var_state_equiv_cfg >> simp[]
QED

Theorem mload_state_equiv_cfg:
  !offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    mload offset s1 = mload offset s2
Proof
  rw[mload_def, state_equiv_cfg_def]
QED

Theorem mstore_state_equiv_cfg:
  !offset v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (mstore offset v s1) (mstore offset v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, mstore_def, lookup_var_def]
QED

Theorem sload_state_equiv_cfg:
  !key s1 s2.
    state_equiv_cfg s1 s2 ==>
    sload key s1 = sload key s2
Proof
  rw[sload_def, state_equiv_cfg_def]
QED

Theorem sstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (sstore key v s1) (sstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, sstore_def, lookup_var_def]
QED

Theorem tload_state_equiv_cfg:
  !key s1 s2.
    state_equiv_cfg s1 s2 ==>
    tload key s1 = tload key s2
Proof
  rw[tload_def, state_equiv_cfg_def]
QED

Theorem tstore_state_equiv_cfg:
  !key v s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (tstore key v s1) (tstore key v s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, tstore_def, lookup_var_def]
QED

Theorem write_memory_with_expansion_state_equiv_cfg:
  !offset bytes s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (write_memory_with_expansion offset bytes s1)
                    (write_memory_with_expansion offset bytes s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem jump_to_state_equiv_cfg:
  !lbl1 lbl2 s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (jump_to lbl1 s1) (jump_to lbl2 s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem halt_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, halt_state_def, lookup_var_def]
QED

Theorem revert_state_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, revert_state_def, lookup_var_def]
QED

Theorem returndatacopy_state_equiv_cfg:
  !destOffset size_val offset s1 s2.
    state_equiv_cfg s1 s2 ==>
    result_equiv_cfg
      (if w2n offset + w2n size_val > LENGTH s1.vs_returndata then
         Revert (revert_state s1)
       else
         OK
           (write_memory_with_expansion (w2n destOffset)
              (TAKE (w2n size_val) (DROP (w2n offset) s1.vs_returndata)) s1))
      (if w2n offset + w2n size_val > LENGTH s2.vs_returndata then
         Revert (revert_state s2)
       else
         OK
           (write_memory_with_expansion (w2n destOffset)
              (TAKE (w2n size_val) (DROP (w2n offset) s2.vs_returndata)) s2))
Proof
  rpt strip_tac >>
  `LENGTH s1.vs_returndata = LENGTH s2.vs_returndata` by
    (irule returndata_length_state_equiv_cfg >> simp[]) >>
  `(w2n offset + w2n size_val > LENGTH s2.vs_returndata) =
   (w2n offset + w2n size_val > LENGTH s1.vs_returndata)` by simp[] >>
  simp[] >>
  Cases_on `w2n offset + w2n size_val > LENGTH s1.vs_returndata`
  >- simp[result_equiv_cfg_def, revert_state_state_equiv_cfg]
  >- (
    simp[result_equiv_cfg_def] >>
    drule_all returndata_state_equiv_cfg >> strip_tac >>
    simp[] >>
    irule write_memory_with_expansion_state_equiv_cfg >>
    simp[]
  )
QED

Theorem next_inst_state_equiv_cfg:
  !s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (next_inst s1) (next_inst s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, next_inst_def, lookup_var_def]
QED

(* Asymmetric jump_to lemmas: state_equiv_cfg ignores prev_bb/current_bb/inst_idx
   so jump_to on one side preserves equivalence *)
Theorem state_equiv_cfg_jump_to_left:
  !lbl s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg (jump_to lbl s1) s2
Proof
  rw[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

Theorem state_equiv_cfg_jump_to_right:
  !lbl s1 s2.
    state_equiv_cfg s1 s2 ==>
    state_equiv_cfg s1 (jump_to lbl s2)
Proof
  rw[state_equiv_cfg_def, var_equiv_def, jump_to_def, lookup_var_def]
QED

val _ = export_theory();
