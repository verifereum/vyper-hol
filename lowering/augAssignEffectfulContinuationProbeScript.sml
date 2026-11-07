(* Conditional execution equations for the saved fixed-array bt.  The
   premises describe executions; they do not assert a complete program. *)
Theory augAssignEffectfulContinuationProbe
Ancestors
  augAssignEffectfulOutcomeProbe vyperInterpreter vyperState
  vyperStorageBackend vyperStorage vyperValueOperation
  venomExecSemantics venomState venomInst emitHelper exprLowering finite_map
  arithmeticProps

Theorem saved_fixed_index_after_effect:
  eval_base_place cx bt es =
    (INL (PlaceR (StoragePlace tr 1w
      (ArrayTV (BaseTV (UintT 8)) (Fixed 1)))), mid) /\
  eval_expr cx key mid = (INL (Value (IntV 0)), post) ==>
  eval_target_place cx (SubscriptTarget bt key) es =
    (INL (StoragePlace tr 1w (BaseTV (UintT 8))), post)
Proof
  strip_tac >>
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  fs[bind_def, read_result_def, return_def, extend_place_def,
     extend_storage_place_def, resolve_array_element_def,
     ignore_bind_def, check_def, get_place_def] >>
  simp[assert_def, return_def, bind_def, ignore_bind_def,
       get_place_def, wordsTheory.WORD_ADD_0]
QED

Theorem saved_scalar_read_noncanonical:
  get_storage cx post tr = update_storage 1w 256w (\k. 0w) ==>
  read_place cx (StoragePlace tr 1w (BaseTV (UintT 8))) post =
    (INL (IntV 0), post)
Proof
  strip_tac >>
  simp[read_place_def, read_storage_slot_def, get_storage_backend_eq,
       bind_def, lift_option_def, return_def] >>
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED

Theorem saved_scalar_type_after_effect:
  place_type_value cx (StoragePlace tr 1w (BaseTV (UintT 8))) post =
    (INL (BaseTV (UintT 8)), post)
Proof
  simp[place_type_value_def, return_def]
QED

(* This is the actual safe-add compiler's failure theorem specialized to
   the raw saved word, not an assertion that a full program reaches it. *)
Theorem saved_raw_uint8_add_reverts:
  compile_safe_add x y (BaseT (UintT 8)) st = (op, st') /\
  eval_operand x ss = SOME 256w /\
  eval_operand y ss = SOME 1w /\
  fresh_vars_wrt st ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  `type_bits (BaseT (UintT 8)) < 256 /\
   ~in_type_range (BaseT (UintT 8))
     (math_val (BaseT (UintT 8)) ((256w:bytes32) + 1w))` by
    (EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC) >>
  metis_tac[compile_safe_add_out_of_range]
QED

Theorem saved_decoded_uint8_add_succeeds:
  evaluate_binop (Unsigned 8) (BaseTV (UintT 8)) Add (IntV 0) (IntV 1) =
    INL (IntV 1)
Proof
  EVAL_TAC >> simp[]
QED

(* Admission ledger for C1.4.3.2 -- candidate STILL OPEN, not a full
   counterexample and not an external-precondition conclusion.

   Checked here: saved_fixed_index_after_effect returns scalar slot 1
   after the key effect, without revisiting the outer dynamic header;
   saved_scalar_read_noncanonical decodes raw 256 as IntV 0; the place
   type remains Uint8; source addition returns 1.  The actual safe-add
   compiler reverts for operands 256 and 1 (saved_raw_uint8_add_reverts).

   Emission audit: exprLowering compile_get_target_ptr first saves the
   recursive base result, then lowers the index. For the saved Fixed 1
   inner array, compile_array_subscript uses literal length 1, not a
   fresh storage header. Index 0 passes, data_ptr is the saved base,
   and the offset is zero. stmtLowering compile_stmt AugAssign emits
   SLOAD/TLOAD at that pointer, lowers RHS, then compile_binop, then
   SSTORE/TSTORE. No decode/mask occurs between current load and binop.
   Uint8 Add emits ADD then unsigned GT against 255, ISZERO, ASSERT;
   sum 257 therefore aborts. This audit is not a checked complete emitted
   target execution or a whole-statement execution theorem.

   Outcome admission audit: vyperCallOutcome.take_call_outcome accepts
   the next outcome for a non-precompile request subject to runtime
   account typing. adopt_call_outcome_equation installs accounts and
   transient storage wholesale on successful NONSTATIC calls. Static
   calls and computed precompiles cannot implement this candidate.
   accounts_runtime_well_typed constrains balances/code lengths, not
   dead payloads. expr_sim_inv additionally requires bounded return data,
   oracle_storage_ok, and initial contract_storage_well_formed;
   oracle_storage_ok checks every outcome's contract storage. The prior
   empty_outer_array_noncanonical_payload theorem checks just the one
   empty dynamic region, NOT all these global obligations. A uint index
   returning nonstatic ExtCall with pure arguments is not excluded just
   by call_operands_effect_root (it checks effects in DROP 1 args).

   Still unproved: concrete supported tops and lowering/body_inv pins;
   full type_stmt/env and expr_sim_inv including layout and all outcomes;
   a well-typed nonstatic external-call index returning ABI zero, its
   target_indices_pre, and target_case for the actual compiled function;
   initial state_rel, fn_has_code, fresh/gas and request/outcome alignment;
   successful source store and gas-admissibility of the entire statement;
   complete emitted target/load/RHS/binop path reaching the checked abort;
   and exclusion of gas_outcome's exemption alternative. stmt_exit only
   relates an Abort to source errors, not source INL (), but that alone
   does not exclude the gas_exempt_cert alternative. No claim of failure
   of stmt_frag follows until these reachability/observation obligations
   are discharged. Next boundary must either exclude the nonstatic
   outcome using a frozen premise, or verify this concrete full path;
   a general selected-word history lemma is not justified by this audit.
*)
