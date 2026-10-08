(* TASK026: arbitrary oracle bookkeeping at source entry, not consumption. *)
Theory vyperOracleInitialStateTest
Ancestors
  list option vyperState vyperInterpreter vyperTypeInvariants vyperTypeInitialState

(* The old projections, including storage and immutable tables, are unchanged;
 * both new fields retain exactly the arbitrary supplied values. *)
Theorem oracle_initial_state_projections:
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).accounts = am.accounts /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).tStorage = am.tStorage /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).scopes = scs /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).immutables = am.immutables /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).logs = am.logs /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).outcomes = orc /\
  (initial_state am scs with <|outcomes := orc; requests := rqs|>).requests = rqs
Proof
  simp[initial_state_def]
QED

Theorem oracle_initial_state_typing_modes:
  machine_well_typed am /\ scope_well_typed scope ==>
  state_well_typed (initial_state am [scope] with <|outcomes := NONE; requests := rqs|>) /\
  state_well_typed (initial_state am [scope] with <|outcomes := SOME os; requests := rqs|>) /\
  accounts_well_typed
    (initial_state am [scope] with <|outcomes := SOME os; requests := rqs|>).accounts
Proof
  simp[initial_state_def, machine_well_typed_def, state_well_typed_def]
QED

Theorem oracle_initial_state_invariant_modes:
  (env_consistent env cx
     (initial_state am scs with <|outcomes := NONE; requests := rqs|>) <=>
   env_consistent env cx (initial_state am scs)) /\
  (env_consistent env cx
     (initial_state am scs with <|outcomes := SOME os; requests := rqs|>) <=>
   env_consistent env cx (initial_state am scs))
Proof
  simp[]
QED

(* Exercise the complete arbitrary initial state, including arbitrary
 * nonempty prior requests/outcomes. SOME still does not consume an outcome. *)
Theorem oracle_initial_state_inert_modes:
  let st = initial_state am scs with <|outcomes := orc; requests := rqs|> in
    eval_expr empty_evaluation_context
      (Call NoneT Send
        [Literal (BaseT AddressT) (BytesL (REPLICATE 20 0w));
         Literal (BaseT (UintT 256)) (IntL 0)] NONE) st =
      (INL (Value NoneV), st) /\
    eval_expr empty_evaluation_context
      (Call NoneT (ExtCall T ("unused", [], NoneT)) [] NONE) st =
      (INR (Error (TypeError "ExtCall no target")), st)
Proof
  EVAL_TAC >> simp[return_def, transfer_value_def]
QED
