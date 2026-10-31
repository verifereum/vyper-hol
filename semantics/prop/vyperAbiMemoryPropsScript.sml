(* Boundary facts for consumers migrating from eager eval_exprs ABI arguments.
   These are memory/state framing facts, not an ABI lowering simulation proof. *)
Theory vyperAbiMemoryProps
Ancestors
  vyperAbiOperand vyperState vyperAST vyperValue vyperStorage
  vfmState list rich_list pair option

Theorem unwrap_complex_memory_keeps_address:
  ¬abi_primitive tv ⇒
  unwrap_abi_operand cx (AbiMemory token off tv) = return (AbiMemory token off tv)
Proof
  simp[unwrap_abi_operand_def]
QED

Theorem pop_memory_write_footprint:
  abi_operation_writes (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) PopOp =
  SOME [(0,n2w (LENGTH vs))]
Proof
  simp[abi_operation_writes_def]
QED

Theorem capture_abi_memory_frame:
  capture_abi_memory cx id tv v st = (result,rt) ⇒
  rt.scopes = st.scopes ∧ rt.accounts = st.accounts ∧
  rt.tStorage = st.tStorage ∧ rt.immutables = st.immutables ∧
  rt.logs = st.logs ∧ rt.pending_deletions = st.pending_deletions ∧
  rt.outcomes = st.outcomes ∧ rt.requests = st.requests
Proof
  rw[capture_abi_memory_def, AllCaseEqs(), return_def, raise_def] >> simp[]
QED

Theorem capture_abi_memory_at_cell:
  encode_value root v = SOME root_writes /\
  encode_value tv child = SOME writes /\
  capture_abi_memory_at cx id root v off tv child st = (INL token,rt) ==>
  token = LENGTH st.abi_memory /\
  oEL token rt.abi_memory = SOME ((cx.stk,id),
    apply_writes (n2w off) writes (apply_writes 0w root_writes empty_storage)) /\
  TAKE token rt.abi_memory = st.abi_memory
Proof
  simp[capture_abi_memory_at_def, return_def] >> strip_tac >> gvs[] >>
  simp[oEL_THM, EL_APPEND_EQN, TAKE_LENGTH_APPEND]
QED

Theorem write_abi_memory_frame:
  write_abi_memory cx id tv v subs ao st = (result,rt) ⇒
  rt.scopes = st.scopes ∧ rt.accounts = st.accounts ∧
  rt.tStorage = st.tStorage ∧ rt.immutables = st.immutables ∧
  rt.logs = st.logs ∧ rt.pending_deletions = st.pending_deletions ∧
  rt.outcomes = st.outcomes ∧ rt.requests = st.requests
Proof
  rw[write_abi_memory_def, write_abi_memory_child_def,
     AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem write_abi_memory_scopes[simp]:
  (SND (write_abi_memory cx id tv v subs ao st)).scopes = st.scopes
Proof
  Cases_on `write_abi_memory cx id tv v subs ao st` >>
  drule write_abi_memory_frame >> simp[]
QED

(* No capture for this local: the writer is exactly the identity computation. *)
Theorem write_abi_memory_irrelevant:
  ¬EXISTS (λ(key,mem). key = (cx.stk,id)) st.abi_memory ⇒
  write_abi_memory cx id tv v subs ao st = (INL (),st)
Proof
  simp[write_abi_memory_def, return_def]
QED

Theorem write_abi_memory_empty:
  st.abi_memory = [] ⇒
  write_abi_memory cx id tv v subs ao st = (INL (),st)
Proof
  simp[write_abi_memory_def, return_def]
QED

Theorem capture_abi_immutable_frame:
  capture_abi_immutable cx src id tv v st = (result,rt) ⇒
  rt.scopes = st.scopes ∧ rt.accounts = st.accounts ∧
  rt.tStorage = st.tStorage ∧ rt.immutables = st.immutables ∧
  rt.logs = st.logs ∧ rt.pending_deletions = st.pending_deletions ∧
  rt.outcomes = st.outcomes ∧ rt.requests = st.requests ∧
  rt.abi_memory = st.abi_memory
Proof
  rw[capture_abi_immutable_def, AllCaseEqs(), return_def, raise_def] >> simp[]
QED

Theorem write_abi_immutables_frame:
  write_abi_immutables cx src id tv v subs ao st = (result,rt) ⇒
  rt.scopes = st.scopes ∧ rt.accounts = st.accounts ∧
  rt.tStorage = st.tStorage ∧ rt.immutables = st.immutables ∧
  rt.logs = st.logs ∧ rt.pending_deletions = st.pending_deletions ∧
  rt.outcomes = st.outcomes ∧ rt.requests = st.requests ∧
  rt.abi_memory = st.abi_memory
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem write_abi_immutables_scopes[simp]:
  (SND (write_abi_immutables cx src id tv v subs ao st)).scopes = st.scopes
Proof
  Cases_on `write_abi_immutables cx src id tv v subs ao st` >>
  drule write_abi_immutables_frame >> simp[]
QED

Theorem unwrap_immutable_copies_before_staging:
  unwrap_abi_operand cx (AbiImmutable token off tv) st = (INL arg,rt) ==>
  ?v. arg = AbiSnapshot v /\ rt = st /\
      read_abi_operand cx (AbiImmutable token off tv) st = (INL v,st)
Proof
  rw[unwrap_abi_operand_def, read_abi_operand_def, bind_def,
     lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, AllCaseEqs(), return_def, raise_def]
QED

Theorem release_abi_captures_frame:
  release_abi_captures mark st = (INL (), st with <|
    abi_memory := TAKE (FST mark) st.abi_memory;
    abi_immutables := TAKE (SND mark) st.abi_immutables |>)
Proof
  simp[release_abi_captures_def, return_def]
QED

Theorem release_abi_captures_preserves_older_cells:
  token < FST mark /\ token < LENGTH st.abi_memory ==>
  oEL token (SND (release_abi_captures mark st)).abi_memory =
    oEL token st.abi_memory
Proof
  simp[release_abi_captures_def, return_def, oEL_THM,
    LENGTH_TAKE_EQ, EL_TAKE] >> rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem release_abi_captures_preserves_older_immutable_cells:
  token < SND mark /\ token < LENGTH st.abi_immutables ==>
  oEL token (SND (release_abi_captures mark st)).abi_immutables =
    oEL token st.abi_immutables
Proof
  simp[release_abi_captures_def, return_def, oEL_THM,
    LENGTH_TAKE_EQ, EL_TAKE] >> rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

Theorem release_abi_memory_frame:
  release_abi_memory mark st =
    (INL (), st with abi_memory := TAKE mark st.abi_memory)
Proof
  simp[release_abi_memory_def, return_def]
QED
