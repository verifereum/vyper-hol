(* ABI-only state changes preserve the established typing observations.
   These facts do not assert that arbitrary arena contents are well typed;
   the address/cell invariant is separately defined in vyperAbiOperandTyping. *)
Theory vyperAbiStateTyping
Ancestors
  list rich_list pair arithmetic vyperAST vyperState vyperAbiOperand
  vyperAbiMemoryProps vyperTypeInvariants

Theorem abi_typing_observations_frame:
  rt.scopes = st.scopes /\ rt.immutables = st.immutables /\
  rt.accounts = st.accounts ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx. env_consistent env cx rt <=> env_consistent env cx st) /\
  rt.accounts = st.accounts
Proof
  strip_tac >>
  simp[state_well_typed_def, env_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def]
QED

Theorem capture_abi_memory_typing_frame:
  capture_abi_memory cx id tv v st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx'. env_consistent env cx' rt <=> env_consistent env cx' st) /\
  rt.accounts = st.accounts /\ rt.abi_immutables = st.abi_immutables
Proof
  strip_tac >> drule capture_abi_memory_frame >> strip_tac >>
  `rt.abi_immutables = st.abi_immutables` by
    gvs[capture_abi_memory_def, AllCaseEqs(), return_def, raise_def] >>
  drule_all abi_typing_observations_frame >> simp[]
QED

Theorem write_abi_memory_typing_frame:
  write_abi_memory cx id tv v subs ao st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx'. env_consistent env cx' rt <=> env_consistent env cx' st) /\
  rt.accounts = st.accounts
Proof
  strip_tac >> drule write_abi_memory_frame >> strip_tac >>
  irule abi_typing_observations_frame >> simp[]
QED

Theorem release_abi_memory_typing_frame:
  release_abi_memory mark st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx. env_consistent env cx rt <=> env_consistent env cx st) /\
  rt.accounts = st.accounts
Proof
  simp[release_abi_memory_def, return_def] >> strip_tac >> gvs[] >>
  simp[state_well_typed_def, env_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def]
QED

(* Arena lifetime is structural. Contents may change, but captured tokens
   survive writes and further captures. No cell-read readiness is assumed. *)
Theorem write_abi_memory_length:
  write_abi_memory cx id tv v subs ao st = (res,rt) ==>
  LENGTH rt.abi_memory = LENGTH st.abi_memory
Proof
  rw[write_abi_memory_def, write_abi_memory_child_def,
     AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem capture_abi_memory_length:
  capture_abi_memory cx id tv v st = (res,rt) ==>
  LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  (!token. res = INL token ==>
    token = LENGTH st.abi_memory /\ LENGTH rt.abi_memory = token + 1)
Proof
  rw[capture_abi_memory_def, AllCaseEqs(), return_def, raise_def] >> simp[]
QED

Theorem release_abi_memory_length:
  mark <= LENGTH st.abi_memory /\
  release_abi_memory mark st = (res,rt) ==>
  res = INL () /\ LENGTH rt.abi_memory = mark
Proof
  simp[release_abi_memory_def, return_def, LENGTH_TAKE_EQ] >>
  rpt strip_tac >> gvs[MIN_DEF]
QED

(* Immutable captures append to a frame-wide arena; local cleanup never
   releases it. Writes retain token positions and only update matching keys. *)
Theorem capture_abi_immutable_typing_frame:
  capture_abi_immutable cx src id tv v st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx'. env_consistent env cx' rt <=> env_consistent env cx' st) /\
  rt.accounts = st.accounts /\ rt.abi_memory = st.abi_memory
Proof
  rw[capture_abi_immutable_def, AllCaseEqs(), return_def, raise_def] >>
  simp[state_well_typed_def, env_consistent_def, env_scopes_consistent_def,
       env_immutables_consistent_def]
QED

Theorem write_abi_immutables_typing_frame:
  write_abi_immutables cx src id tv v subs ao st = (res,rt) ==>
  (state_well_typed rt <=> state_well_typed st) /\
  (!env cx'. env_consistent env cx' rt <=> env_consistent env cx' st) /\
  rt.accounts = st.accounts /\ rt.abi_memory = st.abi_memory
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, state_well_typed_def,
      env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def]
QED

Theorem capture_abi_immutable_length:
  capture_abi_immutable cx src id tv v st = (res,rt) ==>
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
  (!token. res = INL token ==>
    token = LENGTH st.abi_immutables /\ LENGTH rt.abi_immutables = token + 1)
Proof
  rw[capture_abi_immutable_def, AllCaseEqs(), return_def, raise_def] >> simp[]
QED

Theorem capture_abi_immutable_prefix:
  capture_abi_immutable cx src id tv v st = (res,rt) ==>
  TAKE (LENGTH st.abi_immutables) rt.abi_immutables = st.abi_immutables
Proof
  rw[capture_abi_immutable_def, AllCaseEqs(), return_def, raise_def] >>
  simp[TAKE_LENGTH_APPEND]
QED

Theorem capture_abi_memory_prefix:
  capture_abi_memory cx id tv v st = (res,rt) ==>
  TAKE (LENGTH st.abi_memory) rt.abi_memory = st.abi_memory
Proof
  rw[capture_abi_memory_def, AllCaseEqs(), return_def, raise_def] >>
  simp[TAKE_LENGTH_APPEND]
QED

Theorem write_abi_immutables_length:
  write_abi_immutables cx src id tv v subs ao st = (res,rt) ==>
  LENGTH rt.abi_immutables = LENGTH st.abi_immutables
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem write_abi_immutables_keys:
  write_abi_immutables cx src id tv v subs ao st = (res,rt) ==>
  MAP FST rt.abi_immutables = MAP FST st.abi_immutables
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, MAP_MAP_o, combinTheory.o_DEF,
      LAMBDA_PROD] >>
  irule MAP_CONG >> simp[FORALL_PROD]
QED

Theorem write_abi_immutables_cell:
  abi_path_offset tv subs = SOME (off,t) /\
  evaluate_subscripts tv v subs = INL child /\
  abi_operation_writes t child ao = SOME writes /\
  oEL token st.abi_immutables = SOME (key,mem) /\
  write_abi_immutables cx src id tv v subs ao st = (res,rt) ==>
  res = INL () /\
  oEL token rt.abi_immutables = SOME
    (key, if key = (cx.txn.target,(src,id))
          then apply_writes (n2w off) writes mem else mem)
Proof
  rw[write_abi_immutables_def, return_def] >>
  gvs[oEL_THM, EL_MAP, EVERY_MEM, combinTheory.o_DEF] >>
  `MEM ((cx.txn.target,(src,id)),mem) rt.abi_immutables` by
    (simp[MEM_EL] >> qexists_tac `token` >> simp[]) >>
  first_x_assum drule >> simp[]
QED

Theorem write_abi_immutables_unmatched:
  write_abi_immutables cx src id tv v subs ao st = (res,rt) /\
  oEL token st.abi_immutables = SOME (key,mem) /\
  key <> (cx.txn.target,(src,id)) ==>
  oEL token rt.abi_immutables = SOME (key,mem)
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, oEL_THM, EL_MAP]
QED

Theorem write_abi_memory_immutables:
  write_abi_memory cx id tv v subs ao st = (res,rt) ==>
  rt.abi_immutables = st.abi_immutables
Proof
  rw[write_abi_memory_def, write_abi_memory_child_def,
     AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem release_abi_memory_immutables:
  release_abi_memory mark st = (res,rt) ==>
  rt.abi_immutables = st.abi_immutables
Proof
  simp[release_abi_memory_def, return_def] >> strip_tac >> gvs[]
QED

Theorem state_well_typed_abi_immutables[simp]:
  state_well_typed (st with abi_immutables := mem) <=> state_well_typed st
Proof
  simp[state_well_typed_def]
QED

Theorem env_consistent_abi_immutables[simp]:
  env_consistent env cx (st with abi_immutables := mem) <=> env_consistent env cx st
Proof
  simp[env_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def]
QED

Theorem state_well_typed_abi_memory[simp]:
  state_well_typed (st with abi_memory := mem) <=> state_well_typed st
Proof
  simp[state_well_typed_def]
QED

Theorem env_consistent_abi_memory[simp]:
  env_consistent env cx (st with abi_memory := mem) <=> env_consistent env cx st
Proof
  simp[env_consistent_def, env_scopes_consistent_def, env_immutables_consistent_def]
QED
