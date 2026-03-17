Theory vyperLookupStorageScopes

Ancestors
  vyperLookup vyperLookupStorage vyperScopePreservation vyperState vyperInterpreter

(* ============================================================
   Cross-domain independence: lookup_toplevel_name vs scopes

   lookup_toplevel_name reads from immutables/accounts/tStorage,
   never from scopes.  This chain of local lemmas proves that the
   FST (result value) of lookup_global is independent of the scopes
   field, from which the exported theorems follow.
   ============================================================ *)

(* --- Local helpers for monadic scope independence --- *)

Theorem get_address_immutables_scopes_fst[local]:
  ∀cx st s. get_address_immutables cx (st with scopes := s) =
    (FST (get_address_immutables cx st), st with scopes := s)
Proof
  rpt gen_tac >> simp[get_address_immutables_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[lift_option_def, return_def, raise_def]
QED

Theorem get_address_immutables_state[local]:
  ∀cx st. SND (get_address_immutables cx st) = st
Proof
  rpt gen_tac >> simp[get_address_immutables_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[lift_option_def, return_def, raise_def]
QED

Theorem get_immutables_scopes[local]:
  ∀cx mid st s. get_immutables cx mid (st with scopes := s) =
    (FST (get_immutables cx mid st), st with scopes := s)
Proof
  rpt gen_tac >>
  simp[get_immutables_def, bind_def, get_address_immutables_scopes_fst] >>
  Cases_on `get_address_immutables cx st` >>
  `r = st` by (
    mp_tac (SPECL [``cx:evaluation_context``, ``st:evaluation_state``]
      get_address_immutables_state) >> simp[]) >>
  gvs[] >>
  Cases_on `q` >> simp[return_def, raise_def]
QED

Theorem get_immutables_state[local]:
  ∀cx mid st. SND (get_immutables cx mid st) = st
Proof
  rpt gen_tac >> simp[get_immutables_def, bind_def] >>
  Cases_on `get_address_immutables cx st` >>
  `r = st` by (
    mp_tac (SPECL [``cx:evaluation_context``, ``st:evaluation_state``]
      get_address_immutables_state) >> simp[]) >>
  gvs[] >>
  Cases_on `q` >> simp[return_def, raise_def]
QED

Theorem get_storage_backend_scopes_fst[local]:
  ∀cx is_t st s. get_storage_backend cx is_t (st with scopes := s) =
    (FST (get_storage_backend cx is_t st), st with scopes := s)
Proof
  rpt gen_tac >> Cases_on `is_t` >>
  simp[get_storage_backend_def, bind_def,
       get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem read_storage_slot_scopes[local]:
  ∀cx is_t slot tv st s.
    read_storage_slot cx is_t slot tv (st with scopes := s) =
    (FST (read_storage_slot cx is_t slot tv st), st with scopes := s)
Proof
  rpt gen_tac >> Cases_on `is_t` >>
  simp[read_storage_slot_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def,
       bind_def, return_def, lift_option_def] >>
  rpt BasicProvers.FULL_CASE_TAC >>
  simp[return_def, raise_def]
QED

Theorem fst_case_pair_sumE[local]:
  ∀p (f:'a -> 'b + 'c) g.
    FST (case p of (INL v,s) => (f v,s) | (INR e,s) => (INR e,s)) =
    (case FST p of INL v => f v | INR e => INR e)
Proof
  rpt gen_tac >> Cases_on `p` >> Cases_on `q` >> simp[]
QED

Theorem fst_case_fst[local]:
  ∀(x:'a + 'b) (f:'a -> 'c + 'b) s1 s2.
    FST (case x of INL v => (f v, s1) | INR e => (INR e, s2)) =
    (case x of INL v => f v | INR e => INR e)
Proof
  rpt gen_tac >> Cases_on `x` >> simp[]
QED

(* lookup_global result value is independent of scopes *)
Theorem lookup_global_scopes_fst[local]:
  ∀cx mid id st s.
    FST (lookup_global cx mid id (st with scopes := s)) =
    FST (lookup_global cx mid id st)
Proof
  rpt gen_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, ignore_bind_def] >>
  Cases_on `get_module_code cx mid` >> simp[return_def, raise_def] >>
  rename1 `SOME modcode` >>
  Cases_on `find_var_decl_by_num id modcode` >> simp[] >- (
    simp[bind_def, get_immutables_scopes, fst_case_fst] >>
    Cases_on `get_immutables cx mid st` >>
    `r = st` by (
      qpat_x_assum `get_immutables _ _ _ = _` (fn th =>
        mp_tac (SPECL [``cx:evaluation_context``, ``mid:num option``,
                       ``st:evaluation_state``] get_immutables_state) >>
        REWRITE_TAC [th] >> simp[])) >>
    gvs[] >>
    Cases_on `q` >> simp[return_def, raise_def] >>
    Cases_on `FLOOKUP x id` >> simp[return_def, raise_def]
  ) >>
  rename1 `SOME found` >> PairCases_on `found` >>
  Cases_on `found0` >> simp[bind_def] >- (
    Cases_on `lookup_var_slot_from_layout cx b mid found1` >>
    simp[return_def, raise_def] >>
    Cases_on `evaluate_type (get_tenv cx) t` >>
    simp[return_def, raise_def] >>
    rename1 `SOME tv` >>
    Cases_on `tv` >>
    simp[bind_def, return_def, raise_def, read_storage_slot_scopes,
         fst_case_pair_sumE, fst_case_fst]
  ) >>
  Cases_on `lookup_var_slot_from_layout cx b mid found1` >>
  simp[return_def, raise_def]
QED

(* --- Exported cross-domain independence theorems --- *)

(* lookup_toplevel_name is independent of scopes *)
Theorem lookup_toplevel_name_scopes:
  ∀cx st s mid m.
    lookup_toplevel_name cx (st with scopes := s) mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac >>
  simp[lookup_toplevel_name_def] >>
  Cases_on `lookup_global cx mid (string_to_num m) (st with scopes := s)` >>
  Cases_on `lookup_global cx mid (string_to_num m) st` >> simp[] >>
  `q = q'` by (
    qspecl_then [`cx`, `mid`, `string_to_num m`, `st`, `s`]
      mp_tac lookup_global_scopes_fst >> simp[]) >>
  simp[]
QED

(* lookup_toplevel_name is independent of update_name *)
Theorem lookup_toplevel_name_update_name:
  ∀cx st n v mid m.
    lookup_toplevel_name cx (update_name st n v) mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac >>
  simp[update_name_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> simp[] >-
    (Cases_on `st.scopes` >> simp[lookup_toplevel_name_scopes]) >>
  PairCases_on `x` >> simp[lookup_toplevel_name_scopes]
QED

(* lookup_toplevel_name is independent of declare_name *)
Theorem lookup_toplevel_name_declare_name:
  ∀cx st n ty v mid m.
    lookup_toplevel_name cx (declare_name st n ty v) mid m =
    lookup_toplevel_name cx st mid m
Proof
  rpt gen_tac >>
  simp[declare_name_def] >>
  Cases_on `st.scopes` >>
  simp[lookup_toplevel_name_scopes]
QED

Theorem update_toplevel_name_preserves_scopes:
  ∀cx st mid n v.
    (update_toplevel_name cx st mid n v).scopes = st.scopes
Proof
  rw[update_toplevel_name_def] >>
  Cases_on `set_global cx mid (string_to_num n) v st` >>
  imp_res_tac set_global_scopes >> simp[]
QED

(* lookup_name is independent of update_toplevel_name *)
Theorem lookup_name_update_toplevel_name:
  ∀cx st mid n v m.
    lookup_name (update_toplevel_name cx st mid n v) m =
    lookup_name st m
Proof
  rpt gen_tac >>
  `(update_toplevel_name cx st mid n v).scopes = st.scopes`
    by simp[update_toplevel_name_preserves_scopes] >>
  simp[lookup_name_def]
QED

(* var_in_scope is independent of update_toplevel_name *)
Theorem var_in_scope_update_toplevel_name:
  ∀cx st mid n v m.
    var_in_scope (update_toplevel_name cx st mid n v) m ⇔
    var_in_scope st m
Proof
  simp[var_in_scope_def, lookup_name_update_toplevel_name]
QED
