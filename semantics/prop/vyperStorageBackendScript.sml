Theory vyperStorageBackend

Ancestors
  vyperStorage vyperState

(* ===== Non-monadic storage accessors ===== *)

Definition get_storage_def:
  get_storage cx (st : evaluation_state) T = st.tStorage cx.txn.target ∧
  get_storage cx st F = (st.accounts cx.txn.target).storage
End

Definition set_storage_def:
  set_storage cx (st : evaluation_state) T storage' =
    (st with tStorage := (cx.txn.target =+ storage') st.tStorage) ∧
  set_storage cx st F storage' =
    (st with accounts :=
       (cx.txn.target =+ (st.accounts cx.txn.target with storage := storage'))
       st.accounts)
End

Theorem get_storage_after_set:
  ∀cx st b s'. get_storage cx (set_storage cx st b s') b = s'
Proof
  rpt gen_tac \\ Cases_on `b`
  \\ simp[get_storage_def, set_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* ===== Connecting monadic and non-monadic ===== *)

Theorem get_storage_backend_eq:
  ∀cx b st. get_storage_backend cx b st = (INL (get_storage cx st b), st)
Proof
  Cases_on `b` >>
  simp[get_storage_backend_def, get_storage_def, bind_def, return_def,
       get_accounts_def, get_transient_storage_def,
       vfmStateTheory.lookup_account_def,
       vfmExecutionTheory.lookup_transient_storage_def]
QED

Theorem set_storage_backend_eq:
  ∀cx b storage' st.
    set_storage_backend cx b storage' st = (INL (), set_storage cx st b storage')
Proof
  Cases_on `b` >>
  simp[set_storage_backend_def, set_storage_def, bind_def, return_def,
       get_accounts_def, update_accounts_def, update_transient_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       vfmExecutionTheory.update_transient_storage_def,
       vyperStateTheory.evaluation_state_component_equality]
QED

(* ===== Monadic storage backend properties ===== *)

Theorem get_storage_backend_INL:
  ∀cx b st. ∃storage. get_storage_backend cx b st = (INL storage, st)
Proof
  Cases_on `b` >>
  simp[get_storage_backend_def, bind_def, return_def,
       get_accounts_def, get_transient_storage_def]
QED

Theorem get_storage_backend_state:
  !cx is_trans st res st'. get_storage_backend cx is_trans st = (res, st') ==> st' = st
Proof
  Cases_on `is_trans` >>
  rw[get_storage_backend_def, bind_def, get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem get_storage_backend_scopes:
  !cx is_trans st res st'. get_storage_backend cx is_trans st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[get_storage_backend_def, bind_def, get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem set_storage_backend_scopes:
  !cx is_trans storage' st res st'. set_storage_backend cx is_trans storage' st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[set_storage_backend_def, bind_def, update_transient_def, get_accounts_def,
     update_accounts_def, return_def] >> simp[]
QED

Theorem get_storage_backend_scopes_fst:
  ∀cx is_t st s. get_storage_backend cx is_t (st with scopes := s) =
    (FST (get_storage_backend cx is_t st), st with scopes := s)
Proof
  rpt gen_tac >> Cases_on `is_t` >>
  simp[get_storage_backend_def, bind_def,
       get_transient_storage_def, get_accounts_def, return_def]
QED

Theorem get_after_set_storage_backend:
  ∀cx is_transient storage' st.
    get_storage_backend cx is_transient
      (SND (set_storage_backend cx is_transient storage' st)) =
    (INL storage', SND (set_storage_backend cx is_transient storage' st))
Proof
  Cases_on `is_transient` >>
  rw[get_storage_backend_def, set_storage_backend_def,
     bind_def, return_def, get_accounts_def, update_accounts_def,
     get_transient_storage_def, update_transient_def,
     vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
     vfmExecutionTheory.lookup_transient_storage_def,
     vfmExecutionTheory.update_transient_storage_def,
     combinTheory.APPLY_UPDATE_THM]
QED

Theorem get_after_set_other_backend:
  ∀cx b1 b2 storage' st.
    b1 ≠ b2 ⇒
    FST (get_storage_backend cx b2
      (SND (set_storage_backend cx b1 storage' st))) =
    FST (get_storage_backend cx b2 st)
Proof
  Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
  simp[get_storage_backend_def, set_storage_backend_def,
       bind_def, return_def, get_accounts_def, update_accounts_def,
       get_transient_storage_def, update_transient_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def]
QED
