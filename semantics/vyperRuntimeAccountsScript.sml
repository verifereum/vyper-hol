(* Executable account bounds, shared by concrete calls and oracle helpers.
 * Moved verbatim from vyperInterpreter: no evaluator/type-system dependency.
 * TOP-LEVEL: accounts_runtime_well_typed, its unconditional CV representation.
 *)
Theory vyperRuntimeAccounts
Ancestors
  arithmetic list pair words sptree cv cv_std cv_rep
  vfmState vfmCompute[ignore_grammar]
Libs cv_transLib

Definition account_runtime_well_typed_def:
  account_runtime_well_typed (a : account_state) <=>
    a.balance < 2 ** 256 /\ LENGTH a.code <= 24576
End

val () = cv_auto_trans account_runtime_well_typed_def;

Definition accounts_runtime_well_typed_def:
  accounts_runtime_well_typed (accounts : evm_accounts) <=>
    !addr. account_runtime_well_typed (lookup_account addr accounts)
End

Definition accounts_spt_runtime_well_typed_def:
  (accounts_spt_runtime_well_typed (LN : account_state spt) <=> T) /\
  (accounts_spt_runtime_well_typed (LS a) <=> account_runtime_well_typed a) /\
  (accounts_spt_runtime_well_typed (BN l r) <=>
    accounts_spt_runtime_well_typed l /\ accounts_spt_runtime_well_typed r) /\
  (accounts_spt_runtime_well_typed (BS l a r) <=>
    accounts_spt_runtime_well_typed l /\ account_runtime_well_typed a /\
    accounts_spt_runtime_well_typed r)
End

val () = cv_auto_trans accounts_spt_runtime_well_typed_def;

Theorem account_runtime_well_typed_empty_account_state[simp]:
  account_runtime_well_typed empty_account_state
Proof
  simp[account_runtime_well_typed_def, empty_account_state_def]
QED

Theorem accounts_spt_runtime_well_typed_lookup:
  !t k a.
    wf t /\ accounts_spt_runtime_well_typed t /\ lookup k t = SOME a ==>
    account_runtime_well_typed a
Proof
  Induct >> rw[accounts_spt_runtime_well_typed_def, sptreeTheory.lookup_def,
                sptreeTheory.wf_def]
  >> metis_tac[]
QED

Theorem accounts_spt_runtime_well_typed_insert:
  !k a t.
    accounts_spt_runtime_well_typed t /\ account_runtime_well_typed a ==>
    accounts_spt_runtime_well_typed (insert k a t)
Proof
  recInduct sptreeTheory.insert_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[accounts_spt_runtime_well_typed_def] >>
  Cases_on `k = 0` >-
    simp[Once sptreeTheory.insert_def, accounts_spt_runtime_well_typed_def] >>
  Cases_on `EVEN k` >-
    (PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
     gvs[accounts_spt_runtime_well_typed_def]) >>
  PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
  gvs[accounts_spt_runtime_well_typed_def]
QED

Theorem accounts_spt_runtime_well_typed_build_spt:
  !accounts.
    accounts_spt_runtime_well_typed
      (build_spt empty_account_state (dimword (:160)) accounts) <=>
    accounts_runtime_well_typed accounts
Proof
  rw[accounts_runtime_well_typed_def, EQ_IMP_THM]
  >- (
    Cases_on `accounts addr = empty_account_state` >- simp[lookup_account_def] >>
    `lookup (w2n addr) (build_spt empty_account_state (dimword (:160)) accounts) =
       SOME (accounts addr)`
      by (simp[lookup_build_spt] >> qspec_then `addr` mp_tac wordsTheory.w2n_lt >> simp[]) >>
    simp[lookup_account_def] >>
    irule accounts_spt_runtime_well_typed_lookup >>
    qexistsl [`w2n addr`, `build_spt empty_account_state (dimword (:160)) accounts`] >>
    simp[] ) >>
  qsuff_tac `!n. accounts_spt_runtime_well_typed
                   (build_spt empty_account_state n accounts)` >- simp[] >>
  Induct >- simp[build_spt_def, accounts_spt_runtime_well_typed_def] >>
  simp[build_spt_def] >> rw[] >>
  irule accounts_spt_runtime_well_typed_insert >> simp[] >>
  first_x_assum (qspec_then `n2w n` mp_tac) >> simp[lookup_account_def]
QED

val cv_accounts_spt_runtime_well_typed_thm = theorem "cv_accounts_spt_runtime_well_typed_thm";

Theorem accounts_runtime_well_typed_cv_rep:
  cv_rep T
    (cv_accounts_spt_runtime_well_typed (from_evm_accounts accounts))
    b2c
    (accounts_runtime_well_typed accounts)
Proof
  simp[cv_repTheory.cv_rep_def, from_evm_accounts_def,
       GSYM cv_accounts_spt_runtime_well_typed_thm] >>
  AP_TERM_TAC >>
  simp[Once (GSYM accounts_spt_runtime_well_typed_build_spt)]
QED

(* Compositional representation: the old closed encoding theorem only worked
   when accounts was a translation argument, not an outcome/state selector. *)
Theorem accounts_runtime_well_typed_cv[cv_rep]:
  b2c (accounts_runtime_well_typed accounts) =
    cv_accounts_spt_runtime_well_typed (from_evm_accounts accounts)
Proof
  simp[GSYM (SRULE [cv_repTheory.cv_rep_def] accounts_runtime_well_typed_cv_rep)]
QED
