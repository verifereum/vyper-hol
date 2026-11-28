(* Top-theorem entry corollaries for the source recipient-overflow error. *)
Theory totalBalanceOverflow
Ancestors
  totalBalanceOverflowCore totalBalanceCallTrace vyperBalanceOverflow
  e2eDefs e2eDeployDefs
  e2eModsDefs e2eDeployModsDefs vfmTotalBalance

Theorem deploy_state_rel_mods_total_balance_bounded:
  deploy_state_rel_mods mods exps deploy_bc am tx es ==>
  total_balance am.accounts <= 2 ** 256 - 1
Proof
  strip_tac >>
  `total_balance es.rollback.accounts <= 2 ** 256 - 1` by
    (irule balance_bounded_rollback >>
     fs[deploy_state_rel_mods_def]) >>
  `total_balance (accounts_after_transfer tx am.accounts) =
     total_balance am.accounts` by
    (irule total_balance_accounts_after_transfer >>
     fs[deploy_state_rel_mods_def]) >>
  gvs[deploy_state_rel_mods_def]
QED

Theorem call_state_rel_no_recipient_overflow:
  call_state_rel tops runtime_bc am tx es /\
  call_external_trace (SOME (MAP SND (call_trace es))) gobs am tx =
    (res,am',rqs,obs) ==>
  source_result_ok res
Proof
  strip_tac >>
  drule_all call_state_rel_no_recipient_overflow_core >>
  gvs[]
QED

Theorem deploy_state_rel_mods_no_recipient_overflow:
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  load_contract_trace (SOME (MAP SND (call_trace es))) gobs am tx mods exps =
    (res,obs) ==>
  source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[deploy_state_rel_mods_total_balance_bounded] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[deploy_state_rel_mods_def, evm_state_ok_def]) >>
  `source_result_ok res /\
     (!am' rqs. res = INL (am',rqs) ==>
       total_balance am'.accounts <= 2 ** 256 - 1)` by
    (irule source_load_contract_no_recipient_overflow >>
     qexistsl [`am`, `exps`, `gobs`, `mods`, `obs`,
               `MAP SND (call_trace es)`, `tx`] >>
     simp[]) >>
  gvs[]
QED

Theorem deploy_state_rel_no_recipient_overflow:
  deploy_state_rel tops deploy_bc am tx es /\
  load_contract_trace (SOME (MAP SND (call_trace es))) gobs am tx
    [(NONE,tops)] [] = (res,obs) ==>
  source_result_ok res
Proof
  strip_tac >>
  drule_all deploy_state_rel_no_recipient_overflow_core >>
  simp[]
QED

Theorem deploy_state_rel_no_recipient_overflow_public:
  deploy_state_rel tops deploy_bc am tx es /\
  load_contract (SOME (MAP SND (call_trace es))) gobs am tx
    [(NONE,tops)] [] = res ==>
  source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[deploy_state_rel_total_balance_bounded] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[deploy_state_rel_def, evm_state_ok_def]) >>
  `source_result_ok res /\
     (!am' rqs. res = INL (am',rqs) ==>
       total_balance am'.accounts <= 2 ** 256 - 1)` by
    (irule source_load_contract_no_recipient_overflow_public >>
     qexistsl [`am`, `[]`, `gobs`, `[(NONE,tops)]`,
               `MAP SND (call_trace es)`, `tx`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[]
QED

Theorem deploy_state_rel_mods_no_recipient_overflow_public:
  deploy_state_rel_mods mods exps deploy_bc am tx es /\
  load_contract (SOME (MAP SND (call_trace es))) gobs am tx mods exps = res ==>
  source_result_ok res
Proof
  strip_tac >>
  `total_balance am.accounts <= 2 ** 256 - 1` by
    metis_tac[deploy_state_rel_mods_total_balance_bounded] >>
  `EVERY (\co. total_balance co.co_accounts <= 2 ** 256 - 1)
      (MAP SND (call_trace es))` by
    (irule call_trace_outcomes_total_balance_bounded >>
     fs[deploy_state_rel_mods_def, evm_state_ok_def]) >>
  `source_result_ok res /\
     (!am' rqs. res = INL (am',rqs) ==>
       total_balance am'.accounts <= 2 ** 256 - 1)` by
    (irule source_load_contract_no_recipient_overflow_public >>
     qexistsl [`am`, `exps`, `gobs`, `mods`,
               `MAP SND (call_trace es)`, `tx`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  gvs[]
QED
