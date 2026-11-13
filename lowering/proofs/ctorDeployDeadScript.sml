(* deploy_dead is well formed, and deploy_venom_result_rel is preserved by the
 * O1 pipeline's result relation with deploy_dead's dead bytes.
 * TOP-LEVEL: deploy_dead_wf, deploy_dead_lo_ok, deploy_venom_result_rel_dead (pieces of
 * e2e_deploy_correctness).
 * Helpers: ctorDeployDeadSection* (the immutables section's dead bytes),
 * ctorDeployDeadLoad/ImmTypes (load_contract's sources and immutable types).
 *)
Theory ctorDeployDead
Ancestors
  ctorDeployDefs bodyPtrDefs gasContext ctorDeployDeadSectionFrame ctorDeployDeadSectionRel
  ctorDeployDeadLoad ctorDeployDeadImmTypes e2eComposition ptrDiscipline accountsRelProps compileEnv loweringStateRelDefs
  vyperInterpreter list rich_list

Theorem deploy_dead_wf:
  !H tops runtime_bc am tx.
    deploy_source_ok tops am tx ==>
    dead_wf (deploy_dead H tops runtime_bc am tx)
Proof
  rpt strip_tac >> drule deploy_source_ok_struct_args_unique >> strip_tac >>
  simp[dead_wf_def, deploy_dead_def] >> rpt conj_tac
  >- (rpt gen_tac >> Cases_on `a = tx.target` >>
      simp[storage_agree_except_storage_dead] >> strip_tac >>
      drule storage_agree_storage_dead >> simp[])
  >- (rpt gen_tac >> Cases_on `a = tx.target` >>
      simp[storage_agree_except_storage_dead] >> strip_tac >>
      drule storage_agree_storage_dead >> simp[]) >>
  rpt strip_tac >>
  `imm_section_dead tops (DROP (LENGTH runtime_bc) r2) =
   imm_section_dead tops (DROP (LENGTH runtime_bc) r1)` suffices_by simp[] >>
  irule imm_section_dead_frame >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `j + LENGTH runtime_bc` mp_tac) >>
  simp[EL_DROP]
QED

(* The constructor's pointer checks run under deploy_dead H and the
   immutables fixed region's bound: dead_lo_ok at the constructor's context. *)
Theorem deploy_dead_lo_ok:
  !H tops runtime_bc am tx cenv.
    cenv.ce_is_ctor ==>
    dead_lo_ok H (deploy_dead H tops runtime_bc am tx) (imm_len tops) cenv
      (deploy_evaluation_context tops am tx)
Proof
  rpt strip_tac >>
  `cx_tops (deploy_evaluation_context tops am tx) = tops` by
    (irule cx_tops_module >>
     simp[deploy_evaluation_context_def, initial_evaluation_context_def,
          get_module_code_def]) >>
  `(deploy_evaluation_context tops am tx).txn.target = tx.target` by
    simp[deploy_evaluation_context_def, initial_evaluation_context_def] >>
  simp[dead_lo_ok_def, cx_dead_def, deploy_dead_def, dead_sub_def]
QED

(* A list that agrees with pre ++ sec1 outside the dead bytes of sec1 is
   pre ++ sec2 for a sec2 that agrees with sec1 outside them. *)
Theorem append_agree_except_suffix:
  !pre sec1 r2 P.
    LENGTH r2 = LENGTH (pre ++ sec1) /\
    (!i. i < LENGTH (pre ++ sec1) /\ ~(LENGTH pre <= i /\ P (i - LENGTH pre)) ==>
         EL i (pre ++ sec1) = EL i r2) ==>
    ?sec2. r2 = pre ++ sec2 /\ LENGTH sec2 = LENGTH sec1 /\
           !j. j < LENGTH sec1 /\ ~P j ==> EL j sec2 = EL j sec1
Proof
  rpt strip_tac >> qexists_tac `DROP (LENGTH pre) r2` >> rpt conj_tac
  >- (irule LIST_EQ >> rw[EL_APPEND_EQN, EL_DROP] >>
      first_x_assum (qspec_then `x` mp_tac) >> simp[EL_APPEND_EQN])
  >- simp[] >>
  rpt strip_tac >> first_x_assum (qspec_then `j + LENGTH pre` mp_tac) >>
  simp[EL_APPEND_EQN, EL_DROP]
QED

(* deploy_dead's storage and transient dead bytes are those of
   accounts_agree and transient_agree at the target: agreeing up to them
   composes with the source relation, as external_call_dead's do. *)
Theorem accounts_agree_except_target_dead[local]:
  (!a st. D.d_stor a st =
     if a = t then {(k,b) | storage_dead H F st (w2n k) b} else {}) ==>
  (accounts_agree_except D a1 a2 <=>
   (!a. (a1 a with storage := (a2 a).storage) = a2 a) /\
   (!a. a <> t ==> (a1 a).storage = (a2 a).storage) /\
   storage_agree (storage_dead H F (a1 t).storage)
     (a1 t).storage (a2 t).storage)
Proof
  strip_tac >> simp[accounts_agree_except_def] >>
  pop_assum (fn th => simp[th]) >> eq_tac
  >- (strip_tac >> rpt conj_tac
      >- (gen_tac >> first_x_assum (qspec_then `a` (ACCEPT_TAC o CONJUNCT1)))
      >- (rpt strip_tac >> first_x_assum (qspec_then `a` mp_tac) >>
          gvs[storage_agree_except_empty]) >>
      first_x_assum (qspec_then `t` mp_tac) >>
      simp[storage_agree_except_storage_dead]) >>
  rpt strip_tac
  >- (first_x_assum (qspec_then `a` ACCEPT_TAC)) >>
  Cases_on `a = t` >>
  gvs[storage_agree_except_storage_dead, storage_agree_except_empty]
QED

Theorem transient_agree_except_target_dead[local]:
  (!a st. D.d_trans a st =
     if a = t then {(k,b) | storage_dead H T st (w2n k) b} else {}) ==>
  (transient_agree_except D t1 t2 <=>
   (!a. a <> t ==> t1 a = t2 a) /\
   storage_agree (storage_dead H T (t1 t)) (t1 t) (t2 t))
Proof
  strip_tac >> simp[transient_agree_except_def] >>
  pop_assum (fn th => simp[th]) >> eq_tac
  >- (strip_tac >> conj_tac
      >- (rpt strip_tac >> first_x_assum (qspec_then `a` mp_tac) >>
          gvs[storage_agree_except_empty]) >>
      first_x_assum (qspec_then `t` mp_tac) >>
      simp[storage_agree_except_storage_dead]) >>
  rpt strip_tac >> Cases_on `a = t` >>
  gvs[storage_agree_except_storage_dead, storage_agree_except_empty]
QED

Theorem accounts_agree_dead_target_trans[local]:
  !D a1 H cx a0 a2.
    (!a st. D.d_stor a st =
       if a = cx.txn.target then {(k,b) | storage_dead H F st (w2n k) b}
       else {}) /\
    accounts_agree H cx a0 a1 /\ accounts_agree_except D a1 a2 ==>
    accounts_agree H cx a0 a2
Proof
  rpt strip_tac >> irule accounts_agree_storage_dead_trans >>
  qexists_tac `a1` >>
  drule accounts_agree_except_target_dead >>
  disch_then (fn th => gvs[th])
QED

Theorem transient_agree_dead_target_trans[local]:
  !D t1 H cx t0 t2.
    (!a st. D.d_trans a st =
       if a = cx.txn.target then {(k,b) | storage_dead H T st (w2n k) b}
       else {}) /\
    transient_agree H cx t0 t1 /\ transient_agree_except D t1 t2 ==>
    transient_agree H cx t0 t2
Proof
  rpt strip_tac >> irule transient_agree_storage_dead_trans >>
  qexists_tac `t1` >>
  drule transient_agree_except_target_dead >>
  disch_then (fn th => gvs[th])
QED

Theorem request_agree_dead_target_trans[local]:
  !D r1 H cx r0 r2.
    (!a st. D.d_stor a st =
       if a = cx.txn.target then {(k,b) | storage_dead H F st (w2n k) b}
       else {}) /\
    (!a st. D.d_trans a st =
       if a = cx.txn.target then {(k,b) | storage_dead H T st (w2n k) b}
       else {}) /\
    request_agree H cx r0 r1 /\ request_agree_except D r1 r2 ==>
    request_agree H cx r0 r2
Proof
  rw[request_agree_def, request_agree_except_def]
  >- gvs[extCallOracleTheory.call_request_component_equality]
  >- metis_tac[accounts_agree_dead_target_trans]
  >> metis_tac[transient_agree_dead_target_trans]
QED

(* Masking the target's code to the same value keeps accounts equal up to
   dead storage bytes: the code update leaves every storage alone. *)
Theorem accounts_agree_except_code_update[local]:
  accounts_agree_except D a1 a2 ==>
  accounts_agree_except D
    (update_account t (lookup_account t a1 with code := c) a1)
    (update_account t (lookup_account t a2 with code := c) a2)
Proof
  simp[accounts_agree_except_def, vfmStateTheory.update_account_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
  strip_tac >> gen_tac >> first_x_assum (qspec_then `a` strip_assume_tac) >>
  IF_CASES_TAC >> gvs[vfmStateTheory.account_state_component_equality]
QED

Theorem deploy_venom_result_rel_dead:
  !H tops runtime_bc am tx gobs src res res'.
    deploy_source_ok tops am tx /\
    src = load_contract NONE gobs am tx [(NONE, tops)] [] /\
    deploy_venom_result_rel H tops runtime_bc tx src res /\
    ~deploy_source_exempt tops src /\
    dead_result_rel (deploy_dead H tops runtime_bc am tx) res res'
    ==>
    deploy_venom_result_rel H tops runtime_bc tx src res'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `src = _` (assume_tac o SYM) >>
  Cases_on `res` >> Cases_on `res'` >> fs[dead_result_rel_def]
  >- (rename1 `accounts_agree_except _ s.vs_accounts s'.vs_accounts` >>
      Cases_on `src`
      >- (rename1 `INL p` >> PairCases_on `p` >>
          rename1 `INL (am', rqs)` >>
          drule load_contract_sources_layouts >>
          impl_tac >- (qpat_x_assum `deploy_source_ok _ _ _` mp_tac >>
                       simp[deploy_source_ok_def]) >>
          strip_tac >>
          qabbrev_tac `D = deploy_dead H tops runtime_bc am tx` >>
          fs[deploy_venom_result_rel_def, LET_THM] >>
          (* returndata *)
          qspecl_then [`runtime_bc`, `section`, `s'.vs_returndata`,
                       `imm_section_dead tops section`] mp_tac
            append_agree_except_suffix >>
          impl_tac >- (gvs[Abbr `D`, deploy_dead_def] >> rpt strip_tac >>
                       first_x_assum irule >> simp[DROP_LENGTH_APPEND]) >>
          strip_tac >> qexists_tac `sec2` >> rpt conj_tac
          >~ [`s'.vs_returndata = _`] >- first_assum ACCEPT_TAC
          >~ [`immutables_section_rel _ _ sec2`]
          >- (`!pre vis name ty slot post tv v.
                 tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
                 FLOOKUP (get_source_immutables NONE
                   (account_immutables am' tx.target)) name = SOME (tv,v) ==>
                 evaluate_type (type_env tops) ty = SOME tv` by
                metis_tac[load_contract_immutables_typed] >>
              qspecl_then [`tops`, `account_immutables am' tx.target`,
                           `section`, `sec2`] mp_tac immutables_section_rel_dead >>
              impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                           simp[]) >>
              simp[])
          >~ [`accounts_agree H _ _ _`]
          >- (`s'.vs_pending_deletions = s.vs_pending_deletions` by gvs[] >>
              pop_assum SUBST1_TAC >>
              irule accounts_agree_dead_target_trans >>
              qexistsl [`D`, `process_deletions s.vs_pending_deletions
                 (update_account tx.target
                    (lookup_account tx.target s.vs_accounts with
                       code := (lookup_account tx.target am'.accounts).code)
                    s.vs_accounts)`] >>
              rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              TRY (simp[Abbr `D`, deploy_dead_def, initial_evaluation_context_def] >>
                   NO_TAC) >>
              irule accounts_agree_except_process_deletions >>
              irule accounts_agree_except_code_update >> first_assum ACCEPT_TAC)
          >~ [`transient_agree H _ _ _`]
          >- (irule transient_agree_dead_target_trans >>
              qexistsl [`D`, `s.vs_transient`] >>
              rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
              simp[Abbr `D`, deploy_dead_def, initial_evaluation_context_def])
          >~ [`logs_correspond _ _ _ _ _`] >- gvs[] >>
          gvs[LIST_REL_EL_EQN] >> rpt strip_tac >>
          irule request_agree_dead_target_trans >>
          qexistsl [`D`, `EL n s.vs_requests`] >>
          rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
          >- simp[Abbr `D`, deploy_dead_def, initial_evaluation_context_def]
          >- simp[Abbr `D`, deploy_dead_def, initial_evaluation_context_def] >>
          metis_tac[]) >>
      rename1 `INR exc` >> Cases_on `exc` >>
      gvs[deploy_venom_result_rel_def, deploy_source_exempt_def]) >>
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> gvs[deploy_venom_result_rel_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> gvs[deploy_venom_result_rel_def] >>
  Cases_on `a` >> Cases_on `a'` >> gvs[]
QED
