(* deploy_dead is well formed, and deploy_venom_result_rel is preserved by the
 * O1 pipeline's result relation with deploy_dead's dead bytes.
 * TOP-LEVEL: deploy_dead_wf, deploy_venom_result_rel_dead (pieces of
 * e2e_deploy_correctness).
 * Helpers: ctorDeployDeadSection* (the immutables section's dead bytes),
 * ctorDeployDeadLoad/ImmTypes (load_contract's sources and immutable types).
 *)
Theory ctorDeployDead
Ancestors
  ctorDeployDefs ctorDeployDeadSectionFrame ctorDeployDeadSectionRel
  ctorDeployDeadLoad ctorDeployDeadImmTypes e2eComposition ptrDiscipline accountsRelProps compileEnv
  vyperInterpreter list rich_list

Theorem deploy_dead_wf:
  !tops runtime_bc am tx.
    deploy_source_ok tops am tx ==>
    dead_wf (deploy_dead tops runtime_bc am tx)
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

Theorem deploy_venom_result_rel_dead:
  !tops runtime_bc am tx gobs src res res'.
    deploy_source_ok tops am tx /\
    src = load_contract NONE gobs am tx [(NONE, tops)] [] /\
    deploy_venom_result_rel tops runtime_bc tx src res /\
    ~deploy_source_exempt tops src /\
    dead_result_rel (deploy_dead tops runtime_bc am tx) res res'
    ==>
    deploy_venom_result_rel tops runtime_bc tx src res'
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
          `(initial_evaluation_context am'.sources am'.layouts tx NONE).txn = tx`
            by simp[initial_evaluation_context_def] >>
          qabbrev_tac `cx = initial_evaluation_context am'.sources am'.layouts tx NONE` >>
          `deploy_dead tops runtime_bc am tx =
           <| d_stor := (\a st. if a = tx.target
                                then {(k,b) | storage_dead cx F st (w2n k) b}
                                else {});
              d_trans := (\a st. if a = tx.target
                                 then {(k,b) | storage_dead cx T st (w2n k) b}
                                 else {});
              d_imm := K UNIV;
              d_ret := (\r. {i | LENGTH runtime_bc <= i /\
                                imm_section_dead tops (DROP (LENGTH runtime_bc) r)
                                  (i - LENGTH runtime_bc)}) |>` by
            simp[deploy_dead_def, Abbr`cx`] >>
          pop_assum (fn th => fs[th]) >>
          fs[deploy_venom_result_rel_def, LET_THM] >>
          (* returndata *)
          qspecl_then [`runtime_bc`, `section`, `s'.vs_returndata`,
                       `imm_section_dead tops section`] mp_tac
            append_agree_except_suffix >>
          impl_tac >- (gvs[] >> rpt strip_tac >> first_x_assum irule >>
                       simp[DROP_LENGTH_APPEND]) >>
          strip_tac >> qexists_tac `sec2` >> simp[] >>
          `!a. a <> tx.target ==> s'.vs_accounts a = s.vs_accounts a` by
            (rpt strip_tac >>
             qpat_x_assum `accounts_agree_except _ _ _` mp_tac >>
             simp[accounts_agree_except_def] >>
             disch_then (qspec_then `a` strip_assume_tac) >>
             gvs[storage_agree_except_empty] >>
             qpat_x_assum `_ with storage := _ = _` (SUBST1_TAC o SYM) >>
             simp[vfmStateTheory.account_state_component_equality]) >>
          `s.vs_accounts tx.target with storage :=
             (s'.vs_accounts tx.target).storage = s'.vs_accounts tx.target /\
           storage_agree (storage_dead cx F (s.vs_accounts tx.target).storage)
             (s.vs_accounts tx.target).storage
             (s'.vs_accounts tx.target).storage` by
            (qpat_x_assum `accounts_agree_except _ _ _` mp_tac >>
             simp[accounts_agree_except_def] >>
             disch_then (qspec_then `tx.target` mp_tac) >>
             simp[storage_agree_except_storage_dead]) >>
          rpt conj_tac
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
          >- gvs[vfmStateTheory.lookup_account_def]
          >- (fs[vfmStateTheory.lookup_account_def,
                 vfmStateTheory.account_state_component_equality])
          >- (fs[vfmStateTheory.lookup_account_def] >>
              irule storage_agree_dead_trans >>
              qexists_tac `(s.vs_accounts tx.target).storage` >> simp[])
          >- (qpat_x_assum `transient_agree _ _ _` mp_tac >>
              qpat_x_assum `transient_agree_except _ _ _` mp_tac >>
              simp[transient_agree_def, transient_agree_except_def] >>
              rpt strip_tac
              >- (qpat_x_assum `!a. storage_agree_except _ _ _`
                    (qspec_then `addr` mp_tac) >>
                  simp[storage_agree_except_empty] >> metis_tac[]) >>
              qpat_x_assum `!a. storage_agree_except _ _ _`
                (qspec_then `tx.target` mp_tac) >>
              simp[storage_agree_except_storage_dead] >> strip_tac >>
              irule storage_agree_dead_trans >>
              qexists_tac `s.vs_transient tx.target` >> simp[]) >>
          gvs[]) >>
      rename1 `INR exc` >> Cases_on `exc` >>
      gvs[deploy_venom_result_rel_def, deploy_source_exempt_def]) >>
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> gvs[deploy_venom_result_rel_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> gvs[deploy_venom_result_rel_def] >>
  Cases_on `a` >> Cases_on `a'` >> gvs[]
QED
