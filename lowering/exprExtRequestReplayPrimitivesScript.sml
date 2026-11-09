Theory exprExtRequestReplayPrimitives
Ancestors exprExtRequestReplayAlgebra vyperInterpreter vyperState

Theorem extrequest_obs_return[simp]:
  extrequest_obs_equivariant (return x)
Proof
  simp[extrequest_obs_equivariant_def, return_def]
QED

Theorem extrequest_obs_raise[simp]:
  extrequest_obs_equivariant (raise e)
Proof
  simp[extrequest_obs_equivariant_def, raise_def]
QED

Theorem extrequest_obs_bind:
  extrequest_obs_equivariant f /\
  (!x. extrequest_obs_equivariant (g x)) ==>
  extrequest_obs_equivariant (bind f g)
Proof
  rw[extrequest_obs_equivariant_def] >>
  simp[bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `res` >> gvs[]
QED

Theorem extrequest_obs_precompile:
  extrequest_obs_equivariant (precompile_call_success bt)
Proof
  simp[extrequest_obs_equivariant_def, precompile_call_success_def,
    check_def, assert_def, return_def, raise_def] >>
  rpt gen_tac >> Cases_on `precompile_builtin bt` >> simp[] >>
  Cases_on `s.outcomes` >> simp[] >>
  rename1 `SOME outs` >> Cases_on `outs` >> simp[] >>
  Cases_on `call_outcome_success h` >> simp[]
QED

Theorem extrequest_obs_type_check:
  extrequest_obs_equivariant (type_check p msg)
Proof
  simp[extrequest_obs_equivariant_def, type_check_def, assert_def] >>
  Cases_on `p` >> simp[]
QED

Theorem extrequest_obs_lift_sum:
  extrequest_obs_equivariant (lift_sum v)
Proof
  Cases_on `v` >> simp[lift_sum_def]
QED

Theorem extrequest_obs_get_scopes:
  extrequest_obs_equivariant get_scopes
Proof
  simp[extrequest_obs_equivariant_def, get_scopes_def, return_def]
QED

Theorem extrequest_obs_get_accounts:
  extrequest_obs_equivariant get_accounts
Proof
  simp[extrequest_obs_equivariant_def, get_accounts_def, return_def]
QED

Theorem extrequest_obs_lookup_flag:
  extrequest_obs_equivariant (lookup_flag_mem cx nsid mid)
Proof
  PairCases_on `nsid` >>
  simp[lookup_flag_mem_def] >>
  Cases_on `get_module_code cx nsid0` >> simp[] >>
  Cases_on `lookup_flag nsid1 x` >> simp[] >>
  Cases_on `INDEX_OF mid x'` >> simp[]
QED

Theorem extrequest_obs_get_place:
  extrequest_obs_equivariant (get_place r)
Proof
  Cases_on `r` >> simp[get_place_def]
QED

Theorem extrequest_obs_lift_option:
  extrequest_obs_equivariant (lift_option_type v msg)
Proof
  Cases_on `v` >> simp[lift_option_type_def]
QED

Theorem extrequest_obs_address_immutables:
  extrequest_obs_equivariant (get_address_immutables cx)
Proof
  simp[extrequest_obs_equivariant_def, get_address_immutables_def,
    lift_option_type_def] >>
  rpt gen_tac >> Cases_on `ALOOKUP s.immutables cx.txn.target` >>
  simp[return_def, raise_def]
QED

Theorem extrequest_obs_immutables:
  extrequest_obs_equivariant (get_immutables cx src)
Proof
  simp[get_immutables_def] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_address_immutables]
QED

Theorem extrequest_obs_lookup_global:
  extrequest_obs_equivariant (lookup_global cx src id)
Proof
  simp[lookup_global_def] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_lift_option] >> gen_tac >>
  Cases_on `find_var_decl_by_name id x` >> simp[]
  >- (irule extrequest_obs_bind >> simp[extrequest_obs_immutables] >>
      gen_tac >> Cases_on `FLOOKUP x' id` >> simp[]) >>
  PairCases_on `x'` >> Cases_on `x'0` >> simp[] >>
  irule extrequest_obs_bind >> simp[extrequest_obs_lift_option] >>
  gen_tac >> irule extrequest_obs_bind >> simp[extrequest_obs_lift_option]
QED

Theorem extrequest_obs_lift_option_runtime:
  extrequest_obs_equivariant (lift_option v msg)
Proof
  Cases_on `v` >> simp[lift_option_def]
QED

Theorem extrequest_obs_storage_backend:
  extrequest_obs_equivariant (get_storage_backend cx tr)
Proof
  Cases_on `tr` >> simp[get_storage_backend_def] >>
  irule extrequest_obs_bind >> simp[extrequest_obs_get_accounts] >>
  simp[extrequest_obs_equivariant_def, get_transient_storage_def, return_def]
QED

Theorem extrequest_obs_read_storage:
  extrequest_obs_equivariant (read_storage_slot cx tr slot tv)
Proof
  simp[read_storage_slot_def] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_storage_backend, extrequest_obs_lift_option_runtime]
QED

Theorem extrequest_obs_read_place:
  extrequest_obs_equivariant (read_place cx p)
Proof
  Cases_on `p` >> simp[read_place_def, extrequest_obs_read_storage] >>
  irule extrequest_obs_bind >>
  simp[extrequest_obs_get_scopes, extrequest_obs_immutables] >> gen_tac >>
  irule extrequest_obs_bind >>
  simp[extrequest_obs_lift_option, extrequest_obs_lift_sum]
QED

Theorem extrequest_obs_read_result:
  extrequest_obs_equivariant (read_result cx r)
Proof
  Cases_on `r` >> simp[read_result_def, extrequest_obs_read_place]
QED

Theorem extrequest_obs_place_type:
  extrequest_obs_equivariant (place_type_value cx p)
Proof
  Cases_on `p` >> simp[place_type_value_def] >>
  irule extrequest_obs_bind >>
  simp[extrequest_obs_get_scopes, extrequest_obs_immutables] >> gen_tac >>
  irule extrequest_obs_bind >> simp[extrequest_obs_lift_option]
QED

Theorem extrequest_obs_conditional:
  extrequest_obs_equivariant (conditional_result cx r)
Proof
  Cases_on `r` >> simp[conditional_result_def] >>
  irule extrequest_obs_bind >> simp[extrequest_obs_place_type] >> gen_tac >>
  IF_CASES_TAC >> simp[] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_read_place]
QED

Theorem extrequest_replay_switch:
  extrequest_success_replay f /\ extrequest_success_replay g ==>
  extrequest_success_replay (switch_BoolV cx r f g)
Proof
  strip_tac >> simp[switch_BoolV_def] >> irule extrequest_replay_bind >>
  reverse conj_tac >- (irule extrequest_equivariant_replay >>
    simp[extrequest_obs_read_result]) >>
  gen_tac >> Cases_on `x` >> simp[extrequest_replay_raise] >>
  Cases_on `b` >> simp[]
QED

Theorem extrequest_obs_check:
  extrequest_obs_equivariant (check p msg)
Proof
  simp[extrequest_obs_equivariant_def, check_def, assert_def] >>
  Cases_on `p` >> simp[]
QED

Theorem extrequest_obs_resolve_array:
  !cx tr slot tv subs.
    extrequest_obs_equivariant (resolve_array_element cx tr slot tv subs)
Proof
  recInduct resolve_array_element_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> simp[Once resolve_array_element_def, ignore_bind_def] >>
  irule extrequest_obs_bind >> reverse conj_tac
  >- (Cases_on `bd` >> simp[] >> irule extrequest_obs_bind >>
      simp[extrequest_obs_check] >> irule extrequest_obs_bind >>
      simp[extrequest_obs_storage_backend] >> gen_tac >>
      irule extrequest_obs_bind >> simp[extrequest_obs_check]) >>
  metis_tac[]
QED


Theorem extrequest_obs_extend_storage:
  extrequest_obs_equivariant (extend_storage_place cx tr slot tv sb)
Proof
  Cases_on `sb` >> Cases_on `tv` >>
  TRY (rename1 `ValueSubscript v` >> Cases_on `v`) >>
  simp[extend_storage_place_def, ignore_bind_def]
  >~ [`check _ "tuple index oob"`]
  >- (irule extrequest_obs_bind >> reverse conj_tac
      >- simp[extrequest_obs_check] >>
      simp[] >> irule extrequest_obs_bind >>
      simp[extrequest_obs_lift_option])
  >~ [`resolve_array_element _ _ _ _ _`]
  >- (irule extrequest_obs_bind >> reverse conj_tac
      >- simp[extrequest_obs_resolve_array] >>
      qx_gen_tac `triple` >> PairCases_on `triple` >> simp[])
  >> irule extrequest_obs_bind >> reverse conj_tac
  >- simp[extrequest_obs_lift_option] >>
  qx_gen_tac `pair` >> PairCases_on `pair` >> simp[]
QED

Theorem extrequest_obs_extend:
  extrequest_obs_equivariant (extend_place cx r sb)
Proof
  Cases_on `r`
  >- simp[extend_place_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp[extend_place_def] >>
      simp[ignore_bind_def] 
      >~ [`extend_storage_place _ _ _ _ _`]
      >- (irule extrequest_obs_bind >> simp[extrequest_obs_extend_storage]) >>
      irule extrequest_obs_bind >> simp[extrequest_obs_place_type] >>
      gen_tac >> irule extrequest_obs_bind >>
      simp[extrequest_obs_read_place] >>
      gen_tac >> irule extrequest_obs_bind >>
      simp[extrequest_obs_lift_sum]) >>
  rename1 `HashMapRef tr slot kt vt` >>
  Cases_on `sb` >> simp[extend_place_def] >>
  Cases_on `vt` >> simp[] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_lift_option]
QED

Theorem extrequest_obs_select:
  extrequest_obs_equivariant (select_result cx ty r sb)
Proof
  Cases_on `r` >> simp[select_result_def, extrequest_obs_extend] >>
  irule extrequest_obs_bind >> simp[extrequest_obs_lift_option] >>
  gen_tac >> irule extrequest_obs_bind >> simp[extrequest_obs_lift_sum]
QED

Theorem extrequest_obs_array_length:
  extrequest_obs_equivariant (result_array_length cx r)
Proof
  Cases_on `r`
  >- (simp[result_array_length_def] >> irule extrequest_obs_bind >>
      simp[extrequest_obs_read_result] >>
      Cases >> simp[] >> CASE_TAC >> simp[]) 
  >- (rename1 `PlaceR p` >> Cases_on `p`
      >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
          simp[result_array_length_def] 
          >~ [`ArrayTV et bd`] 
          >- (Cases_on `bd` >> simp[result_array_length_def] >>
              irule extrequest_obs_bind >> simp[extrequest_obs_storage_backend]) >>
          irule extrequest_obs_bind >> simp[extrequest_obs_read_result] >>
          Cases >> simp[] >> CASE_TAC >> simp[]) >>
      simp[result_array_length_def] >> irule extrequest_obs_bind >>
      simp[extrequest_obs_read_result] >>
      Cases >> simp[] >> CASE_TAC >> simp[]) >>
  simp[result_array_length_def] >> irule extrequest_obs_bind >>
  simp[extrequest_obs_read_result] >>
  Cases >> simp[] >> CASE_TAC >> simp[]
QED
