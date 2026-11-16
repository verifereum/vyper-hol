(* Outcome-input replacement commutes with source operations that do not consume it. *)
Theory vyperEvalOutcomeReplace
Ancestors vyperState vyperInterpreter

Theorem outcomes_replace_bind:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!v s oc. g v (s with outcomes := oc) =
    (FST (g v s), SND (g v s) with outcomes := oc)) ==>
  !s oc. bind f g (s with outcomes := oc) =
    (FST (bind f g s), SND (bind f g s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[bind_def] >>
  namedCases_on `f s` ["res mid"] >>
  namedCases_on `res` ["v", "e"] >> gvs[]
QED

Theorem outcomes_replace_try:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!e s oc. h e (s with outcomes := oc) =
    (FST (h e s), SND (h e s) with outcomes := oc)) ==>
  !s oc. try f h (s with outcomes := oc) =
    (FST (try f h s), SND (try f h s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[try_def] >>
  namedCases_on `f s` ["res mid"] >>
  namedCases_on `res` ["v", "e"] >> gvs[]
QED

Theorem outcomes_replace_ignore_bind:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s oc. g (s with outcomes := oc) =
    (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. ignore_bind f g (s with outcomes := oc) =
    (FST (ignore_bind f g s), SND (ignore_bind f g s) with outcomes := oc)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >>
  irule outcomes_replace_bind >> simp[]
QED

Theorem outcomes_replace_return[simp]:
  return v (s with outcomes := oc) =
    (FST (return v s), SND (return v s) with outcomes := oc)
Proof
  simp[return_def]
QED

Theorem outcomes_replace_raise[simp]:
  raise e (s with outcomes := oc) =
    (FST (raise e s), SND (raise e s) with outcomes := oc)
Proof
  simp[raise_def]
QED

Theorem outcomes_replace_finally:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s oc. g (s with outcomes := oc) =
    (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. finally f g (s with outcomes := oc) =
    (FST (finally f g s), SND (finally f g s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[finally_def] >>
  namedCases_on `f s` ["res mid"] >>
  namedCases_on `res` ["v", "e"] >>
  gvs[ignore_bind_def, bind_def, return_def, raise_def] >>
  namedCases_on `g mid` ["cleanup fin"] >>
  Cases_on `cleanup` >> gvs[]
QED

Theorem outcomes_replace_bind_guarded:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s0 v t. f s0 = (INL v,t) ==>
    !s oc. g v (s with outcomes := oc) =
      (FST (g v s), SND (g v s) with outcomes := oc)) ==>
  !s oc. bind f g (s with outcomes := oc) =
    (FST (bind f g s), SND (bind f g s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[bind_def] >>
  namedCases_on `f s` ["res mid"] >>
  namedCases_on `res` ["v", "e"] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem outcomes_replace_ignore_bind_guarded:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s0 v t. f s0 = (INL v,t) ==>
    !s oc. g (s with outcomes := oc) =
      (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. ignore_bind f g (s with outcomes := oc) =
    (FST (ignore_bind f g s), SND (ignore_bind f g s) with outcomes := oc)
Proof
  strip_tac >> rewrite_tac[ignore_bind_def] >>
  irule outcomes_replace_bind_guarded >> simp[] >> metis_tac[]
QED

Theorem outcomes_replace_try_guarded:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s0 e t. f s0 = (INR e,t) ==>
    !s oc. h e (s with outcomes := oc) =
      (FST (h e s), SND (h e s) with outcomes := oc)) ==>
  !s oc. try f h (s with outcomes := oc) =
    (FST (try f h s), SND (try f h s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[try_def] >>
  namedCases_on `f s` ["res mid"] >>
  namedCases_on `res` ["v", "e"] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem outcomes_replace_finally_guarded:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s0 r t. f s0 = (r,t) ==>
    !s oc. g (s with outcomes := oc) =
      (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. finally f g (s with outcomes := oc) =
    (FST (finally f g s), SND (finally f g s) with outcomes := oc)
Proof
  rpt strip_tac >> simp[finally_def] >>
  namedCases_on `f s` ["res mid"] >>
  `!s oc. g (s with outcomes := oc) =
      (FST (g s), SND (g s) with outcomes := oc)` by
    (first_x_assum drule >> simp[]) >>
  Cases_on `res` >>
  gvs[ignore_bind_def, bind_def, return_def, raise_def] >>
  namedCases_on `g mid` ["cleanup fin"] >>
  Cases_on `cleanup` >> gvs[]
QED

Theorem outcomes_replace_next_gas_reading:
  next_gas_reading (s with outcomes := oc) =
    (FST (next_gas_reading s), SND (next_gas_reading s) with outcomes := oc)
Proof
  Cases_on `s.gas_obs` >>
  simp[next_gas_reading_def, return_def, raise_def]
QED

Theorem outcomes_replace_basic:
  check b msg (s with outcomes := oc) =
    (FST (check b msg s), SND (check b msg s) with outcomes := oc) /\
  type_check b msg (s with outcomes := oc) =
    (FST (type_check b msg s), SND (type_check b msg s) with outcomes := oc) /\
  get_accounts (s with outcomes := oc) =
    (FST (get_accounts s), SND (get_accounts s) with outcomes := oc) /\
  get_scopes (s with outcomes := oc) =
    (FST (get_scopes s), SND (get_scopes s) with outcomes := oc) /\
  set_scopes scs (s with outcomes := oc) =
    (FST (set_scopes scs s), SND (set_scopes scs s) with outcomes := oc) /\
  update_accounts fa (s with outcomes := oc) =
    (FST (update_accounts fa s), SND (update_accounts fa s) with outcomes := oc) /\
  get_transient_storage (s with outcomes := oc) =
    (FST (get_transient_storage s), SND (get_transient_storage s) with outcomes := oc) /\
  update_transient ft (s with outcomes := oc) =
    (FST (update_transient ft s), SND (update_transient ft s) with outcomes := oc) /\
  append_logs ls (s with outcomes := oc) =
    (FST (append_logs ls s), SND (append_logs ls s) with outcomes := oc) /\
  push_log lg (s with outcomes := oc) =
    (FST (push_log lg s), SND (push_log lg s) with outcomes := oc)
Proof
  simp[check_def, type_check_def, assert_def, get_accounts_def,
    get_scopes_def, set_scopes_def, update_accounts_def,
    get_transient_storage_def, update_transient_def, append_logs_def,
    push_log_def, return_def]
QED

Theorem outcomes_replace_lifts:
  lift_option x msg (s with outcomes := oc) =
    (FST (lift_option x msg s), SND (lift_option x msg s) with outcomes := oc) /\
  lift_option_type y msg (s with outcomes := oc) =
    (FST (lift_option_type y msg s), SND (lift_option_type y msg s) with outcomes := oc) /\
  lift_sum z (s with outcomes := oc) =
    (FST (lift_sum z s), SND (lift_sum z s) with outcomes := oc) /\
  lift_sum_runtime zr (s with outcomes := oc) =
    (FST (lift_sum_runtime zr s), SND (lift_sum_runtime zr s) with outcomes := oc)
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >> Cases_on `zr` >>
  simp[lift_option_def, lift_option_type_def, lift_sum_def,
    lift_sum_runtime_def, return_def, raise_def]
QED

Theorem outcomes_replace_storage_backend:
  get_storage_backend cx tr (s with outcomes := oc) =
    (FST (get_storage_backend cx tr s), SND (get_storage_backend cx tr s) with outcomes := oc) /\
  set_storage_backend cx tr storage (s with outcomes := oc) =
    (FST (set_storage_backend cx tr storage s), SND (set_storage_backend cx tr storage s) with outcomes := oc)
Proof
  Cases_on `tr` >>
  simp[get_storage_backend_def, set_storage_backend_def, get_accounts_def,
    get_transient_storage_def, update_accounts_def, update_transient_def,
    bind_def, return_def]
QED

Theorem outcomes_replace_read_storage_slot:
  !s oc. read_storage_slot cx tr slot ty (s with outcomes := oc) =
    (FST (read_storage_slot cx tr slot ty s),
     SND (read_storage_slot cx tr slot ty s) with outcomes := oc)
Proof
  rewrite_tac[read_storage_slot_def] >>
  irule outcomes_replace_bind >>
  simp[outcomes_replace_storage_backend, outcomes_replace_lifts]
QED

Theorem outcomes_replace_write_storage_slot:
  !s oc. write_storage_slot cx tr slot ty v (s with outcomes := oc) =
    (FST (write_storage_slot cx tr slot ty v s),
     SND (write_storage_slot cx tr slot ty v s) with outcomes := oc)
Proof
  rewrite_tac[write_storage_slot_def, ignore_bind_def] >>
  irule outcomes_replace_bind >>
  simp[check_not_static_def, outcomes_replace_basic] >>
  irule outcomes_replace_bind >>
  simp[outcomes_replace_storage_backend] >>
  gen_tac >> irule outcomes_replace_bind >>
  simp[outcomes_replace_lifts, outcomes_replace_storage_backend]
QED

Theorem outcomes_replace_get_address_immutables:
  get_address_immutables cx (s with outcomes := oc) =
    (FST (get_address_immutables cx s),
     SND (get_address_immutables cx s) with outcomes := oc)
Proof
  rewrite_tac[get_address_immutables_def, outcomes_replace_lifts] >> simp[]
QED

Theorem outcomes_replace_get_immutables:
  !s oc. get_immutables cx src (s with outcomes := oc) =
    (FST (get_immutables cx src s),
     SND (get_immutables cx src s) with outcomes := oc)
Proof
  rewrite_tac[get_immutables_def] >> irule outcomes_replace_bind >>
  simp[outcomes_replace_get_address_immutables]
QED

Theorem outcomes_replace_read_place:
  !s oc. read_place cx p (s with outcomes := oc) =
    (FST (read_place cx p s), SND (read_place cx p s) with outcomes := oc)
Proof
  Cases_on `p` >> rewrite_tac[read_place_def]
  >- simp[outcomes_replace_read_storage_slot]
  >- (irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts])
  >> irule outcomes_replace_bind >> simp[outcomes_replace_get_immutables] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts]
QED

Theorem outcomes_replace_read_result:
  !s oc. read_result cx tv (s with outcomes := oc) =
    (FST (read_result cx tv s), SND (read_result cx tv s) with outcomes := oc)
Proof
  Cases_on `tv` >> simp[read_result_def, outcomes_replace_read_place,
    return_def, raise_def]
QED

Theorem outcomes_replace_read_results:
  !s oc. read_results cx tvs (s with outcomes := oc) =
    (FST (read_results cx tvs s), SND (read_results cx tvs s) with outcomes := oc)
Proof
  Induct_on `tvs` >> rewrite_tac[read_results_def] >- simp[return_def] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_read_result] >>
  gen_tac >> irule outcomes_replace_bind >> simp[]
QED

Theorem outcomes_replace_place_type_value:
  !s oc. place_type_value cx p (s with outcomes := oc) =
    (FST (place_type_value cx p s),
     SND (place_type_value cx p s) with outcomes := oc)
Proof
  Cases_on `p` >> rewrite_tac[place_type_value_def] >- simp[]
  >- (irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts])
  >> irule outcomes_replace_bind >> simp[outcomes_replace_get_immutables] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts]
QED

Theorem outcomes_replace_cond:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s oc. g (s with outcomes := oc) =
    (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. (if b then f else g) (s with outcomes := oc) =
    (FST ((if b then f else g) s),
     SND ((if b then f else g) s) with outcomes := oc)
Proof
  Cases_on `b` >> simp[]
QED

Theorem outcomes_replace_conditional_result:
  !s oc. conditional_result cx tv (s with outcomes := oc) =
    (FST (conditional_result cx tv s),
     SND (conditional_result cx tv s) with outcomes := oc)
Proof
  Cases_on `tv` >> rewrite_tac[conditional_result_def]
  >- simp[return_def]
  >- (irule outcomes_replace_bind >> simp[outcomes_replace_place_type_value] >>
      gen_tac >> irule outcomes_replace_cond >> simp[return_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_read_place, return_def])
  >> simp[raise_def]
QED

Theorem outcomes_replace_precompile_call_success:
  ~precompile_builtin bt ==>
  !s oc. precompile_call_success bt (s with outcomes := oc) =
    (FST (precompile_call_success bt s),
     SND (precompile_call_success bt s) with outcomes := oc)
Proof
  simp[return_def]
QED

Theorem outcomes_replace_set_address_immutables:
  set_address_immutables cx imms (s with outcomes := oc) =
    (FST (set_address_immutables cx imms s),
     SND (set_address_immutables cx imms s) with outcomes := oc)
Proof
  simp[set_address_immutables_def, return_def]
QED

Theorem outcomes_replace_set_immutable:
  !s oc. set_immutable cx src nm ty v (s with outcomes := oc) =
    (FST (set_immutable cx src nm ty v s),
     SND (set_immutable cx src nm ty v s) with outcomes := oc)
Proof
  rewrite_tac[set_immutable_def] >> irule outcomes_replace_bind >>
  simp[outcomes_replace_get_address_immutables,
       outcomes_replace_set_address_immutables]
QED

Theorem outcomes_replace_write_place:
  !s oc. write_place cx p v (s with outcomes := oc) =
    (FST (write_place cx p v s), SND (write_place cx p v s) with outcomes := oc)
Proof
  Cases_on `p` >> rewrite_tac[write_place_def]
  >- simp[outcomes_replace_write_storage_slot]
  >- (irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> PairCases_on `v'` >>
      simp[ignore_bind_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic] >> irule outcomes_replace_bind >>
      simp[outcomes_replace_lifts, outcomes_replace_basic])
  >> irule outcomes_replace_bind >> simp[outcomes_replace_get_immutables] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> irule outcomes_replace_bind >>
  simp[outcomes_replace_lifts, outcomes_replace_set_immutable]
QED

Theorem outcomes_replace_scopes:
  push_scope (s with outcomes := oc) =
    (FST (push_scope s), SND (push_scope s) with outcomes := oc) /\
  push_scope_with_var nm ty v (s with outcomes := oc) =
    (FST (push_scope_with_var nm ty v s),
     SND (push_scope_with_var nm ty v s) with outcomes := oc) /\
  pop_scope (s with outcomes := oc) =
    (FST (pop_scope s), SND (pop_scope s) with outcomes := oc)
Proof
  Cases_on `s.scopes` >>
  simp[push_scope_def, push_scope_with_var_def, pop_scope_def,
    return_def, raise_def]
QED

Theorem outcomes_replace_new_variable:
  !s oc. new_variable nm ty v (s with outcomes := oc) =
    (FST (new_variable nm ty v s),
     SND (new_variable nm ty v s) with outcomes := oc)
Proof
  rewrite_tac[new_variable_def] >> irule outcomes_replace_bind >>
  simp[outcomes_replace_basic] >> gen_tac >>
  rename1 `lookup_scopes nm env` >>
  Cases_on `env` >> rewrite_tac[ignore_bind_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_basic, raise_def]
QED

Theorem outcomes_replace_handlers:
  handle_loop_exception e (s with outcomes := oc) =
    (FST (handle_loop_exception e s),
     SND (handle_loop_exception e s) with outcomes := oc) /\
  handle_function e (s with outcomes := oc) =
    (FST (handle_function e s), SND (handle_function e s) with outcomes := oc)
Proof
  Cases_on `e` >>
  simp[handle_loop_exception_def, handle_function_def, return_def, raise_def]
QED

Theorem outcomes_replace_get_place:
  get_place tv (s with outcomes := oc) =
    (FST (get_place tv s), SND (get_place tv s) with outcomes := oc)
Proof
  Cases_on `tv` >> simp[get_place_def, return_def, raise_def]
QED

Theorem outcomes_replace_resolve_array_element:
  !slot ty s oc. resolve_array_element cx tr slot ty subs (s with outcomes := oc) =
    (FST (resolve_array_element cx tr slot ty subs s),
     SND (resolve_array_element cx tr slot ty subs s) with outcomes := oc)
Proof
  Induct_on `subs`
  >- (rpt gen_tac >> Cases_on `ty` >>
      simp[resolve_array_element_def, return_def]) >>
  map_every qx_gen_tac [`sb`, `slot`, `ty`] >>
  Cases_on `ty` >> simp[resolve_array_element_def, return_def] >>
  rename1 `ArrayTV ety bd` >>
  Cases_on `sb` >> simp[resolve_array_element_def, raise_def] >>
  rename1 `ValueSubscript v` >>
  Cases_on `v` >> simp[resolve_array_element_def, raise_def] >>
  irule outcomes_replace_bind >> simp[] >>
  Cases_on `bd` >> simp[ignore_bind_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_basic, return_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_storage_backend] >>
  gen_tac >> irule outcomes_replace_bind >>
  simp[outcomes_replace_basic, return_def]
QED

Theorem outcomes_replace_lookup_flag_mem:
  !s oc. lookup_flag_mem cx fid mid (s with outcomes := oc) =
    (FST (lookup_flag_mem cx fid mid s),
     SND (lookup_flag_mem cx fid mid s) with outcomes := oc)
Proof
  PairCases_on `fid` >> rewrite_tac[lookup_flag_mem_def] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def]
QED

Theorem outcomes_replace_lookup_global:
  !s oc. lookup_global cx src nm (s with outcomes := oc) =
    (FST (lookup_global cx src nm s),
     SND (lookup_global cx src nm s) with outcomes := oc)
Proof
  rewrite_tac[lookup_global_def] >> irule outcomes_replace_bind >>
  rewrite_tac[outcomes_replace_lifts] >> simp[] >> qx_gen_tac `ts` >>
  simp[] >>
  Cases_on `find_var_decl_by_name nm ts`
  >- (simp[] >> irule outcomes_replace_bind >>
      simp[outcomes_replace_get_immutables] >> gen_tac >>
      BasicProvers.TOP_CASE_TAC >> simp[return_def, raise_def]) >>
  rename1 `SOME decl` >> PairCases_on `decl` >> Cases_on `decl0` >> simp[] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def] >>
  simp[ignore_bind_def, bind_def, record_storage_event_def, return_def]
QED

Theorem outcomes_replace_result_array_length:
  !s oc. result_array_length cx tv (s with outcomes := oc) =
    (FST (result_array_length cx tv s),
     SND (result_array_length cx tv s) with outcomes := oc)
Proof
  Cases_on `tv`
  >- (rewrite_tac[result_array_length_def] >> irule outcomes_replace_bind >>
      simp[outcomes_replace_read_result] >>
      Cases >> simp[return_def, raise_def] >>
      Cases_on `a` >> simp[return_def])
  >- (rename1 `PlaceR p` >> Cases_on `p`
      >- (rename1 `StoragePlace tr slot ty` >> Cases_on `ty` >>
          rewrite_tac[result_array_length_def]
          >~ [`ArrayTV et bd`]
          >- (Cases_on `bd` >> rewrite_tac[result_array_length_def] >>
              simp[return_def] >> irule outcomes_replace_bind >>
              simp[outcomes_replace_storage_backend, return_def])
          >> irule outcomes_replace_bind >> simp[outcomes_replace_read_result] >>
          Cases >> simp[return_def, raise_def] >>
          Cases_on `a` >> simp[return_def])
      >> rewrite_tac[result_array_length_def] >> irule outcomes_replace_bind >>
      simp[outcomes_replace_read_result] >>
      Cases >> simp[return_def, raise_def] >>
      Cases_on `a` >> simp[return_def])
  >> rewrite_tac[result_array_length_def] >> irule outcomes_replace_bind >>
  simp[outcomes_replace_read_result] >>
  Cases >> simp[return_def, raise_def] >>
  Cases_on `a` >> simp[return_def]
QED

Theorem outcomes_replace_array_iterator_results:
  !s oc. array_iterator_results cx ty res (s with outcomes := oc) =
    (FST (array_iterator_results cx ty res s),
     SND (array_iterator_results cx ty res s) with outcomes := oc)
Proof
  Cases_on `res` >>
  TRY (rename1 `PlaceR p` >> Cases_on `p` >>
       TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
            TRY (rename1 `ArrayTV etv bd` >> Cases_on `bd`))) >>
  simp_tac (srw_ss()) [array_iterator_results_def] >>
  rpt (FIRST [irule outcomes_replace_bind, irule outcomes_replace_ignore_bind,
              gen_tac, conj_tac] >>
       simp[outcomes_replace_read_result, outcomes_replace_lifts,
            outcomes_replace_basic, outcomes_replace_result_array_length,
            return_def, LET_THM])
QED

Theorem outcomes_replace_switch_BoolV:
  (!s oc. f (s with outcomes := oc) =
    (FST (f s), SND (f s) with outcomes := oc)) /\
  (!s oc. g (s with outcomes := oc) =
    (FST (g s), SND (g s) with outcomes := oc)) ==>
  !s oc. switch_BoolV cx tv f g (s with outcomes := oc) =
    (FST (switch_BoolV cx tv f g s),
     SND (switch_BoolV cx tv f g s) with outcomes := oc)
Proof
  strip_tac >> rewrite_tac[switch_BoolV_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_read_result] >>
  gen_tac >> irule outcomes_replace_cond >> simp[] >>
  irule outcomes_replace_cond >> simp[raise_def]
QED

Theorem outcomes_replace_extend_storage_place:
  !s oc. extend_storage_place cx tr slot ty sb (s with outcomes := oc) =
    (FST (extend_storage_place cx tr slot ty sb s),
     SND (extend_storage_place cx tr slot ty sb s) with outcomes := oc)
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript v` >> Cases_on `v` >> Cases_on `ty` >>
      simp[extend_storage_place_def, raise_def, ignore_bind_def] >>
      irule outcomes_replace_bind >>
      simp[outcomes_replace_basic, outcomes_replace_lifts,
        outcomes_replace_resolve_array_element, ignore_bind_def, return_def]
      >- (irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def])
      >> qx_gen_tac `tup` >> PairCases_on `tup` >> simp[return_def])
  >> Cases_on `ty` >> simp[extend_storage_place_def, raise_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> pairarg_tac >> simp[return_def]
QED

Theorem outcomes_replace_extend_place:
  !s oc. extend_place cx tv sb (s with outcomes := oc) =
    (FST (extend_place cx tv sb s),
     SND (extend_place cx tv sb s) with outcomes := oc)
Proof
  Cases_on `tv` >- simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      rewrite_tac[extend_place_def]
      >- (irule outcomes_replace_bind >>
          simp[outcomes_replace_extend_storage_place, return_def])
      >> irule outcomes_replace_bind >> simp[outcomes_replace_place_type_value] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_read_place] >>
      gen_tac >> rewrite_tac[ignore_bind_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def])
  >> rename1 `HashMapRef tr slot kt vt` >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  Cases_on `vt` >> simp[return_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def] >>
  simp[ignore_bind_def, bind_def, record_storage_event_def, return_def]
QED

Theorem outcomes_replace_select_result:
  !s oc. select_result cx ty tv sb (s with outcomes := oc) =
    (FST (select_result cx ty tv sb s),
     SND (select_result cx ty tv sb s) with outcomes := oc)
Proof
  Cases_on `tv` >> rewrite_tac[select_result_def]
  >- (irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> irule outcomes_replace_bind >>
      simp[outcomes_replace_lifts, return_def])
  >> simp[outcomes_replace_extend_place]
QED

Theorem outcomes_replace_append_place:
  !s oc. append_place cx p v (s with outcomes := oc) =
    (FST (append_place cx p v s),
     SND (append_place cx p v s) with outcomes := oc)
Proof
  Cases_on `p`
  >- (rename1 `StoragePlace tr slot ty` >>
      Cases_on `ty` >> simp[append_place_def, ignore_bind_def]
      >~ [`ArrayTV ety bd`]
      >- (Cases_on `bd` >> simp[append_place_def, ignore_bind_def]
          >- (irule outcomes_replace_bind >> simp[outcomes_replace_place_type_value] >>
              gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_read_place] >>
              gen_tac >> irule outcomes_replace_bind >>
              simp[outcomes_replace_lifts, outcomes_replace_write_place])
          >> irule outcomes_replace_bind >> simp[outcomes_replace_storage_backend] >>
          gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
          irule outcomes_replace_bind >> simp[outcomes_replace_write_storage_slot])
      >> irule outcomes_replace_bind >> simp[outcomes_replace_place_type_value] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_read_place] >>
      gen_tac >> irule outcomes_replace_bind >>
      simp[outcomes_replace_lifts, outcomes_replace_write_place])
  >> rewrite_tac[append_place_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_place_type_value] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_read_place] >>
  gen_tac >> irule outcomes_replace_bind >>
  simp[outcomes_replace_lifts, outcomes_replace_write_place]
QED

Theorem outcomes_replace_pop_place:
  !s oc. pop_place cx p (s with outcomes := oc) =
    (FST (pop_place cx p s), SND (pop_place cx p s) with outcomes := oc)
Proof
  Cases_on `p`
  >- (rename1 `StoragePlace tr slot ty` >> Cases_on `ty` >>
      simp[pop_place_def, raise_def] >> rename1 `ArrayTV ety bd` >>
      Cases_on `bd` >> simp[pop_place_def, raise_def, ignore_bind_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_storage_backend] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_write_storage_slot, return_def])
  >- (rewrite_tac[pop_place_def, ignore_bind_def] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      qx_gen_tac `tup` >> PairCases_on `tup` >> simp[] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_basic] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
      qx_gen_tac `tup` >> PairCases_on `tup` >> simp[] >>
      irule outcomes_replace_bind >> simp[outcomes_replace_basic, return_def])
  >> rewrite_tac[pop_place_def, ignore_bind_def] >>
  irule outcomes_replace_bind >> simp[outcomes_replace_get_immutables] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts] >>
  gen_tac >> irule outcomes_replace_bind >>
  simp[outcomes_replace_set_immutable, return_def]
QED

