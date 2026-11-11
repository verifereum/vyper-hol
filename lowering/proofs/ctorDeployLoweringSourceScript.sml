(* A piece of deploy_unit_execution_correct (ctorDeployLowering).
   ADMITTED until proved. *)
Theory ctorDeployLoweringSource
Ancestors
  ctorDeployLoweringDefs vyperState vyperInterpreter vyperScopePreservation
  supportedStmtTraverse supportedExprTraverse e2eDeployDefs
  vyperTypeDeploymentSoundness evalNoHalt

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
  gen_tac >> irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def]
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
  irule outcomes_replace_bind >> simp[outcomes_replace_lifts, return_def]
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

Theorem send_call_value_transport:
  send_call_value mut cx
    (s with <|scopes := scs; outcomes := oc; gas_obs := gobs|>) =
  (FST (send_call_value mut cx s),
   SND (send_call_value mut cx s) with
     <|scopes := scs; outcomes := oc; gas_obs := gobs|>)
Proof
  Cases_on `cx.txn.value = 0` >>
  simp[send_call_value_def, transfer_value_def, COND_RATOR,
    ignore_bind_def, bind_def, check_def, assert_def, get_accounts_def,
    update_accounts_def, return_def, raise_def] >>
  Cases_on `mut = Payable` >>
  simp[bind_def, assert_def, get_accounts_def, update_accounts_def,
    return_def, raise_def, COND_RATOR] >>
  Cases_on `cx.txn.sender = cx.txn.target` >>
  simp[bind_def, assert_def, get_accounts_def, update_accounts_def,
    return_def, raise_def, COND_RATOR] >>
  rpt IF_CASES_TAC >> simp[bind_def, return_def, raise_def, update_accounts_def]
QED

Theorem lock_if_nr_transport:
  lock_if_nr cx nr view
    (s with <|scopes := scs; outcomes := oc; gas_obs := gobs|>) =
  (FST (lock_if_nr cx nr view s),
   SND (lock_if_nr cx nr view s) with
     <|scopes := scs; outcomes := oc; gas_obs := gobs|>)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  simp[acquire_nonreentrant_lock_def, ignore_bind_def, bind_def,
    get_transient_storage_def, update_transient_def, return_def,
    raise_def, check_not_static_def, check_def, assert_def, COND_RATOR] >>
  rpt IF_CASES_TAC >>
  simp[bind_def, return_def, raise_def, update_transient_def, assert_def] >>
  Cases_on `view` >> simp[]
QED

Theorem send_call_value_scopes:
  send_call_value mut cx s = (r,t) ==> t.scopes = s.scopes
Proof
  Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
  simp[send_call_value_def, ignore_bind_def, bind_def, check_def,
       assert_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[transfer_value_scopes]
QED

Theorem lock_if_nr_scopes:
  lock_if_nr cx nr view s = (r,t) ==> t.scopes = s.scopes
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def] >>
  Cases_on `view` >> Cases_on `cx.txn.is_static` >>
  simp[ignore_bind_def, bind_def, check_not_static_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[acquire_nonreentrant_lock_scopes]
QED

Theorem deploy_ctor_prefix_transport:
  ignore_bind (send_call_value mut cx) (lock_if_nr cx nr (is_view_mut mut))
    (initial_state am [env] with <|outcomes := NONE; requests := []|>) =
    (INL (), es0) ==>
  ignore_bind (send_call_value mut cx)
    (ignore_bind (set_scopes [env]) (lock_if_nr cx nr (is_view_mut mut)))
    (initial_state am [FEMPTY] with
      <|outcomes := oc; requests := []; gas_obs := gobs|>) =
    (INL (), es0 with <|gas_obs := gobs; outcomes := oc|>)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `ignore_bind _ _ s0` >>
  `s0.scopes = [env]` by simp[Abbr `s0`, initial_state_def] >>
  `initial_state am [FEMPTY] with
     <|outcomes := oc; requests := []; gas_obs := gobs|> =
   s0 with <|scopes := [FEMPTY]; gas_obs := gobs; outcomes := oc|>` by
    simp[Abbr `s0`, initial_state_def] >>
  namedCases_on `send_call_value mut cx s0` ["r mid"] >>
  Cases_on `r` >>
  gvs[ignore_bind_def, bind_def, Excl "lock_if_nr_def"] >>
  `mid.scopes = [env]` by metis_tac[send_call_value_scopes] >>
  `es0.scopes = [env]` by metis_tac[lock_if_nr_scopes] >>
  simp[send_call_value_transport, Excl "lock_if_nr_def"] >>
  simp[bind_def, set_scopes_def, return_def, Excl "lock_if_nr_def"] >>
  simp[send_call_value_transport, lock_if_nr_transport,
       Excl "lock_if_nr_def"] >>
  simp[evaluation_state_component_equality]
QED

(* load_contract is deploy_ctor_finish of the constructor body's run from
   deploy_ctor_start, at any gas observations.  The body is call-free
   (constructor_call_free), so it never reads the call outcomes: a run with
   any outcomes field gives the same result. *)
Theorem deploy_ctor_return_none:
  !tops am tx mut nr body am_c es0 gobs oc v st.
  deploy_source_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
  eval_stmts (deploy_evaluation_context tops am tx) body
    (es0 with <|gas_obs := gobs; outcomes := oc|>) =
      (INR (ReturnException v),st) ==> v = NoneV
Proof
  simp[ctorDeployDefsTheory.deploy_source_ok_def, deploy_typing_ok_def,
    deploy_ctor_start_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >> rpt strip_tac >>
  `context_well_typed (deploy_evaluation_context tops am tx)` by
    (gvs[vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
      vyperTypeInvariantsTheory.context_well_typed_def,
      deploy_evaluation_context_def, initial_evaluation_context_def]) >>
  drule deploy_ctor_prefix_transport >>
  disch_then (qspecl_then [`oc`, `gobs`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx bdy` >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := oc; requests := []; gas_obs := gobs|>) =
       (INR (ReturnException v),st)` by
    (gvs[ignore_bind_def, bind_def, AllCaseEqs(),
      Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  gvs[lock_if_nr_def, is_view_mut_def] >>
  `cx = (initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources)
      am.layouts (tx with created_in_tx := T) NONE with in_deploy := T)` by
    simp[Abbr `cx`, deploy_evaluation_context_def] >>
  `ALOOKUP [(NONE,tops)] NONE = SOME tops` by simp[] >>
  qpat_x_assum `supported_program _` kall_tac >>
  qpat_x_assum `constructor_call_free _` kall_tac >>
  qpat_x_assum `checked_deployment_constants_ready _ _ _ _` kall_tac >>
  qpat_x_assum `deploy_storage_ok _ _ _` kall_tac >>
  drule_at (Pat `_ = (INR (ReturnException _),_)`)
    checked_constructor_prefix_return_typed >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`tx.args`, `[]`] mp_tac) >>
  gvs[Abbr `cx`, deploy_evaluation_context_def]
QED

Theorem deploy_ctor_source_run_none:
  !tops am tx mut nr body am_c es0 gobs res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut,nr,body,am_c,es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <|gas_obs := gobs; outcomes := NONE|>) = (res,st) ==>
    load_contract NONE gobs am tx [(NONE,tops)] [] =
      deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
        nr mut am_c res st
Proof
  rpt gen_tac >> strip_tac >>
  `!v. res = INR (ReturnException v) ==> v = NoneV` by
    (rpt strip_tac >> irule deploy_ctor_return_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexistsl [`gobs`, `NONE`, `st`] >> gvs[]) >>
  `res <> INR HaltException` by
    (strip_tac >>
     gvs[ctorDeployDefsTheory.deploy_source_ok_def, deploy_ctor_start_def,
         Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
     rename1 `lookup_function NONE _ Deploy tops = SOME (_,_,_,_,_,cbody)` >>
     `get_module_code (deploy_evaluation_context tops am tx) NONE = SOME tops` by
       simp[deploy_evaluation_context_def, vyperInterpreterTheory.initial_evaluation_context_def,
            vyperContextTheory.get_module_code_def] >>
     `!st st'. eval_stmts (deploy_evaluation_context tops am tx) cbody st <>
               (INR HaltException, st')` by
       (rpt gen_tac >> irule deploy_body_no_halt >> metis_tac[]) >>
     metis_tac[]) >>
  gvs[deploy_ctor_start_def, Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  drule deploy_ctor_prefix_transport >>
  disch_then (qspecl_then [`NONE`, `gobs`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx bdy` >>
  `ignore_bind (send_call_value mut cx)
     (ignore_bind (set_scopes [env])
       (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy)))
     (initial_state am_c [FEMPTY] with
       <|outcomes := NONE; requests := []; gas_obs := gobs|>) = (res,st)` by
    (gvs[ignore_bind_def, bind_def, AllCaseEqs(),
      Excl "lock_if_nr_def", Excl "is_view_mut_def"]) >>
  `deploy_evaluation_context tops
      (am with <|exports updated_by CONS (tx.target,[]);
        immutables updated_by CONS (tx.target,imms)|>) tx = cx` by
    simp[Abbr `cx`, deploy_evaluation_context_def] >>
  `cx.in_deploy /\ cx.txn = tx with created_in_tx := T` by
    simp[Abbr `cx`, deploy_evaluation_context_def, initial_evaluation_context_def] >>
  `bind (eval_external_defaults cx [])
      (\dflt_vs. case bind_arguments (type_env_all_modules [(NONE,tops)]) args
          (tx.args ++ dflt_vs) of
        NONE => raise (Error (RuntimeError "call bind_arguments"))
      | SOME env => ignore_bind (set_scopes [env])
          (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy))) =
    ignore_bind (set_scopes [env])
      (ignore_bind (lock_if_nr cx nr (is_view_mut mut)) (eval_stmts cx bdy))` by
    simp[FUN_EQ_THM, bind_def, eval_external_defaults_nil] >>
  simp[load_contract_def, call_external_function_def,
    GSYM deploy_evaluation_context_def,
    eval_external_defaults_nil,
    Excl "lock_if_nr_def", Excl "is_view_mut_def"] >>
  qpat_x_assum `deploy_source_ok _ _ _` kall_tac >>
  qpat_x_assum `lookup_function _ _ _ _ = _` kall_tac >>
  qpat_x_assum `LENGTH _ = _` kall_tac >>
  qpat_x_assum `bind_arguments _ _ _ = _` kall_tac >>
  qpat_x_assum `initial_immutables _ _ = _` kall_tac >>
  qpat_x_assum `evaluate_all_constants _ _ _ _ = _` kall_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` kall_tac >>
  rpt (qpat_x_assum `ignore_bind _ _ _ = _` kall_tac) >>
  qpat_x_assum `bind _ _ = _` kall_tac >>
  Cases_on `res`
  >- (Cases_on `x` >>
      simp[deploy_ctor_finish_def, Abbr `cx`, unlock_if_nr_def] >>
      qmatch_goalsub_abbrev_tac `action st` >>
      namedCases_on `action st` ["rr ss"] >> Cases_on `rr` >> simp[] >>
      qpat_x_assum `action st = _` mp_tac >> simp[Abbr `action`] >>
      Cases_on `(deploy_evaluation_context tops am tx).nonreentrant_slot` >>
      rw[return_def, release_nonreentrant_lock_def, bind_def,
         get_transient_storage_def, update_transient_def]) >>
  rename1 `INR ex` >> Cases_on `ex` >>
  gvs[deploy_ctor_finish_def, Abbr `cx`, unlock_if_nr_def] >>
  simp[vyperValueOperationTheory.safe_cast_def] >>
  qmatch_goalsub_abbrev_tac `action st` >>
  namedCases_on `action st` ["rr ss"] >> Cases_on `rr` >> simp[] >>
  qpat_x_assum `action st = _` mp_tac >> simp[Abbr `action`] >>
  Cases_on `(deploy_evaluation_context tops am tx).nonreentrant_slot` >>
  rw[return_def, release_nonreentrant_lock_def, bind_def,
     get_transient_storage_def, update_transient_def]
QED

Theorem deploy_ctor_finish_outcomes:
  deploy_ctor_finish tops tx cx nr mut am_c res (st with outcomes := oc) =
  deploy_ctor_finish tops tx cx nr mut am_c res st
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[deploy_ctor_finish_def, unlock_if_nr_def,
    release_nonreentrant_lock_def, update_transient_def,
    return_def, raise_def, abstract_machine_from_state_def] >>
  Cases_on `mut` >>
  simp[bind_def, get_transient_storage_def, update_transient_def,
    return_def, abstract_machine_from_state_def]
QED

Theorem outcomes_replace_evaluate_call_free:
  (!cx stmt. ~supported_stmt_expr_exists constructor_call_root stmt ==>
    !s oc. eval_stmt cx stmt (s with outcomes := oc) =
      (FST (eval_stmt cx stmt s), SND (eval_stmt cx stmt s) with outcomes := oc)) /\
  (!cx body. ~supported_stmts_expr_exists constructor_call_root body ==>
    !s oc. eval_stmts cx body (s with outcomes := oc) =
      (FST (eval_stmts cx body s), SND (eval_stmts cx body s) with outcomes := oc)) /\
  (!cx it. ~supported_iterator_exists constructor_call_root it ==>
    !s oc. eval_iterator cx it (s with outcomes := oc) =
      (FST (eval_iterator cx it s), SND (eval_iterator cx it s) with outcomes := oc)) /\
  (!cx ty nm body vs. ~supported_stmts_expr_exists constructor_call_root body ==>
    !s oc. eval_for cx ty nm body vs (s with outcomes := oc) =
      (FST (eval_for cx ty nm body vs s), SND (eval_for cx ty nm body vs s) with outcomes := oc)) /\
  (!cx e. ~supported_expr_exists constructor_call_root e ==>
    !s oc. eval_expr cx e (s with outcomes := oc) =
      (FST (eval_expr cx e s), SND (eval_expr cx e s) with outcomes := oc)) /\
  (!cx es. ~supported_exprs_exists constructor_call_root es ==>
    !s oc. eval_exprs cx es (s with outcomes := oc) =
      (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with outcomes := oc)) /\
  (!cx target. ~supported_target_exists constructor_call_root target ==>
    !s oc. eval_base_place cx target (s with outcomes := oc) =
      (FST (eval_base_place cx target s), SND (eval_base_place cx target s) with outcomes := oc)) /\
  (!cx target. ~supported_target_exists constructor_call_root target ==>
    !s oc. eval_target_place cx target (s with outcomes := oc) =
      (FST (eval_target_place cx target s), SND (eval_target_place cx target s) with outcomes := oc)) /\
  (!cx target v. ~supported_assignment_exists constructor_call_root target ==>
    !s oc. assign_tuple_targets cx target v (s with outcomes := oc) =
      (FST (assign_tuple_targets cx target v s), SND (assign_tuple_targets cx target v s) with outcomes := oc)) /\
  (!cx targets vs. ~supported_assignments_exists constructor_call_root targets ==>
    !s oc. assign_tuple_target_list cx targets vs (s with outcomes := oc) =
      (FST (assign_tuple_target_list cx targets vs s), SND (assign_tuple_target_list cx targets vs s) with outcomes := oc)) /\
  (!cx es. ~supported_exprs_exists constructor_call_root es ==>
    !s oc. eval_expr_results cx es (s with outcomes := oc) =
      (FST (eval_expr_results cx es s), SND (eval_expr_results cx es s) with outcomes := oc))
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def,
    supported_assignment_exists_def, supported_iterator_exists_def,
    supported_assert_exists_def, supported_raise_exists_def,
    constructor_call_root_def] >>
  rpt strip_tac >> map_every qid_spec_tac [`oc`, `s`] >>
  gvs[] >> once_rewrite_tac[evaluate_def] >>
  simp[outcomes_replace_lookup_global, outcomes_replace_lookup_flag_mem,
    return_def, raise_def]
  >~ [`builtin_args_length_ok bt (LENGTH es)`]
  >- (match_mp_tac outcomes_replace_ignore_bind_guarded >>
      simp[outcomes_replace_basic] >>
      rpt gen_tac >> strip_tac >>
      match_mp_tac outcomes_replace_bind >> conj_tac
      >- (Cases_on `bt = Len`
          >- (gvs[] >> match_mp_tac outcomes_replace_bind >> conj_tac
              >- (first_x_assum irule >> reverse conj_tac
                  >- (goal_assum (drule_at Any)) >>
                  Cases_on `es` >>
                  gvs[type_check_def, assert_def, raise_def,
                      vyperContextTheory.builtin_args_length_ok_def,
                      supported_exprs_exists_every]) >>
              simp[outcomes_replace_bind, outcomes_replace_result_array_length,
                   return_def]) >>
          Cases_on `bt = Bop In \/ bt = Bop NotIn`
          >- (gvs[] >>
              (match_mp_tac outcomes_replace_bind >> conj_tac
               >- metis_tac[] >>
               simp[outcomes_replace_ignore_bind, outcomes_replace_bind,
                    outcomes_replace_basic, outcomes_replace_lifts])) >>
          Cases_on `bt = Env MsgGas`
          >- gvs[outcomes_replace_next_gas_reading] >>
          gvs[] >> match_mp_tac outcomes_replace_bind >> conj_tac
          >- metis_tac[] >>
          simp[outcomes_replace_bind, outcomes_replace_ignore_bind,
               outcomes_replace_basic, outcomes_replace_lifts,
               outcomes_replace_precompile_call_success, return_def]) >>
      simp[return_def]) >>
  rpt (FIRST [first_assum ACCEPT_TAC,
      goal_assum (drule_at Any),
      first_assum (fn th => irule th >> rpt conj_tac >>
        FIRST [goal_assum (drule_at Any) >> NO_TAC,
               gvs[] >> NO_TAC]),
      (first_assum irule >> goal_assum (drule_at Any)),
      irule outcomes_replace_bind_guarded,
      irule outcomes_replace_ignore_bind_guarded,
      irule outcomes_replace_finally_guarded,
      irule outcomes_replace_try_guarded,
      irule outcomes_replace_switch_BoolV,
      IF_CASES_TAC,
      conj_tac, gen_tac, disch_tac] >>
    simp[outcomes_replace_basic, outcomes_replace_lifts,
      outcomes_replace_read_result, outcomes_replace_read_place,
      outcomes_replace_place_type_value, outcomes_replace_write_place,
      outcomes_replace_new_variable, outcomes_replace_scopes,
      outcomes_replace_handlers, outcomes_replace_append_place,
      outcomes_replace_pop_place, outcomes_replace_select_result,
      outcomes_replace_extend_place, outcomes_replace_get_place,
      outcomes_replace_result_array_length, outcomes_replace_conditional_result,
      outcomes_replace_next_gas_reading, return_def, raise_def])
  (* the seven goals left: two custom errors, a tuple-target value, struct
     fields, the array iterator, the for loop, a builtin arity clash *)
  >>~- ([`order_custom_error_args`],
    (Cases_on `err` >> simp[] >>
        rpt BasicProvers.TOP_CASE_TAC >> simp[raise_def] >>
        drule vyperASTTheory.order_custom_error_args_perm >> strip_tac >>
        rename1 `order_custom_error_args params (CustomError id pos kws) = SOME es` >>
        `~supported_exprs_exists constructor_call_root es` by
          (simp[supported_exprs_exists_every] >>
           metis_tac[sortingTheory.PERM_EVERY]) >>
        gvs[] >>
        `!s oc. eval_exprs cx es (s with outcomes := oc) =
          (FST (eval_exprs cx es s), SND (eval_exprs cx es s) with outcomes := oc)` by
          metis_tac[] >>
        map_every qid_spec_tac [`oc`, `s`] >>
        irule outcomes_replace_bind >> simp[] >> gen_tac >>
        irule outcomes_replace_bind >> simp[outcomes_replace_lifts, raise_def]))
  >~ [`TupleV _`]
  >- (Cases_on `v` >> simp[raise_def] >> Cases_on `a` >> gvs[raise_def])
  >~ [`eval_exprs _ (MAP SND _)`]
  >- (gvs[supported_fields_exists_every, supported_exprs_exists_every,
          listTheory.EVERY_MAP] >>
      metis_tac[outcomes_replace_array_iterator_results])
  >~ [`array_iterator_results _ _ _ (_ with outcomes := _)`]
  >- metis_tac[outcomes_replace_array_iterator_results]
  >~ [`eval_for _ _ _ _ _ (_ with outcomes := _)`]
  >- metis_tac[]
  >> Cases_on `es` >>
  gvs[type_check_def, assert_def, raise_def,
      vyperContextTheory.builtin_args_length_ok_def,
      supported_exprs_exists_every]
QED

Theorem deploy_ctor_source_run:
  !tops am tx mut nr body am_c es0 gobs oc res st.
    deploy_source_ok tops am tx /\ tx.function_name = "__init__" /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    eval_stmts (deploy_evaluation_context tops am tx) body
      (es0 with <| gas_obs := gobs; outcomes := oc |>) = (res, st) ==>
    load_contract NONE gobs am tx [(NONE, tops)] [] =
      deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx) nr mut am_c res st
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `deploy_ctor_start tops am tx (mut,nr,bdy,am_c,es0)` >>
  `~supported_stmts_expr_exists constructor_call_root bdy` by
    (gvs[ctorDeployDefsTheory.deploy_source_ok_def,
       constructor_call_free_def, deploy_ctor_start_def,
       Excl "lock_if_nr_def", Excl "is_view_mut_def"] >> metis_tac[]) >>
  drule (cj 2 outcomes_replace_evaluate_call_free) >>
  disch_then (qspecl_then
    [`deploy_evaluation_context tops am tx`,
     `es0 with <|gas_obs := gobs; outcomes := oc|>`, `NONE`] mp_tac) >>
  simp[] >> strip_tac >>
  `load_contract NONE gobs am tx [(NONE,tops)] [] =
    deploy_ctor_finish tops tx (deploy_evaluation_context tops am tx)
      nr mut am_c res (st with outcomes := NONE)` by
    (irule deploy_ctor_source_run_none >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  gvs[deploy_ctor_finish_outcomes]
QED
