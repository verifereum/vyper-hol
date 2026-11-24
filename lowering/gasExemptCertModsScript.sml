(* Exempt errors retain a concrete origin through actual source sequencing
   and completed target prefixes, including prefixes inside INVOKE. *)
Theory gasExemptCertMods
Ancestors
  gasExemptOriginMods sourceExemptMods gasNormalPrefix gasSummary gasSummaryCompose fragGasFocus fragGasMode fragGasPathMem
  vyperState vyperInterpreter vyperValue venomState list arithmetic

Inductive gas_exempt_cert_mods:
[~origin:]
  (!memory mods ctx func source es s0 marks err ee t.
     gas_exempt_origin_mods memory mods (ctx, func) source (es, s0)
       marks (err, ee) t ==>
     gas_exempt_cert_mods memory mods (ctx, func) source (es, s0)
       marks (err, ee) (func, t))

[~bind_unit:]
  (!memory mods ctx func (a : evaluation_state -> (unit) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_unit:]
  (!memory mods ctx func (a : evaluation_state -> (unit) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_bool:]
  (!memory mods ctx func (a : evaluation_state -> (bool) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_bool:]
  (!memory mods ctx func (a : evaluation_state -> (bool) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_result:]
  (!memory mods ctx func (a : evaluation_state -> (eval_result) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_result:]
  (!memory mods ctx func (a : evaluation_state -> (eval_result) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_value:]
  (!memory mods ctx func (a : evaluation_state -> (value) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_value:]
  (!memory mods ctx func (a : evaluation_state -> (value) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_place:]
  (!memory mods ctx func (a : evaluation_state -> (place) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_place:]
  (!memory mods ctx func (a : evaluation_state -> (place) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_values:]
  (!memory mods ctx func (a : evaluation_state -> (value list) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_values:]
  (!memory mods ctx func (a : evaluation_state -> (value list) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~bind_results:]
  (!memory mods ctx func (a : evaluation_state -> (eval_result list) evaluation_result)
      k es s0 left v mid t right err ee leaf finish.
     gas_marked_exec memory (ctx, func) a (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert_mods memory mods (ctx, func) (k v)
       (mid with gas_obs := [], t) right (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       (left ++ right) (err, ee) (leaf, finish))

[~error_results:]
  (!memory mods ctx func (a : evaluation_state -> (eval_result list) evaluation_result)
      k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind a (return ())) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind a k) (es, s0)
       marks (err, ee) (leaf, finish))

[~cleanup:]
  (!memory mods ctx func source cleanup es s0 marks err mid ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func) source (es, s0)
       marks (err, mid) (leaf, finish) /\
     (!tail. cleanup ((mid with gas_obs := []) with gas_obs := tail) =
       (INL (), ee with gas_obs := tail)) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (finally source cleanup)
       (es, s0) marks (err, ee) (leaf, finish))

[~handler:]
  (!memory mods ctx func source handler es s0 marks err mid ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func) source (es, s0)
       marks (err, mid) (leaf, finish) /\
     (!tail. handler (Error err)
       ((mid with gas_obs := []) with gas_obs := tail) =
       (INR (Error err), ee with gas_obs := tail)) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (try source handler)
       (es, s0) marks (err, ee) (leaf, finish))

[~get_scopes:]
  (!memory mods ctx func k es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func) (k es.scopes) (es, s0)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) (bind get_scopes k) (es, s0)
       marks (err, ee) (leaf, finish))

[~invoke:]
  (!memory mods ctx func s callee entered source es marks err ee leaf finish.
     gas_invoke_entry (ctx, func) s callee entered /\
     gas_exempt_cert_mods memory mods (ctx, callee) source (es, entered)
       marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func) source (es, s)
       marks (err, ee) (leaf, finish))

[~unforce_result:]
  (!memory mods ctx func cx e es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
       (es, s0) marks (err, ee) (leaf, finish) ==>
     gas_exempt_cert_mods memory mods (ctx, func)
       (ignore_bind (eval_expr cx e) (return ()))
       (es, s0) marks (err, ee) (leaf, finish))

[~source_cong:]
  (!memory mods ctx func source source' es s0 marks err ee leaf finish.
     gas_exempt_cert_mods memory mods (ctx, func) source (es, s0)
       marks (err, ee) (leaf, finish) /\
     (!gs. source' (es with gas_obs := gs) = source (es with gas_obs := gs)) ==>
     gas_exempt_cert_mods memory mods (ctx, func) source' (es, s0)
       marks (err, ee) (leaf, finish))
End

Theorem gas_exempt_cert_forget_memory_mods:
  !checked mods p source start marks out endpoint.
    gas_exempt_cert_mods checked mods p source start marks out endpoint ==>
    !memory. (memory ==> checked) ==>
      gas_exempt_cert_mods memory mods p source start marks out endpoint
Proof
  ho_match_mp_tac gas_exempt_cert_mods_ind >> rpt conj_tac >|
  [(rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_origin, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_unit, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_unit, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_bool, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_bool, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_result, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_result, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_value, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_value, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_place, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_place, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_values, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_values, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_bind_results, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_error_results, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    irule gas_exempt_cert_mods_cleanup >> qexists_tac `mid` >> simp[]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    irule gas_exempt_cert_mods_handler >> qexists_tac `mid` >> simp[]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_get_scopes, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_invoke, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> rpt strip_tac >>
    Cases_on `memory` >> Cases_on `checked` >> gvs[] >>
    metis_tac[gas_exempt_cert_mods_unforce_result, gas_exempt_origin_from_mem_mods,
              gas_marked_exec_from_mem]),
   (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
    irule gas_exempt_cert_mods_source_cong >> qexists_tac `source` >> simp[])]
QED


(* The endpoint of the concrete child remains separate from the source
   endpoint after enclosing cleanup. Entering a call is not completing it. *)
Theorem read_place_no_exempt_error_mods[local]:
  !mods cx p st err st'.
    read_place cx p st = (INR (Error err), st') ==>
    ~unspecified_behaviour_exempt_mods mods err
Proof
  rpt gen_tac >> Cases_on `p`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tr` >>
      simp[read_place_def, read_storage_slot_def, get_storage_backend_def,
           get_accounts_def, get_transient_storage_def, bind_def, return_def,
           lift_option_def, vyperMiscTheory.option_CASE_rator, raise_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[unspecified_behaviour_exempt_mods_def])
  >- (simp[read_place_def, get_scopes_def, bind_def, return_def,
           lift_option_type_def, lift_sum_def, vyperMiscTheory.option_CASE_rator,
           vyperMiscTheory.sum_CASE_rator, raise_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[unspecified_behaviour_exempt_mods_def] >>
      drule read_memory_path_error_shape >>
      strip_tac >> gvs[unspecified_behaviour_exempt_mods_def])
  >> simp[read_place_def, get_immutables_def, get_address_immutables_def,
          bind_def, return_def, lift_option_type_def, lift_sum_def,
          vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
          raise_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[unspecified_behaviour_exempt_mods_def] >>
     drule evaluate_subscripts_error_shape >>
     strip_tac >> gvs[unspecified_behaviour_exempt_mods_def]
QED

Theorem read_result_no_exempt_error_mods:
  !mods cx r st err st'.
    read_result cx r st = (INR (Error err), st') ==>
    ~unspecified_behaviour_exempt_mods mods err
Proof
  rpt gen_tac >> Cases_on `r` >>
  simp[read_result_def, return_def, raise_def] >>
  rpt strip_tac
  >- (drule read_place_no_exempt_error_mods >> metis_tac[])
  >> gvs[unspecified_behaviour_exempt_mods_def]
QED

Theorem gas_source_unforce_result_mods:
  !mods cx e st err ee.
    unspecified_behaviour_exempt_mods mods err /\
    ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()) st =
      (INR (Error err), ee) ==>
    ignore_bind (eval_expr cx e) (return ()) st =
      (INR (Error err), ee)
Proof
  rpt gen_tac >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >>
  simp[ignore_bind_def, bind_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule read_result_no_exempt_error_mods >> metis_tac[]
QED

Theorem gas_exempt_cert_execution_mods:
  !memory mods ctx func source es s0 marks err ee leaf finish.
    gas_exempt_cert_mods memory mods (ctx, func) source (es, s0)
      marks (err, ee) (leaf, finish) ==>
    (!tail. source
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INR (Error err), ee with gas_obs := tail)) /\
    gas_focus_path memory (ctx, func) s0 (LENGTH marks) (leaf, finish) /\
    unspecified_behaviour_exempt_mods mods err
Proof
  let
    val normal = rpt gen_tac >> simp[] >> strip_tac >>
      conj_tac
      >- (irule gas_marked_source_bind_normal >>
          qexistsl_tac [`ctx`, `func`, `memory`, `mid`, `t`, `v`] >>
          simp[evaluation_state_component_equality]) >>
      simp[LENGTH_APPEND] >>
      metis_tac[gas_marked_exec_def, gas_focus_path_rules]
    val error = rpt gen_tac >> simp[] >> strip_tac >>
      irule gas_source_ignore_return_exception_bind >> simp[]
  in
  qsuff_tac
    `!memory mods p source start marks out endpoint.
       gas_exempt_cert_mods memory mods p source start marks out endpoint ==>
       (!tail. source ((FST start) with gas_obs :=
          gas_explicit marks (SND start).vs_gas_readings ++ tail) =
          (INR (Error (FST out)), (SND out) with gas_obs := tail)) /\
       gas_focus_path memory p (SND start) (LENGTH marks) endpoint /\
       unspecified_behaviour_exempt_mods mods (FST out)`
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  ho_match_mp_tac gas_exempt_cert_mods_ind >> rpt conj_tac
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      drule gas_exempt_origin_execution_mods >>
      drule gas_exempt_origin_classified_mods >>
      simp[gas_marked_exec_def] >> metis_tac[gas_focus_path_rules])
  >- normal
  >- error
  >- normal
  >- error
  >- normal
  >- error
  >- normal
  >- error
  >- normal
  >- error
  >- normal
  >- error
  >- normal
  >- error
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      irule gas_source_finally_exception >> qexists_tac `mid` >>
      simp[evaluation_state_component_equality])
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      irule gas_source_try_exception >> qexists_tac `mid` >>
      simp[evaluation_state_component_equality])
  >- (rpt gen_tac >> simp[get_scopes_def, bind_def, return_def])
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      drule gas_invoke_entry_readings >> strip_tac >>
      conj_tac >- gvs[] >> metis_tac[gas_focus_path_rules])
  >- (rpt gen_tac >> simp[] >> strip_tac >>
      gen_tac >> irule gas_source_unforce_result_mods >> metis_tac[]) >>
  rpt gen_tac >> simp[] >> strip_tac >> simp[]
  end
QED

Theorem gas_exempt_cert_function_cleanup_mods:
  !memory mods ctx func a es s0 marks err ee leaf finish saved k.
  gas_exempt_cert_mods memory mods (ctx,func)
    (ignore_bind (a : evaluation_state -> unit evaluation_result) (return ()))
    (es,s0) marks (err,ee) (leaf,finish) ==>
  gas_exempt_cert_mods memory mods (ctx,func)
    (bind (finally (try (ignore_bind a (return NoneV)) handle_function)
       (set_scopes saved)) k)
    (es,s0) marks (err,ee with scopes := saved) (leaf,finish)
Proof
  rpt strip_tac >> irule gas_exempt_cert_mods_error_value >>
  rewrite_tac[ignore_bind_finally_unit, ignore_bind_try_unit,
    ignore_bind_return_twice] >>
  irule gas_exempt_cert_mods_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[set_scopes_def, vyperStateTheory.return_def] >>
  irule gas_exempt_cert_mods_handler >> qexists_tac `ee` >>
  simp[handle_function_def, ignore_bind_def, bind_def, raise_def]
QED

Theorem gas_exempt_cert_start_gas_obs_mods:
  !memory mods env source start marks out endpoint.
    gas_exempt_cert_mods memory mods env source start marks out endpoint ==>
    !gs. gas_exempt_cert_mods memory mods env source
      (FST start with gas_obs := gs, SND start) marks out endpoint
Proof
  ho_match_mp_tac gas_exempt_cert_mods_ind >> rpt strip_tac >> simp[]
  >- (irule gas_exempt_cert_mods_origin >>
      fs[gas_exempt_origin_mods_def] >>
      drule gas_value_prefix_start_gas_obs >>
      disch_then (qspec_then `gs` assume_tac) >> metis_tac[]) >>
  fs[]
  >- metis_tac[gas_exempt_cert_mods_bind_unit, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_unit]
  >- metis_tac[gas_exempt_cert_mods_bind_bool, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_bool]
  >- metis_tac[gas_exempt_cert_mods_bind_result, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_result]
  >- metis_tac[gas_exempt_cert_mods_bind_value, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_value]
  >- metis_tac[gas_exempt_cert_mods_bind_place, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_place]
  >- metis_tac[gas_exempt_cert_mods_bind_values, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_values]
  >- metis_tac[gas_exempt_cert_mods_bind_results, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_mods_error_results]
  >- (irule gas_exempt_cert_mods_cleanup >> qexists `mid` >> simp[])
  >- (irule gas_exempt_cert_mods_handler >> qexists `mid` >> simp[])
  >- (irule gas_exempt_cert_mods_get_scopes >> simp[])
  >- metis_tac[gas_exempt_cert_mods_invoke]
  >- metis_tac[gas_exempt_cert_mods_unforce_result] >>
  irule gas_exempt_cert_mods_source_cong >> qexists_tac `source` >> simp[]
QED
