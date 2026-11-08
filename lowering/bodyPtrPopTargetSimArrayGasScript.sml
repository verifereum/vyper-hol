Theory bodyPtrPopTargetSimArrayGas
Ancestors
  bodyPtrPopTargetSimArraySource gasSummaryComposePtr bodyPtrPopTargetDefs
  vyperState vyperStorageBackend vyperAST vyperInterpreter list
  vyperStoragePlaceProvenance appendStorageSourcePtr fragGasPathPtr
  exprSimDefs venomState fragExec

Theorem target_memory_extend_gas_tail_ptr:
  !cx id path sub es gs.
    extend_place cx (PlaceR (MemoryPlace id path)) sub (es with gas_obs := gs) =
      (FST (extend_place cx (PlaceR (MemoryPlace id path)) sub es),
       es with gas_obs := gs) /\
    SND (extend_place cx (PlaceR (MemoryPlace id path)) sub es) = es
Proof
  rpt gen_tac >> Cases_on `lookup_scopes id es.scopes` >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       get_scopes_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, raise_def] >>
  rename1 `subscripts_type entry.type path` >>
  Cases_on `subscripts_type entry.type path` >> simp[return_def, raise_def] >>
  Cases_on `read_memory_path entry path` >> simp[return_def, raise_def] >>
  rename1 `evaluate_subscripts tv v [sub]` >>
  Cases_on `evaluate_subscripts tv v [sub]` >> simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[return_def, raise_def, get_storage_gas_obs]
QED

Theorem target_storage_array_extend_gas_tail_ptr:
  extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (ValueSubscript (IntV i)) es = (res,ee) ==>
  !gs. extend_place cx (PlaceR (StoragePlace tr slot (ArrayTV etv bd)))
    (ValueSubscript (IntV i)) (es with gas_obs := gs) =
    (res,ee with gas_obs := gs)
Proof
  Cases_on `bd` >>
  simp[extend_place_def, extend_storage_place_def, resolve_array_element_def,
       bind_def, ignore_bind_def, check_def, assert_def, get_storage_backend_eq,
       return_def, raise_def, resolve_array_element_empty, AllCaseEqs()] >>
  rpt strip_tac >> gvs[return_def, raise_def, get_storage_gas_obs]
QED

(* The continuation alternatives carry a checked path even on failure.
   Marks for an abort may be nonzero; none of those reads is explicit. *)
Theorem target_extension_outcome_ptr:
  (!res. source es = (res,es) ==>
    !tail. source (es with gas_obs := tail) = (res,es with gas_obs := tail)) /\
  ((?pv t H un. source es = (INL pv,es) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
      Q (INL pv) (es with gas_obs := []) H un t) \/
   (?msg t H un fuel pc. source es = (INR (Error (RuntimeError msg)),es) /\
      gas_path_ptr D 0 ctx fn PG G tn s fuel H un
        (Abort Revert_abort (t with vs_inst_idx := pc)))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn) Q
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac
  >- (simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_ptr_at_def] >>
      qexistsl_tac [`INL pv`, `es`, `H`, `un`, `OK t`] >> simp[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `REPLICATE fuel F` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INR (Error (RuntimeError msg))`, `es`, `H`, `un`,
    `Abort Revert_abort (t with vs_inst_idx := pc)`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]
QED

Theorem target_array_extend_gas_tail_ptr:
  ((?id path. pv = PlaceR (MemoryPlace id path)) \/
   (?tr slot etv bd i. pv = PlaceR (StoragePlace tr slot (ArrayTV etv bd)) /\
      sub = ValueSubscript (IntV i))) /\
  extend_place cx pv sub es = (res,es) ==>
  !tail. extend_place cx pv sub (es with gas_obs := tail) =
    (res,es with gas_obs := tail)
Proof
  strip_tac >> gvs[]
  >- (qspec_then `cx` mp_tac target_memory_extend_gas_tail_ptr >>
      disch_then (qspecl_then [`id`, `path`, `sub`, `es`] mp_tac) >> simp[]) >>
  metis_tac[target_storage_array_extend_gas_tail_ptr]
QED

Theorem target_array_suffix_outcome_ptr:
  ((?id path. pv = PlaceR (MemoryPlace id path)) \/
   (?tr slot etv bd i. pv = PlaceR (StoragePlace tr slot (ArrayTV etv bd)) /\
      sub = ValueSubscript (IntV i))) /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx + LENGTH (emitted_insts sn sb) = LENGTH sb.cs_current_insts /\
  ef.gas_obs = [] /\
  ((?pv' t H un.
      extend_place cx pv sub ef = (INL pv',ef) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
      target_post ctx fn cenv cx es sa sb s0 ef pv' vt rb t /\
      ghost_inv d cenv cx ef H un t /\ target_ptr_ok cenv pv' rb H un t /\
      ghost_kept cenv es sa G0 tn0 s0 H un /\
      t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sn sb)) \/
   (?msg t H un fuel pc.
      extend_place cx pv sub ef = (INR (Error (RuntimeError msg)),ef) /\
      gas_path_ptr D 0 ctx fn PG G tn s fuel H un
        (Abort Revert_abort (t with vs_inst_idx := pc)))) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (extend_place cx pv sub) (ef,s,G,tn)
    (\res ee H un t. ?pv'. res = INL pv' /\
      target_post ctx fn cenv cx es sa sb s0 ee pv' vt rb t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee H un t /\ target_ptr_ok cenv pv' rb H un t /\
      ghost_kept cenv es sa G0 tn0 s0 H un)
    (\res ee gt r. expr_exit res r)
Proof
  disch_tac >> irule target_extension_outcome_ptr >> conj_tac
  >- (rpt strip_tac >> irule target_array_extend_gas_tail_ptr >> metis_tac[]) >>
  fs[] >>
  `ef with gas_obs := [] = ef` by
    simp[evaluation_state_component_equality] >> simp[] >> metis_tac[]
QED
