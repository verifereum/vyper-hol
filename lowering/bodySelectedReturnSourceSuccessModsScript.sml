(* Source continuation of the same successful qualified internal call. *)
Theory bodySelectedReturnSourceSuccessMods
Ancestors
  vyperInterpreter vyperState vyperAST vyperTyping
  vyperStorageTrace vyperStorageFootprint
  externalCallSelected[qualified] gasContext exprSimDefs loweringHalt
Libs
  monadsyntax

val callee_src = ``do lock_if_nr cx nr (is_view_mut mut);
  try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
           return NoneV
       od) handle_function
  od``;

val rest = ``do lock_if_nr cx nr (is_view_mut mut);
  rv <- finally_unless_halt
    (finally
       (try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                return NoneV
             od) handle_function)
       (pop_function prev))
    (unlock_if_nr cx nr (is_view_mut mut));
  crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
  return (Value crv)
  od``;

Theorem selected_return_source_result[local]:
  (^callee_src) u = (INL v,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) ==>
  (^rest) u =
    case safe_cast rtv v of
      NONE => (INR (Error (TypeError "IntCall cast ret")),out with scopes := prev)
    | SOME cv => (INL (Value cv),out with scopes := prev)
Proof
  strip_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) u` >> Cases_on `q` >>
  gvs[ignore_bind_def, bind_def,
      Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  drule externalCallSelectedTheory.unlock_if_nr_with_scopes >>
  disch_then (qspec_then `prev` assume_tac) >>
  Cases_on `safe_cast rtv v` >>
  simp[finally_def, finally_unless_halt_def, pop_function_def, set_scopes_def,
       ignore_bind_def, bind_def, lift_option_type_def, lift_option_def,
       return_def, raise_def, Excl "unlock_if_nr_def", Excl "is_view_mut_def"]
QED

Theorem selected_return_source_success_mods:
  (!tail. (^callee_src) (es1 with gas_obs := prefix ++ tail) =
          (INL v,ee with gas_obs := tail)) /\
  unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := []) = (INL (),out) /\
  gas_admissible (^rest) expr_vv_res_ok es1 ==>
  safe_cast rtv v = SOME v /\
  (!tail. (^rest) (es1 with gas_obs := prefix ++ tail) =
          (INL (Value v),(out with scopes := prev) with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H out.storage_trace ==>
       valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace)
Proof
  strip_tac >>
  `!tail. unlock_if_nr cx nr (is_view_mut mut) (ee with gas_obs := tail) =
           (INL (),out with gas_obs := tail)` by
    (drule externalCallSelectedTheory.unlock_if_nr_with_gas_obs >> simp[]) >>
  `!tail. (^rest) (es1 with gas_obs := prefix ++ tail) =
      case safe_cast rtv v of
        NONE => (INR (Error (TypeError "IntCall cast ret")),
                 (out with scopes := prev) with gas_obs := tail)
      | SOME cv => (INL (Value cv),(out with scopes := prev) with gas_obs := tail)` by
    (gen_tac >>
     qpat_assum `!tail. (^callee_src) _ = _` (qspec_then `tail` assume_tac) >>
     qpat_assum `!tail. unlock_if_nr _ _ _ _ = _` (qspec_then `tail` assume_tac) >>
     drule_all selected_return_source_result >>
     simp[vyperStateTheory.evaluation_state_fupdcanon]) >>
  `safe_cast rtv v = SOME v` by
    (Cases_on `safe_cast rtv v`
     >- (qpat_assum `!tail. (^rest) _ = _` (qspec_then `[]` assume_tac) >>
         gvs[] >> drule_all gas_admissible_result >> simp[expr_vv_res_ok_def]) >>
     metis_tac[loweringHaltTheory.safe_cast_some_eq]) >>
  simp[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      `storage_trace_frame (unlock_if_nr cx nr (is_view_mut mut))` by
        simp[storage_trace_frame_optional_locks] >>
      drule valid_horizon_frame >>
      disch_then drule >> simp[]) >>
  gen_tac >> strip_tac >>
  `storage_trace_frame (^callee_src)` by
    (irule storage_trace_frame_ignore_bind >>
     simp[storage_trace_frame_optional_locks] >>
     irule storage_trace_frame_try >>
     simp[storage_trace_frame_function_handler] >>
     irule storage_trace_frame_ignore_bind >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_return]) >>
  qpat_assum `!tail. (^callee_src) _ = _` (qspec_then `[]` assume_tac) >>
  drule valid_horizon_frame >> disch_then drule >> simp[]
QED
