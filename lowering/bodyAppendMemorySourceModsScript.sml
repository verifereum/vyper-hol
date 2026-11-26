(* Source alternatives at the reached memory Append continuation. *)
Theory bodyAppendMemorySourceMods
Ancestors
  vyperState vyperValueOperation vyperValue vyperTyping vyperLookup
  stmtSimAugAssignPlaceMemory gasContext stmtSimDefs list finite_map

Theorem append_memory_read_step[local]:
  lookup_scopes id mid.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type tv v ==>
  !tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
    if LENGTH vs < cap then
      write_place cx (MemoryPlace id path) (ArrayV (DynArrayV (vs ++ [v])))
        (mid with gas_obs := tail)
    else (INR (Error (RuntimeError "append overflow")),mid with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  `compatible_bound (Dynamic cap) (SUC (LENGTH vs)) <=> LENGTH vs < cap` by
    (simp[compatible_bound_def] >> decide_tac) >>
  simp[append_place_def, place_type_value_def, read_place_def,
       append_element_def, safe_cast_well_typed, SNOC_APPEND,
       get_scopes_def, lift_option_type_def, lift_option_def, bind_def,
       return_def, raise_def, lift_sum_def] >>
  IF_CASES_TAC >> simp[bind_def, return_def, raise_def, lift_sum_def]
QED

Theorem append_memory_replace_error[local]:
  replace_memory_entry entry path arr = INR err ==> ?msg. err = TypeError msg
Proof
  Cases_on `evaluate_subscripts entry.type entry.value path` >>
  simp[replace_memory_entry_def] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace arr)` >>
  simp[] >> metis_tac[aug_place_replace_read_error]
QED

Theorem append_memory_write_step[local]:
  find_containing_scope id mid.scopes = SOME (pre,sc,entry,rest) ==>
  !cx arr path tail. write_place cx (MemoryPlace id path) arr (mid with gas_obs := tail) =
    if entry.assignable then
      case replace_memory_entry entry path arr of
      | INL new => (INL (),mid with <|scopes := pre ++ (sc |+ (id,new))::rest;
                                      gas_obs := tail|>)
      | INR err => (INR (Error err),mid with gas_obs := tail)
    else (INR (Error (TypeError "write_place not assignable")),mid with gas_obs := tail)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `entry.assignable` >>
  Cases_on `replace_memory_entry entry path arr` >>
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, lift_option_def, type_check_def, assert_def,
       lift_sum_def, return_def, raise_def, set_scopes_def]
QED

Theorem append_memory_source_cases_mods:
  lookup_scopes id mid.scopes = SOME entry /\
  subscripts_type entry.type path = SOME (ArrayTV tv (Dynamic cap)) /\
  read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
  value_has_type entry.type entry.value /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  value_has_type tv v /\
  gas_admissible (append_place cx (MemoryPlace id path) v) (stmt_res_ok lctx) mid ==>
  if LENGTH vs < cap then
    let arr = ArrayV (DynArrayV (vs ++ [v])) in
    ?ff. value_has_type (ArrayTV tv (Dynamic cap)) arr /\
         write_place cx (MemoryPlace id path) arr mid = (INL (),ff) /\
         ff.storage_trace = mid.storage_trace /\
         (!tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
            (INL (),ff with gas_obs := tail))
  else !tail. append_place cx (MemoryPlace id path) v (mid with gas_obs := tail) =
         (INR (Error (RuntimeError "append overflow")),mid with gas_obs := tail)
Proof
  strip_tac >> drule_all_then assume_tac append_memory_read_step >>
  Cases_on `LENGTH vs < cap` >> simp[] >>
  qabbrev_tac `arr = ArrayV (DynArrayV (vs ++ [v]))` >>
  `value_has_type (ArrayTV tv (Dynamic cap)) arr` by
    fs[Abbr `arr`, value_has_type_def, all_have_type_EVERY, EVERY_APPEND] >>
  drule_then strip_assume_tac lookup_scopes_find_containing_scope >>
  rename1 `find_containing_scope _ _ = SOME (pre,sc,entry,rest)` >>
  drule_then (qspecl_then [`cx`,`arr`,`path`] assume_tac) append_memory_write_step >>
  `!msg. write_place cx (MemoryPlace id path) arr (mid with gas_obs := []) <>
    (INR (Error (TypeError msg)),mid with gas_obs := [])` by
    (rpt strip_tac >>
     `append_place cx (MemoryPlace id path) v (mid with gas_obs := []) =
       (INR (Error (TypeError msg)),mid with gas_obs := [])` by fs[] >>
     drule_all gas_admissible_result >> simp[stmt_res_ok_def]) >>
  reverse (Cases_on `entry.assignable` >> fs[])
  >- (qpat_x_assum `!msg. write_place _ _ _ _ <> _`
        (qspec_then `"write_place not assignable"` mp_tac) >> simp[]) >>
  Cases_on `replace_memory_entry entry path arr` >> fs[]
  >- (rename1 `replace_memory_entry _ _ _ = INL new` >>
      qexists_tac `mid with scopes := pre ++ (sc |+ (id,new))::rest` >>
      `mid with gas_obs := mid.gas_obs = mid` by simp[evaluation_state_component_equality] >>
      conj_tac
      >- (qpat_x_assum `!tail. write_place _ _ _ _ = _` (qspec_then `mid.gas_obs` mp_tac) >>
          simp[evaluation_state_component_equality]) >>
      simp[]) >>
  drule_then (qx_choose_then `msg` SUBST_ALL_TAC) append_memory_replace_error >>
  qpat_x_assum `!msg. write_place _ _ _ _ <> _` (qspec_then `msg` mp_tac) >> simp[]
QED
