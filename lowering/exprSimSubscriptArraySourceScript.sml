(* Source read boundaries for framed array subscript simulation. *)
Theory exprSimSubscriptArraySource
Ancestors
  exprSimSource exprSimHypsDefs vyperState vyperInterpreter vyperValue
  vyperPlaceResultTyping vyperPlaceStatePreservation vyperTypeEnvPreservation
  vyperTypeInvariants vyperTypeSystem
  integer option list rich_list finite_map

Theorem read_result_nonstorage_frame:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  s'.scopes = s.scopes /\ s'.immutables = s.immutables ==>
  FST (read_result cx r s') = FST (read_result cx r s)
Proof
  strip_tac >> Cases_on `r`
  >- simp[read_result_def, return_def]
  >- (Cases_on `p`
      >- metis_tac[]
      >- (rename1 `PlaceR (MemoryPlace id path)` >>
          simp[read_result_def, read_place_def, get_scopes_def, bind_def,
               lift_option_type_def, lift_sum_def, return_def, raise_def] >>
          Cases_on `lookup_scopes id s.scopes` >>
          simp[return_def, raise_def] >>
          rename1 `lookup_scopes id s.scopes = SOME entry` >>
          Cases_on `read_memory_path entry path` >> simp[return_def, raise_def])
      >> simp[read_result_def, read_place_def, get_immutables_def,
              get_address_immutables_def, bind_def, lift_option_type_def,
              lift_sum_def, return_def, raise_def] >>
      rpt (CASE_TAC >> simp[return_def, raise_def, bind_def]))
  >> simp[read_result_def, raise_def]
QED

(* A stale child snapshot refutes an unrestricted read/selection equation.
   This history is typed, but its child key is not indexed through a dynamic
   array, as expr_sim_inv requires. *)
Theorem fixed_array_snapshot_probe[local]:
  let tv = ArrayTV (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) (Dynamic 2);
      p = [ValueSubscript (IntV 0)];
      hist = [(p ++ [ValueSubscript (IntV 0)], IntV 9);
              (p, ArrayV (StaticArrayV [IntV 5; IntV 1]))]
  in read_popped tv p hist = SOME (ArrayV (StaticArrayV [IntV 5; IntV 1])) /\
     read_popped tv (p ++ [ValueSubscript (IntV 0)]) hist = SOME (IntV 9)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem eval_expr_subscript_bind:
  eval_expr cx (Subscript ann obj idx) =
  bind (eval_expr cx obj) (\r.
    bind (bind (eval_expr cx idx) (read_result cx)) (\v.
      select_result cx (expr_type obj) r (ValueSubscript v)))
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem lookup_scopes_popped_keys_indexed:
  popped_keys_indexed scs /\ lookup_scopes id scs = SOME entry ==>
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
             subscripts_type entry.type p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST entry.popped)
Proof
  strip_tac >> drule lookup_scopes_EL >> strip_tac >>
  gvs[popped_keys_indexed_def, EVERY_EL] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

Theorem indexed_history_no_fixed_child:
  EVERY (\k. ?p i etv n. k = p ++ [ValueSubscript i] /\
             subscripts_type tv p = SOME (ArrayTV etv (Dynamic n)))
    (MAP FST hist) /\
  subscripts_type tv path = SOME (ArrayTV et (Fixed bound)) ==>
  !i v. ~MEM (path ++ [ValueSubscript i],v) hist
Proof
  simp[EVERY_MEM, MEM_MAP] >> rpt strip_tac >>
  first_x_assum (qspec_then `path ++ [ValueSubscript i]` mp_tac) >>
  (impl_tac >- (qexists_tac `(path ++ [ValueSubscript i],v)` >> simp[])) >>
  strip_tac >> gvs[GSYM SNOC_APPEND, SNOC_11]
QED

Theorem evaluate_subscripts_append_error:
  !path tv ptv a err suffix.
    subscripts_type tv path = SOME ptv /\
    evaluate_subscripts tv a path = INR err ==>
    evaluate_subscripts tv a (path ++ suffix) = INR err
Proof
  Induct >- simp[evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[subscripts_type_def, AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (fn th =>
    qspec_then `path` assume_tac th >>
    qspec_then `path ++ suffix` assume_tac th) >>
  Cases_on `evaluate_subscripts tv a [h]` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem prefix_snoc_not_equal[local]:
  !path pre sb.
    IS_PREFIX (path ++ [sb]) pre /\ pre <> path ++ [sb] ==>
    IS_PREFIX path pre
Proof
  Induct >> Cases_on `pre` >> simp[IS_PREFIX] >> rpt strip_tac >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED

Theorem snapshot_snoc_evaluate[local]:
  subscripts_type tv path = SOME ptv /\ IS_PREFIX path pre /\
  subscripts_type tv pre = SOME htv ==>
  evaluate_subscripts htv saved (DROP (LENGTH pre) (path ++ [sb])) =
    case evaluate_subscripts htv saved (DROP (LENGTH pre) path) of
    | INL v => evaluate_subscripts ptv v [sb]
    | INR err => INR err
Proof
  simp[IS_PREFIX_APPEND] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  gvs[vyperPlaceStatePreservationTheory.subscripts_type_append] >>
  Cases_on `evaluate_subscripts htv saved l`
  >- (drule_all evaluate_subscripts_append >> simp[]) >>
  drule_all evaluate_subscripts_append_error >> simp[]
QED

Theorem read_popped_snoc:
  !hist tv path ptv v sb w.
    subscripts_type tv path = SOME ptv /\
    read_popped tv path hist = SOME v /\
    evaluate_subscripts ptv v [sb] = INL w /\
    (!saved. ~MEM (path ++ [sb],saved) hist) ==>
    read_popped tv (path ++ [sb]) hist = SOME w
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  `h0 <> path ++ [sb]` by metis_tac[MEM] >>
  `!saved. ~MEM (path ++ [sb],saved) hist` by metis_tac[MEM] >>
  Cases_on `IS_PREFIX path h0`
  >- (Cases_on `subscripts_type tv h0`
      >- (gvs[read_popped_def] >> first_x_assum drule_all >> simp[]) >>
      rename1 `subscripts_type tv h0 = SOME htv` >>
      drule_all_then assume_tac snapshot_snoc_evaluate >>
      Cases_on `evaluate_subscripts htv h1 (DROP (LENGTH h0) path)` >>
      gvs[read_popped_def] >>
      `IS_PREFIX (path ++ [sb]) h0` by
        (gvs[IS_PREFIX_APPEND] >> metis_tac[APPEND_ASSOC]) >>
      simp[Once read_popped_def] >>
      first_x_assum drule_all >> simp[]) >>
  `~IS_PREFIX (path ++ [sb]) h0` by metis_tac[prefix_snoc_not_equal] >>
  gvs[read_popped_def] >> first_x_assum drule_all >> simp[]
QED

Theorem read_memory_path_snoc:
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w /\
  (!saved. ~MEM (path ++ [sb],saved) entry.popped) ==>
  read_memory_path entry (path ++ [sb]) = INL w
Proof
  strip_tac >> Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >>
      drule_all evaluate_subscripts_append >>
      disch_then (qspec_then `[sb]` assume_tac) >> simp[read_memory_path_def]) >>
  gvs[read_memory_path_def, AllCaseEqs()] >>
  drule_all read_popped_snoc >> strip_tac >>
  drule_all evaluate_subscripts_append_error >>
  disch_then (qspec_then `[sb]` assume_tac) >> simp[read_memory_path_def]
QED

Theorem select_memory_result:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb]))
      (\_. return (PlaceR (MemoryPlace id (path ++ [sb])))) es
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_sum_def, return_def, extend_memory_place_def] >>
  Cases_on `evaluate_subscripts ptv v [sb]` >> simp[return_def, raise_def]
QED

Theorem read_memory_child_result:
  lookup_scopes id es.scopes = SOME entry /\
  subscripts_type entry.type path = SOME ptv /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w /\
  (!saved. ~MEM (path ++ [sb],saved) entry.popped) ==>
  read_result cx (PlaceR (MemoryPlace id (path ++ [sb]))) es = (INL w,es)
Proof
  strip_tac >> drule_all read_memory_path_snoc >> strip_tac >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def]
QED

Theorem select_value_result:
  evaluate_type (get_tenv cx) ty = SOME ptv ==>
  select_result cx ty (Value v) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb])) (\w. return (Value w)) es
Proof
  simp[select_result_def, bind_def, lift_option_type_def, return_def]
QED

Theorem select_immutable_result:
  get_immutables cx src es = (INL imms,es) /\
  FLOOKUP imms id = SOME (itv,iv) /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL v ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb es =
    bind (lift_sum (evaluate_subscripts ptv v [sb]))
      (\_. return (PlaceR (ImmutablePlace src id (path ++ [sb])))) es
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       lift_sum_def, return_def, extend_memory_place_def] >>
  Cases_on `evaluate_subscripts ptv v [sb]` >> simp[return_def, raise_def]
QED

Theorem read_immutable_child_result:
  get_immutables cx src es = (INL imms,es) /\
  FLOOKUP imms id = SOME (itv,iv) /\
  subscripts_type itv path = SOME ptv /\
  evaluate_subscripts itv iv path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [sb]))) es = (INL w,es)
Proof
  strip_tac >> drule_all evaluate_subscripts_append >>
  disch_then (qspec_then `[sb]` assume_tac) >>
  simp[read_result_def, read_place_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def]
QED

Theorem select_fixed_memory_read:
  runtime_place_typed cx es (MemoryPlace id path) (ArrayTV et (Fixed n)) /\
  popped_keys_indexed es.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) es = (INL v,es) /\
  evaluate_subscripts (ArrayTV et (Fixed n)) v [ValueSubscript i] = INL w ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) (ValueSubscript i) es =
    (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript i]))),es) /\
  read_result cx (PlaceR (MemoryPlace id (path ++ [ValueSubscript i]))) es = (INL w,es)
Proof
  strip_tac >> Cases_on `lookup_scopes id es.scopes` >>
  gvs[runtime_place_typed_def, place_type_value_def, read_result_def,
      read_place_def, get_scopes_def, bind_def, lift_option_type_def,
      lift_sum_def, return_def, raise_def] >>
  rename1 `lookup_scopes id es.scopes = SOME entry` >>
  Cases_on `subscripts_type entry.type path` >> gvs[return_def, raise_def] >>
  Cases_on `read_memory_path entry path` >> gvs[return_def, raise_def] >>
  drule_all lookup_scopes_popped_keys_indexed >> strip_tac >>
  drule_all indexed_history_no_fixed_child >> strip_tac >>
  conj_tac
  >- (drule_all_then assume_tac select_memory_result >>
      simp[bind_def, lift_sum_def, return_def]) >>
  `read_memory_path entry (path ++ [ValueSubscript i]) = INL w` by
    (irule read_memory_path_snoc >> conj_tac >- simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[return_def]
QED
