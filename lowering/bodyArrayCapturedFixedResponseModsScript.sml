(* Gas-observation response for a captured fixed MemoryPlace array. *)
Theory bodyArrayCapturedFixedResponseMods
Ancestors
  bodyFullSubscriptCapturedPlace exprSimMemorySource
  exprSimSubscriptArraySource exprSimSubscriptArraySuffix
  valueTypingMemoryProps vyperAssignPreservesType
  vyperTypeValues vyperArray vyperValueOperation vyperInterpreter vyperState
  loweringPosts

Theorem array_captured_fixed_response_mods:
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
  popped_keys_indexed fin.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) fin =
    (INL (ArrayV (SArrayV kvs)),fin) /\
  value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  n < dimword (:256) /\
  i = (if sgn then w2i iw else &(w2n iw)) ==>
  let r = PlaceR (MemoryPlace id path) in
  let r' = PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])) in
    (~idx_in_range sgn iw (n2w n) ==>
       select_result cx (ArrayT et (Fixed n)) r
         (ValueSubscript (IntV i)) fin =
         (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin) /\
       (!tail. select_result cx (ArrayT et (Fixed n)) r
          (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
          (INR (Error (RuntimeError "evaluate_subscripts array_index")),
           fin with gas_obs := tail))) /\
    (idx_in_range sgn iw (n2w n) ==>
       ?v. 0 <= i /\ Num i < n /\ iw = n2w (Num i) /\
           array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v /\
           value_has_type etv v /\ val_wf etv v /\
           read_result cx r' fin = (INL v,fin) /\
           select_result cx (ArrayT et (Fixed n)) r
             (ValueSubscript (IntV i)) fin = (INL r',fin) /\
           (!tail. read_result cx r' (fin with gas_obs := tail) =
               (INL v,fin with gas_obs := tail)) /\
           (!tail. select_result cx (ArrayT et (Fixed n)) r
             (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
             (INL r',fin with gas_obs := tail)))
Proof
  strip_tac >> simp[LET_THM] >> unabbrev_all_tac >>
  `well_formed_type_value etv` by
    (irule evaluate_type_well_formed_type_value >>
     qexistsl_tac [`get_tenv cx`,`et`] >> simp[]) >>
  `idx_in_range sgn iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >>
     disch_then (qspecl_then [`iw`,`sgn`] mp_tac) >> simp[] >> metis_tac[]) >>
  `0 <= i /\ i < &n <=> 0 <= i /\ Num i < n` by
    (`0 <= (&n:int)` by simp[] >>
     `Num (&n:int) = n` by simp[] >>
     metis_tac[integerTheory.NUM_LT]) >>
  `idx_in_range sgn iw (n2w n) <=> 0 <= i /\ Num i < n` by metis_tac[] >>
  conj_tac
  >- (strip_tac >>
      `~valid_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` by
        (simp[vyperArrayTheory.valid_index_def] >> metis_tac[]) >>
      `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
         [ValueSubscript (IntV i)] =
         INR (RuntimeError "evaluate_subscripts array_index")` by
        (irule evaluate_array_subscript_oob >> simp[]) >>
      `!tr slot vt. MemoryPlace id path <> StoragePlace tr slot vt` by simp[] >>
      `select_result cx (ArrayT et (Fixed n))
         (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV (if sgn then w2i iw else &(w2n iw)))) fin =
         (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
        metis_tac[select_nonstorage_place_error] >>
      conj_tac
      >- simp[] >>
      gen_tac >>
      `select_result cx (ArrayT et (Fixed n))
         (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV (if sgn then w2i iw else &(w2n iw))))
         (fin with gas_obs := tail) =
       (FST (select_result cx (ArrayT et (Fixed n))
         (PlaceR (MemoryPlace id path))
         (ValueSubscript (IntV (if sgn then w2i iw else &(w2n iw)))) fin),
        fin with gas_obs := tail)` by
        (irule select_result_nonstorage_gas_obs >> simp[]) >>
      simp[]) >>
  strip_tac >>
  `0 <= i /\ Num i < n` by metis_tac[] >>
  `iw = n2w (Num i)` by
    (Cases_on `sgn` >> gvs[] >>
     qpat_x_assum `0 <= i` mp_tac >>
     qpat_x_assum `i = _` mp_tac >>
     simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >> intLib.COOPER_TAC) >>
  `valid_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` by
    (simp[vyperArrayTheory.valid_index_def,
          vyperValueOperationTheory.array_length_def,
          IgnAsm `i = if _ then _ else _`] >>
     metis_tac[]) >>
  `?v. array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v` by
    (irule (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >> simp[]) >>
  `value_has_type etv v` by metis_tac[array_index_has_type] >>
  `val_wf etv v` by metis_tac[value_has_type_memory_wf] >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_array_subscript_result, IgnAsm `i = if _ then _ else _`] >>
  drule_all select_fixed_memory_read >>
  disch_then (qspec_then `ArrayT et (Fixed n)` strip_assume_tac) >>
  qexists `v` >>
  qpat_x_assum `i = if _ then _ else _` (SUBST1_TAC o SYM) >>
  simp[] >> conj_tac
  >- (irule read_result_gas_obs >> simp[]) >>
  gen_tac >>
  `select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) (fin with gas_obs := tail) =
    (FST (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) fin),fin with gas_obs := tail)` by
    (irule select_result_nonstorage_gas_obs >> simp[]) >>
  simp[]
QED
