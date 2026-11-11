(* Canonical indexed storage reads for nonliteral word-array membership. *)
Theory exprSimBopRestWordStorage
Ancestors
  exprSimBopRestWordIndex exprSimUnwrap accountsRelProps vyperLookupStorage
  vyperStorage vyperValueOperation vyperValue vyperTyping loweringPosts
  vyperStorageWritePreservation vyperStorageBackend vyperState vyperInterpreter
  list alist arithmetic

Theorem rest_word_storage_extent:
  storage_holds cx tr ty r w es s /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  w2n w + type_slot_size tv <= dimword (:256)
Proof
  strip_tac >> gvs[storage_holds_def, storage_range_agree_def, AllCaseEqs()]
QED

Theorem rest_word_decode_array_elements:
  !n storage offset tv vs.
    (decode_static_array storage offset tv n = SOME vs ==>
       LENGTH vs = n /\
       !i. i < n ==> decode_value storage (offset + i * type_slot_size tv) tv = SOME (EL i vs)) /\
    (decode_dyn_array storage offset tv n = SOME vs ==>
       LENGTH vs = n /\
       !i. i < n ==> decode_value storage (offset + i * type_slot_size tv) tv = SOME (EL i vs))
Proof
  Induct_on `n` >- simp[decode_value_def] >>
  qpat_x_assum `!storage offset tv vs. _`
    (fn th => assume_tac (cj 1 th) >> assume_tac (cj 2 th)) >>
  rpt gen_tac >> conj_tac >>
  simp[decode_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  Cases_on `i` >> simp[] >>
  simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  first_x_assum irule >> simp[]
QED

Theorem rest_word_decode_value_array_index:
  decode_value storage offset (ArrayTV tv bd) = SOME (ArrayV av) /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v ==>
  decode_value storage
    (offset + (case bd of Fixed _ => 0 | Dynamic _ => 1) +
     i * type_slot_size tv) tv = SOME v
Proof
  Cases_on `bd` >>
  simp[Once decode_value_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (drule (cj 1 rest_word_decode_array_elements) >> strip_tac >>
      gvs[array_length_def, array_index_def] >>
      `ALOOKUP (enumerate_static_array (default_value tv) 0 vs) i =
       if EL i vs = default_value tv then NONE else SOME (EL i vs)` by
        (qspec_then `default_value tv` mp_tac enumerate_static_array_ALOOKUP >>
         disch_then (qspecl_then [`0`, `vs`, `i`] mp_tac) >> simp[]) >>
      gvs[] >> Cases_on `EL i vs = default_value tv` >> gvs[] >>
      first_x_assum irule >> simp[]) >>
  drule (cj 2 rest_word_decode_array_elements) >> strip_tac >>
  gvs[array_length_def, array_index_def, oEL_THM] >>
  first_x_assum irule >> simp[]
QED

Theorem rest_word_storage_range_array_index:
  storage_range_agree st st' w (ArrayTV tv bd) /\ type_slot_size tv = 1 /\
  i < (case bd of Fixed n => n | Dynamic n => n) /\
  (case bd of Fixed _ => T | Dynamic _ => i < w2n (lookup_storage w st)) ==>
  storage_range_agree st st'
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) tv
Proof
  Cases_on `bd` >> simp[storage_range_agree_def, type_slot_size_def] >>
  strip_tac >> Cases_on `w` >> gvs[wordsTheory.word_add_n2w] >>
  `!base j b. ~dead_bytes st base tv j b` by
    (rpt strip_tac >> drule (cj 1 dead_bytes_range) >> simp[] >> decide_tac) >>
  rpt strip_tac >> first_x_assum irule >>
  simp[loweringStateRelDefsTheory.dead_bytes_def] >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem rest_word_slots_array_index:
  slots_in_range st off (ArrayTV tv bd) /\
  i < (case bd of Fixed n => n | Dynamic n => w2n (read_slot st off)) ==>
  slots_in_range st
    (off + (case bd of Fixed _ => 0 | Dynamic _ => 1) +
     i * type_slot_size tv) tv
Proof
  Cases_on `bd` >> simp[Once slots_in_range_def] >> rpt strip_tac
  >- (irule static_slots_in_range_index >> goal_assum drule >> simp[]) >>
  gvs[AllCaseEqs()] >>
  `MIN (w2n (read_slot st off)) n = w2n (read_slot st off)` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  gvs[] >> drule_all dyn_slots_in_range_index >>
  `off + 1 + i * type_slot_size tv = off + (i * type_slot_size tv + 1)` by
    decide_tac >> simp[]
QED

Theorem rest_word_decode_array_bounds:
  decode_value st off (ArrayTV tv bd) = SOME (ArrayV av) ==>
  array_length (ArrayTV tv bd) av <= (case bd of Fixed n => n | Dynamic n => n) /\
  (case bd of Fixed _ => T | Dynamic _ =>
     array_length (ArrayTV tv bd) av = w2n (read_slot st off))
Proof
  Cases_on `bd` >> simp[Once decode_value_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[array_length_def]
  >- (drule (cj 2 rest_word_decode_array_elements) >> strip_tac >>
      gvs[] >> simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  drule (cj 2 rest_word_decode_array_elements) >> strip_tac >>
  gvs[] >> simp[arithmeticTheory.MIN_DEF] >> decide_tac
QED

Theorem rest_word_storage_holds_array_index:
  storage_holds cx tr (ArrayT ty bd) r w es s /\
  read_result cx r es = (INL (ArrayV av), es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v ==>
  storage_holds cx tr ty (Value v)
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) es s
Proof
  rpt strip_tac >>
  `type_slot_size tv = 1` by metis_tac[word_type_slot_size] >>
  gvs[storage_holds_def, evaluate_type_def] >>
  gvs[read_storage_slot_def, bind_def, get_storage_backend_eq,
      lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `decode_value (get_storage cx es tr) (w2n w) (ArrayTV tv bd)` >>
  gvs[return_def, raise_def] >>
  drule rest_word_decode_array_bounds >> strip_tac >>
  `w2n w + type_slot_size (ArrayTV tv bd) <= dimword (:256)` by
    gvs[storage_range_agree_def] >>
  `w2n (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) =
   w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 1) + i` by
    (Cases_on `bd` >> Cases_on `w` >>
     gvs[type_slot_size_def, wordsTheory.word_add_n2w] >>
     irule arithmeticTheory.MOD_UNIQUE >> qexists_tac `0` >> simp[] >> decide_tac) >>
  drule_all rest_word_decode_value_array_index >> simp[] >> strip_tac >>
  `slots_in_range (get_storage cx es tr)
     (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 1) +
      i * type_slot_size tv) tv` by
    (irule rest_word_slots_array_index >>
     Cases_on `bd` >> gvs[] >> decide_tac) >>
  `storage_range_agree (get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s)
     (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) tv` by
    (irule rest_word_storage_range_array_index >> simp[] >>
     Cases_on `bd` >> gvs[read_slot_def] >> decide_tac) >>
  Cases_on `bd` >> gvs[] >>
  qexists_tac `v` >> simp[read_result_def, return_def]
QED

Theorem rest_word_storage_array_load:
  storage_holds cx tr (ArrayT ty bd) r w es s /\
  read_result cx r es = (INL (ArrayV av), es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v ==>
  (if tr then tload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) s
   else sload (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 1) + i)) s) =
  typed_val_to_w256 tv v
Proof
  strip_tac >> drule_all rest_word_storage_holds_array_index >> strip_tac >>
  drule_all storage_holds_load >> simp[]
QED

Theorem rest_word_storage_array_length:
  storage_holds cx tr (ArrayT ty (Dynamic cap)) r w es s /\
  read_result cx r es = (INL (ArrayV av), es) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  array_length (ArrayTV tv (Dynamic cap)) av <= cap /\
  (if tr then tload w s else sload w s) =
    n2w (array_length (ArrayTV tv (Dynamic cap)) av)
Proof
  strip_tac >> gvs[storage_holds_def, evaluate_type_def] >>
  gvs[read_storage_slot_def, bind_def, get_storage_backend_eq,
      lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `decode_value (get_storage cx es tr) (w2n w) (ArrayTV tv (Dynamic cap))` >>
  gvs[return_def, raise_def] >>
  drule rest_word_decode_array_bounds >> simp[] >> strip_tac >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by simp[type_slot_size_def] >>
  drule_all storage_range_agree_head >> strip_tac >>
  simp[venomStateTheory.tload_def, venomStateTheory.sload_def, read_slot_def] >>
  Cases_on `tr` >> gvs[]
QED
