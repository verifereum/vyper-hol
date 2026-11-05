(* Location adapters for the nonliteral membership loop. *)
Theory exprSimBopRestWordLoads
Ancestors
  exprSimBopRestWordIndex exprSimAggregateEncoding valueEncodingProps vyperTyping
  compileEnv loweringPosts exprSimUnwrapProps exprLoweringProps venomMemDefs
  valueEncodingProofs valueEncoding vyperValueOperation vyperValue list alist

Theorem rest_word_array_memory_index:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  val_in_memory (ArrayTV et bd) (ArrayV av) off mem /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  val_in_memory et v
    (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
     i * type_memory_size et) mem
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_sarray, val_in_memory_dynarray,
       array_index_def, oEL_THM] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  >- (drule_all kvs_in_memory_lookup >> simp[]) >>
  drule_all elems_in_memory_EL >> simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem rest_word_memory_word:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v off mem ==>
  mem_word_at off mem = typed_val_to_w256 tv v
Proof
  strip_tac >> Cases_on `ty` >>
  gvs[is_word_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, typed_val_to_w256_def,
      val_to_w256_def]
QED

Theorem rest_word_array_memory_load:
  is_word_type ty /\ evaluate_type tenv ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  val_in_memory (ArrayTV et bd) (ArrayV av) off mem /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  mem_word_at (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
               i * type_memory_size et) mem = typed_val_to_w256 et v
Proof
  strip_tac >> irule rest_word_memory_word >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by
    (irule vyperAssignPreservesTypeTheory.array_index_has_type >> metis_tac[]) >>
  `val_in_memory et v
     (off + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
      i * type_memory_size et) mem` by
    (irule rest_word_array_memory_index >> metis_tac[]) >>
  metis_tac[]
QED

Theorem rest_word_array_element_extent:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av ==>
  (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
  type_memory_size (ArrayTV et bd)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, array_length_def, type_memory_size_def] >>
  decide_tac
QED

Theorem rest_word_located_memory_bound:
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (ArrayV av))
    (LocatedValue ty p) s /\ p.ptr_location = LocMemory /\
  expr_type e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  eval_operand p.ptr_operand s = SOME w ==>
  w2n w + type_memory_size tv < dimword (:256)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `local_ptrs_rel func cenv es'.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, val_footprint_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  disch_then (qspec_then `tv` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[alloca_next_valid_def, local_region_def, local_ptrs_rel_def]
  >- (qpat_x_assum `!aid base sz. _` drule >> decide_tac)
  >- (qpat_x_assum `!name entry p sz. _` drule >>
      disch_then drule >> strip_tac >> gvs[] >> decide_tac) >>
  simp[wordsTheory.w2n_lt]
QED

Theorem rest_word_array_sub_layout:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  sub_layout (ArrayTV et bd) (ArrayV av)
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) et v
Proof
  strip_tac >> simp[sub_layout_def] >> conj_tac
  >- (drule_all rest_word_array_element_extent >> simp[]) >>
  rpt strip_tac >> drule_all rest_word_array_memory_index >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  simp[]
QED

Theorem rest_word_sub_layout_trans:
  sub_layout tv1 v1 k1 tv2 v2 /\ sub_layout tv2 v2 k2 tv3 v3 ==>
  sub_layout tv1 v1 (k1 + k2) tv3 v3
Proof
  simp[sub_layout_def] >> strip_tac >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >> first_x_assum drule >>
  simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]
QED
