(* Array sub-layout and runtime immutable contents; no execution relation. *)
Theory bodyPtrBopInCodeContents
Ancestors exprSimUnwrap exprSimProps exprSimAggregateEncoding valueEncodingProps
  vyperTyping compileEnv loweringPosts exprLoweringProps venomMemDefs
  valueEncodingProofs valueEncoding vyperValueOperation vyperValue vyperAssignPreservesType
  list alist

Theorem membership_array_memory_index:
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
  drule_all elems_in_memory_EL >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem membership_array_element_extent:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av ==>
  (case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32 + 32 <=
  type_memory_size (ArrayTV et bd)
Proof
  Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, array_length_def, type_memory_size_def] >> decide_tac
QED

Theorem membership_array_sub_layout:
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  type_memory_size et = 32 /\ i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  sub_layout (ArrayTV et bd) (ArrayV av)
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) et v
Proof
  strip_tac >> simp[sub_layout_def] >> conj_tac
  >- (drule_all membership_array_element_extent >> simp[]) >>
  rpt strip_tac >> drule_all membership_array_memory_index >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >> simp[]
QED

Theorem membership_array_immutable_index:
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  immutable_holds cenv cx ty (Value v)
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)) es s
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (ArrayT ty bd) = SOME (ArrayTV et bd)` by
    (fs[immutable_holds_def, evaluate_type_def, AllCaseEqs()]) >>
  irule immutable_holds_sub >>
  `type_memory_size et = 32` by metis_tac[word_tv_memory_size] >>
  `well_formed_type_value et` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type et v` by (irule array_index_has_type >> metis_tac[]) >>
  `sub_layout (ArrayTV et bd) (ArrayV av)
     ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32) et v` by
    (irule membership_array_sub_layout >> simp[]) >>
  qpat_assum `immutable_holds _ _ _ _ _ _ _` (irule_at Any) >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_x_assum `sub_layout _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [arithmeticTheory.MULT_COMM, arithmeticTheory.ADD_COMM]
QED

Theorem membership_array_immutable_dload:
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ty bd) (Value (ArrayV av)) w es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME et /\
  value_has_type (ArrayTV et bd) (ArrayV av) /\
  i < array_length (ArrayTV et bd) av /\
  array_index (ArrayTV et bd) av (&i) = SOME v ==>
  word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n (w + n2w
      ((case bd of Fixed _ => 0 | Dynamic _ => 32) + i * 32)))
      s.vs_data_section ++ REPLICATE 32 0w)) = typed_val_to_w256 et v
Proof
  strip_tac >> drule_all membership_array_immutable_index >> strip_tac >>
  drule_all immutable_holds_dload >> simp[]
QED
