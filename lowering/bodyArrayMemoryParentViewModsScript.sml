(* The old certificate supplies provenance; the covered read supplies new bytes. *)
Theory bodyArrayMemoryParentViewMods
Ancestors
  bodyPtrDefs bodyPtrBopHashFootprint bodyPtrBopInMemoryContents
  loweringPosts loweringStateRelDefs ptrDiscipline targetSubscriptStorage
  typedArrayLoopValues typedMemoryCopy typedCopyLayoutPtr valueEncoding
  vyperInterpreter vyperPlaceTyping vyperTyping vyperValue venomState
  exprSimProps valueEncodingProps vyperAST vyperState context finite_map words arithmetic

Theorem memory_parent_certificate[local]:
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  p.ptr_location = LocMemory /\
  ptr_vv_ok cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid G1 tn1 s /\
  ghost_kept_at lo ce mid sm G1 tn1 s Gi tni /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  eval_operand p.ptr_operand s = SOME a /\ eval_operand p.ptr_operand it = SOME a /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
  (!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
       val_in_memory (ArrayTV etv bd) v (w2n a) m) ==>
  ptr_mem_ok cx (ArrayT et bd) v p.ptr_operand Gi tni it /\
  ptr_vv_ok cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) fin Gi tni it /\
  op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = op_prov G1 p.ptr_operand /\
  (type_memory_size (ArrayTV etv bd) <> 0 ==>
    ?b sz. op_prov Gi p.ptr_operand = SOME (b,sz) /\ b <= w2n a /\
           w2n a + type_memory_size (ArrayTV etv bd) <= b + sz)
Proof
  strip_tac >>
  `op_taint tn1 p.ptr_operand = {} /\
   ?vm. ptr_mem_ok cx (ArrayT et bd) vm p.ptr_operand G1 tn1 s` by
    (qpat_assum `ptr_vv_ok _ _ _ _ mid _ _ _` (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >>
     simp[] >> strip_tac >> goal_assum (drule_at Any)) >>
  `op_taint tni p.ptr_operand = {} /\
   op_prov Gi p.ptr_operand = op_prov G1 p.ptr_operand` by
    (qpat_assum `ghost_kept_at _ _ mid _ _ _ _ _ _` mp_tac >>
     Cases_on `p.ptr_operand` >> fs[ghost_kept_at_def, op_prov_def, op_taint_def]) >>
  `!z. val_footprint (ArrayTV etv bd) z = type_memory_size (ArrayTV etv bd) /\
       val_store_size (ArrayTV etv bd) z = type_memory_size (ArrayTV etv bd)` by
    (gen_tac >> Cases_on `z` >> simp[val_footprint_def, val_store_size_def]) >>
  `type_memory_size (ArrayTV etv bd) <> 0 ==>
    ?x b n. p.ptr_operand = Var x /\ FLOOKUP Gi x = SOME (b,n) /\
            b <= w2n a /\ w2n a + type_memory_size (ArrayTV etv bd) <= b + n` by
    (strip_tac >>
     `val_footprint (ArrayTV etv bd) vm <> 0` by simp[] >>
     drule_all_then strip_assume_tac ptr_mem_ok_bounds >>
     gvs[op_prov_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `ptr_mem_ok cx (ArrayT et bd) v p.ptr_operand Gi tni it` by
    gvs[ptr_mem_ok_def] >>
  `ptr_vv_ok cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) fin Gi tni it` by gvs[ptr_vv_ok_def] >>
  simp[] >> strip_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  qexistsl [`b`,`n`] >> fs[op_prov_def]
QED

Theorem memory_parent_fixed_view[local]:
  ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME tv /\
  mem_path_offset tv path = SOME (j,ArrayTV etv (Fixed n)) /\
  local_region ce fin.scopes it id (w2n B) sz /\
  j + type_memory_size (ArrayTV etv (Fixed n)) <= sz /\ w2n a = w2n B + j /\
  eval_operand op it = SOME a /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
  value_has_type (ArrayTV etv (Fixed n)) v /\ val_wf (ArrayTV etv (Fixed n)) v /\
  (type_memory_size (ArrayTV etv (Fixed n)) <> 0 ==>
    ?b n'. op_prov Gi op = SOME (b,n') /\ b <= w2n a /\
            w2n a + type_memory_size (ArrayTV etv (Fixed n)) <= b + n') ==>
  (?kvs. v = ArrayV (SArrayV kvs)) /\
  vv_at ce cx (ArrayT et (Fixed n)) sa st2 fin (PlaceR (MemoryPlace id path))
    (LocatedValue t (mk_ptr op LocMemory)) it /\
  (type_memory_size etv <> 0 ==>
    ?b n'. op_prov Gi op = SOME (b,n') /\ b <= w2n a /\
            w2n a + n * type_memory_size etv <= b + n')
Proof
  strip_tac >>
  drule_then strip_assume_tac value_has_type_sarray_cases >>
  qpat_x_assum `v = ArrayV (SArrayV kvs)` SUBST_ALL_TAC >>
  conj_tac >- simp[] >>
  conj_tac
  >- (simp[vv_at_def, mk_ptr_def, val_footprint_def] >>
      disj2_tac >> disj1_tac >> qexistsl [`id`,`w2n B`,`sz`] >>
      simp[local_val_at_def, local_place_at_def, local_path_at_def] >>
      `w2n B + j - w2n B = j` by decide_tac >> simp[] >>
      qexists `path` >> simp[]) >>
  `n <> 0` by
    (Cases_on `n` >> simp[] >>
     qpat_x_assum `evaluate_type _ (ArrayT et (Fixed 0)) = SOME _` mp_tac >>
     simp[Once evaluate_type_def] >> Cases_on `evaluate_type (get_tenv cx) et` >> simp[]) >>
  fs[type_memory_size_def]
QED

Theorem memory_parent_dynamic_view[local]:
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic cap)) = SOME (ArrayTV etv (Dynamic cap)) /\
  lookup_scopes id fin.scopes = SOME entry /\
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Dynamic cap)) /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
  value_has_type (ArrayTV etv (Dynamic cap)) v /\
  (!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
       val_in_memory (ArrayTV etv (Dynamic cap)) v (w2n a) m) /\
  (type_memory_size (ArrayTV etv (Dynamic cap)) <> 0 ==>
    ?b n. op_prov Gi op = SOME (b,n) /\ b <= w2n a /\
           w2n a + type_memory_size (ArrayTV etv (Dynamic cap)) <= b + n) ==>
  subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
  ?vs b n. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\ LENGTH vs < dimword (:256) /\
    read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
    mload (w2n a) it = n2w (LENGTH vs) /\ mem_word_taint tni.t_mem (w2n a) = {} /\
    op_prov Gi op = SOME (b,n) /\ b <= w2n a /\ w2n a + (32 + cap * type_memory_size etv) <= b + n
Proof
  strip_tac >>
  conj_tac >- gvs[runtime_place_typed_memory] >>
  drule_then strip_assume_tac typed_copy_dynarray_typed_value >>
  qpat_x_assum `v = ArrayV (DynArrayV vs)` SUBST_ALL_TAC >>
  `read_memory_path entry path = INL (ArrayV (DynArrayV vs))` by
    (qpat_x_assum `read_result _ _ _ = _` mp_tac >>
     simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def] >>
     Cases_on `read_memory_path entry path` >> simp[return_def, raise_def]) >>
  `LENGTH vs < dimword (:256)` by
    (drule target_storage_array_type_bound >> simp[bound_length_def] >> decide_tac) >>
  `mload (w2n a) it = n2w (LENGTH vs)` by
    (drule dynarray_in_memory_robust_length >>
     disch_then (qspec_then `it.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def, mem_word_at_eq_mload]) >>
  `mem_word_taint tni.t_mem (w2n a) = {}` by
    (drule dynarray_memory_header_clean >> simp[]) >>
  qexists `vs` >> fs[type_memory_size_def]
QED

Theorem array_memory_parent_view_mods:
  lookup_scopes id fin.scopes = SOME entry /\
  local_region ce fin.scopes it id (w2n B) sz /\
  ce.ce_var_type id = SOME rt /\ evaluate_type (get_tenv cx) rt = SOME entry.type /\
  mem_path_offset entry.type path = SOME (j,ArrayTV etv bd) /\
  j + type_memory_size (ArrayTV etv bd) <= sz /\ w2n a = w2n B + j /\
  w2n B + sz <= it.vs_alloca_next /\ w2n B + sz < dimword (:256) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv bd) /\
  post_value_type ce obj = ArrayT et bd /\ p.ptr_location = LocMemory /\
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid G1 tn1 s /\
  ghost_kept_at lo ce mid sm G1 tn1 s Gi tni /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\ (!l. p.ptr_operand <> Label l) /\
  eval_operand p.ptr_operand s = SOME a /\ eval_operand p.ptr_operand it = SOME a /\
  read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
  value_has_type (ArrayTV etv bd) v /\ val_wf (ArrayTV etv bd) v /\
  (!m. mem_agree_outside tni.t_mem it.vs_memory m ==>
       val_in_memory (ArrayTV etv bd) v (w2n a) m) ==>
  ptr_mem_ok cx (ArrayT et bd) v p.ptr_operand Gi tni it /\
  ptr_vv_ok cx (ArrayT et bd) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) fin Gi tni it /\
  op_taint tni p.ptr_operand = {} /\ op_prov Gi p.ptr_operand = op_prov G1 p.ptr_operand /\
  w2n a + type_memory_size (ArrayTV etv bd) <= it.vs_alloca_next /\
  w2n a + type_memory_size (ArrayTV etv bd) < dimword (:256) /\
  (!n. bd = Fixed n ==>
    (?kvs. v = ArrayV (SArrayV kvs)) /\
    vv_at ce cx (ArrayT et (Fixed n)) sa st2 fin (PlaceR (MemoryPlace id path))
      (LocatedValue t (mk_ptr p.ptr_operand LocMemory)) it /\
    (type_memory_size etv <> 0 ==>
      ?b n'. op_prov Gi p.ptr_operand = SOME (b,n') /\ b <= w2n a /\
              w2n a + n * type_memory_size etv <= b + n')) /\
  (!cap. bd = Dynamic cap ==>
    subscripts_type entry.type path = SOME (ArrayTV etv (Dynamic cap)) /\
    ?vs b n. v = ArrayV (DynArrayV vs) /\ LENGTH vs <= cap /\ LENGTH vs < dimword (:256) /\
      read_memory_path entry path = INL (ArrayV (DynArrayV vs)) /\
      mload (w2n a) it = n2w (LENGTH vs) /\ mem_word_taint tni.t_mem (w2n a) = {} /\
      op_prov Gi p.ptr_operand = SOME (b,n) /\ b <= w2n a /\
      w2n a + (32 + cap * type_memory_size etv) <= b + n)
Proof
  strip_tac >>
  qpat_x_assum `post_value_type _ _ = _` (fn th =>
    qpat_x_assum `ptr_vv_ok _ _ _ _ mid _ _ _` (assume_tac o REWRITE_RULE [th])) >>
  drule_all_then strip_assume_tac memory_parent_certificate >>
  `w2n a + type_memory_size (ArrayTV etv bd) <= it.vs_alloca_next /\
   w2n a + type_memory_size (ArrayTV etv bd) < dimword (:256)` by decide_tac >>
  rpt (conj_tac >- simp[]) >> conj_tac
  >- (gen_tac >> disch_then SUBST_ALL_TAC >> irule memory_parent_fixed_view >>
      qpat_assum `mem_path_offset _ _ = _` (irule_at Any) >>
      qpat_assum `local_region _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  gen_tac >> disch_then SUBST_ALL_TAC >> irule memory_parent_dynamic_view >>
  qpat_assum `read_result _ _ _ = _` (irule_at Any) >> simp[] >>
  goal_assum (drule_at Any)
QED
