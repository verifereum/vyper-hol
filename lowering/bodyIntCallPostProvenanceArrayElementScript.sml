Theory bodyIntCallPostProvenanceArrayElement
Ancestors
  exprSimSubscriptArrayFramed typedCopyLayoutPtr exprSimAttributeProps
  exprSimProps loweringPosts context valueEncodingDefs valueEncoding
  vyperValueOperation vyperAST arithmetic words

Theorem vv_at_array_element:
  vv_at cenv cx (ArrayT et bd) sa sb es r (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx child es = (INL v,es) /\ val_wf etv v /\
  mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv) /\
  j + val_footprint etv v <= val_footprint (ArrayTV etv bd) (ArrayV av) /\
  (!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id path)) /\
  eval_operand dst s = SOME dw /\ w2n dw = w2n w + j ==>
  vv_at cenv cx et sa sb es child (LocatedValue et (mk_ptr dst LocMemory)) s
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, mk_ptr_def] >> strip_tac >> gvs[]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >>
  simp[] >>
  `j + w2n w - b = (w2n w - b) + j` by decide_tac >>
  qpat_x_assum `j + w2n w - b = _` SUBST1_TAC >>
  conj_tac
  >- (drule_all local_val_at_array_element >>
      disch_then (qspec_then `v` ACCEPT_TAC)) >>
  irule local_place_at_step >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem array_element_footprint_contained:
  value_has_type (ArrayTV et bd) (ArrayV av) /\ val_wf et v /\
  array_index (ArrayTV et bd) av i = SOME v ==>
  (case bd of Fixed _ => 0 | Dynamic _ => 32) +
    Num i * type_memory_size et + val_footprint et v <=
    val_footprint (ArrayTV et bd) (ArrayV av)
Proof
  strip_tac >> Cases_on `bd`
  >- (`val_footprint et v <= type_memory_size et` by
        (irule val_footprint_le >> simp[]) >>
      Cases_on `av` >>
      gvs[array_index_def, vyperTypingTheory.value_has_type_def,
          val_footprint_def, type_memory_size_def, AllCaseEqs()] >>
      `(Num i + 1) * type_memory_size et <= n * type_memory_size et` by
        (irule LESS_MONO_MULT >> decide_tac) >>
      qpat_x_assum `(_ + 1) * _ <= _` mp_tac >>
      pure_rewrite_tac[RIGHT_ADD_DISTRIB, MULT_LEFT_1] >> decide_tac) >>
  Cases_on `av` >>
  gvs[array_index_def, listTheory.oEL_THM, AllCaseEqs()]
  >~ [`ArrayV (SArrayV l)`] >- gvs[vyperTypingTheory.value_has_type_def]
  >~ [`ArrayV (TupleV l)`] >- gvs[vyperTypingTheory.value_has_type_def] >>
  drule_all dynarray_live_child_footprint >> simp[AC ADD_ASSOC ADD_COMM]
QED

Theorem array_element_address_no_wrap:
  value_has_type (ArrayTV et bd) (ArrayV av) /\ val_wf et v /\
  array_index (ArrayTV et bd) av i = SOME v /\
  w2n (w:bytes32) + val_footprint (ArrayTV et bd) (ArrayV av) < dimword (:256) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size et ==>
  w2n (w + n2w j) = w2n w + j
Proof
  strip_tac >> drule_all array_element_footprint_contained >> strip_tac >>
  irule field_ptr_w2n >>
  qexistsl [`val_footprint et v`, `val_footprint (ArrayTV et bd) (ArrayV av)`] >>
  gvs[]
QED

Theorem vv_post_array_element_general:
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sb s0 es' r
    (LocatedValue ann p) s /\
  expr_type obj = ArrayT et bd /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\
  read_result cx r es' = (INL (ArrayV av),es') /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf etv v /\ value_has_type etv v /\
  read_result cx child es' = (INL v,es') /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\
  (!id path'. child = PlaceR (MemoryPlace id path') <=>
     ?path. path' = path ++ [ValueSubscript (IntV i)] /\ r = PlaceR (MemoryPlace id path)) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 es' child
    (LocatedValue et (mk_ptr dst p.ptr_location)) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_holds cenv cx (ArrayT et bd) r (LocatedValue ann p) es' s` by
    gvs[vv_post_def, expr_type_def] >>
  drule_all vv_holds_array_element >> strip_tac >>
  `vv_at cenv cx et sa sb es' child (LocatedValue et (mk_ptr dst p.ptr_location)) s` by
    (Cases_on `p.ptr_location = LocMemory`
     >- (`vv_at cenv cx (ArrayT et bd) sa sb es' r (LocatedValue ann p) s`
           by gvs[vv_post_def, expr_type_def] >>
         `mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv)` by
           (Cases_on `av` >> Cases_on `bd` >>
            gvs[mem_step_offset_def, array_index_def, val_wf_def,
                listTheory.oEL_THM, AllCaseEqs()]) >>
         drule_all array_element_footprint_contained >> strip_tac >>
         gvs[] >> irule vv_at_array_element >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     `vv_at cenv cx (ArrayT et bd) sa sb es' r (LocatedValue ann p) s`
       by gvs[vv_post_def, expr_type_def] >>
     pop_assum mp_tac >>
     simp[vv_at_def, mk_ptr_def, compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  gvs[vv_post_def, expr_type_def, expr_has_effect_thm, mk_ptr_def] >>
  first_assum ACCEPT_TAC
QED
