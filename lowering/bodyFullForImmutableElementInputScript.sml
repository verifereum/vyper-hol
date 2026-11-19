(* Input domain for the positioned LocCode element copy of a For loop. *)
Theory bodyFullForImmutableElementInput
Ancestors
  bodyFullForFacts bodySimDeclCases bodySim supportedStmts vyperAST
  vyperTypeValues memoryValueAbiStatic vyperValueOperation vyperTyping exprSimHyps compileEnv
  whitelistForIterImmCopy exprSimCopy exprSimBopRestWordLoadSafety allocaSiteResource
  loweringPosts exprLoweringProps loweringStateRelDefs bodyPtrDefs
  ptrDiscipline venomMemDefs venomState valueEncoding valueEncodingProps
  valueEncodingTyping abiDecodeStaticProps arithmetic words list finite_map

Theorem for_immutable_element_copy_input:
  supported_stmt tops bindings (For id fty (Array e) n loop_body) /\
  body_inv tops ctx c cx /\ expr_sim_inv c cx env es /\
  arr_ty = expr_type e /\
  arr_elem_ty = (case arr_ty of ArrayT et _ => et | _ => fty) /\
  evaluate_type (get_tenv cx) arr_ty = SOME (ArrayTV tv bd) /\
  immutable_holds c cx (post_value_type c e) rv bw es s /\
  read_result cx rv es = (INL (ArrayV av),es) /\
  vs = MAP Value (array_elements (ArrayTV tv bd) av) /\ k < LENGTH vs /\
  bytes = elem_size_in_location c LocCode arr_elem_ty /\
  header = (case bd of Fixed _ => 0 | Dynamic _ => 32) /\
  lookup_var out s = SOME (bw + n2w (header + k * bytes)) /\
  not_fresh_at sa out /\
  stmt_state_rel H ctx func c cx es s /\ ghost_inv_at D lo d c cx es G tn s /\
  (c.ce_is_ctor ==> w2n bw + type_memory_size (ArrayTV tv bd) <= lo) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dst,capacity) /\
  bytes <= capacity /\
  (!region x. c.ce_imm_alloca = SOME region /\ region = Var x ==>
    not_fresh_at sa x) /\
  op_taint tn (Var out) = {} /\ op_prov G (Var out) = NONE ==>
  arr_ty = ArrayT fty bd /\ arr_elem_ty = fty /\
  evaluate_type (get_tenv cx) fty = SOME tv /\
  bytes = type_memory_size tv /\ (bytes = 32 \/ ?q. bytes = 32*q /\ 32 < bytes) /\
  w2n dst + capacity < dimword (:256) /\
  ?v a. EL k vs = Value v /\ value_has_type tv v /\ val_wf tv v /\
    immutable_holds c cx fty (Value v) a es s /\
    eval_operand (Var out) s = SOME a /\ copy_old_operand sa (Var out) /\
    op_taint tn (Var out) = {} /\
    w2n a = w2n bw + header + k * bytes /\
    w2n dst + bytes <= s.vs_alloca_next /\
    (c.ce_is_ctor ==>
      op_prov G (Var out) = NONE /\
      w2n a + bytes <= lo /\ lo <= w2n dst /\
      w2n a + bytes <= s.vs_alloca_next /\
      loweringStateRelDefs$regions_disjoint (w2n a) bytes (w2n dst) bytes /\
      !region. c.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
        op_taint tn region = {} /\ op_prov G region = NONE) /\
    (~c.ce_is_ctor ==>
      w2n a + bytes <= LENGTH s.vs_data_section /\ w2n a + bytes < dimword (:256))
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule supported_stmt_for_projection >> simp[] >> strip_tac >>
  drule evaluate_type_ArrayTV_result >>
  disch_then (qx_choose_then `et` strip_assume_tac) >>
  `expr_type e = ArrayT et bd` by fs[] >>
  `et = fty` by
    (qpat_assum `supported_iterator _ _ (Array _) _` mp_tac >>
     Cases_on `e` >> fs[supported_iterator_def, expr_type_def] >>
     Cases_on `bd` >> gvs[]) >>
  `post_value_type c e = expr_type e` by
    (irule post_value_type_declared_return >> qexists_tac `tops` >>
     `supported_program tops /\ c.ce_func_return_type = build_func_return_type tops` by
       fs[body_inv_def] >> simp[] >>
     rpt gen_tac >> disch_then SUBST_ALL_TAC >>
     qpat_x_assum `supported_iterator _ _ (Array _) _` mp_tac >>
     simp[supported_iterator_def]) >>
  `immutable_holds c cx (ArrayT fty bd) rv bw es s` by fs[] >>
  `value_has_type (ArrayTV tv bd) (ArrayV av) /\
   w2n bw + type_memory_size (ArrayTV tv bd) < dimword (:256)` by
    (qpat_assum `immutable_holds _ _ (ArrayT _ _) _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [immutable_holds_def]) >>
     gvs[] >>
     rename1 `sub_layout itv iv delta (ArrayTV tv bd) (ArrayV av)` >>
     rename1 `root + type_memory_size itv < dimword (:256)` >>
     `delta + type_memory_size (ArrayTV tv bd) <= type_memory_size itv` by
       fs[sub_layout_def] >>
     `root + delta < dimword (:256)` by decide_tac >>
     simp[w2n_n2w] >> decide_tac) >>
  `val_wf (ArrayTV tv bd) (ArrayV av)` by simp[value_has_type_val_wf] >>
  `well_formed_type_value (ArrayTV tv bd)` by metis_tac[evaluate_type_well_formed_type_value] >>
  qpat_x_assum `vs = MAP _ _` SUBST_ALL_TAC >>
  qpat_x_assum `k < LENGTH (MAP _ _)`
    (assume_tac o REWRITE_RULE [LENGTH_MAP]) >>
  `type_memory_bytes c fty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `bytes = type_memory_size tv` by
    simp[elem_size_in_location_def, is_slot_addressed_def] >>
  `immutable_holds c cx fty (Value (EL k (array_elements (ArrayTV tv bd) av)))
     (bw + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
                  k * type_memory_size tv)) es s /\
   value_has_type tv (EL k (array_elements (ArrayTV tv bd) av)) /\
   0 < type_memory_size tv` by
    ((irule immutable_iter_element_ready >> goal_assum (drule_at Any) >> simp[] >> (metis_tac[immutable_iter_element_ready]))) >>
  qpat_x_assum `bytes = elem_size_in_location _ _ _` kall_tac >>
  `header + k * bytes + bytes <= type_memory_size (ArrayTV tv bd)` by
    (Cases_on `bd` >> rename1 `ArrayTV tv (_ cap)` >>
     `k < cap` by
       (Cases_on `av` >>
        gvs[value_has_type_def, array_elements_def, LENGTH_GENLIST] >> decide_tac) >>
     qpat_x_assum `bytes = type_memory_size tv` SUBST_ALL_TAC >>
     `SUC k * type_memory_size tv <= cap * type_memory_size tv` by
       simp[LE_MULT_RCANCEL] >>
     pop_assum (assume_tac o PURE_REWRITE_RULE [MULT_CLAUSES]) >>
     fs[type_memory_size_def, AC MULT_ASSOC MULT_COMM] >> decide_tac) >>
  `w2n bw + (header + k * bytes) < dimword (:256)` by decide_tac >>
  `w2n (bw + n2w (header + k * bytes)) = w2n bw + (header + k * bytes)` by
    (irule w2n_add_n2w_lt >> simp[]) >>
  suspend "copy_domain"
QED

Resume for_immutable_element_copy_input[copy_domain]:
  `w2n bw + type_memory_size (ArrayTV tv bd) <=
    (if c.ce_is_ctor then s.vs_alloca_next else LENGTH s.vs_data_section)` by
    (irule rest_word_immutable_region_bound >> metis_tac[]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `lo <= w2n dst` by
    (qhdtm_assum `allocas_from` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  `w2n dst + capacity <= s.vs_alloca_next` by
    (irule alloca_site_registered_below >>
     `alloca_inv s` by fs[Once stmt_state_rel_def] >>
     simp[] >> qexists_tac `aid` >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (`alloca_room ctx func s` by fs[Once stmt_state_rel_def] >>
     drule alloca_room_next_lt >> simp[]) >>
  `w2n dst + capacity < dimword (:256)` by decide_tac >>
  `w2n dst + bytes <= s.vs_alloca_next` by decide_tac >>
  `c.ce_is_ctor ==> lo <> 0` by
    (strip_tac >>
     qpat_assum `c.ce_is_ctor ==> _ <= lo` (assume_tac o UNDISCH) >>
     decide_tac) >>
  `!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE` by
    (`immutable_base_zero c s` by fs[Once stmt_state_rel_def] >>
     Cases >>
     fs[immutable_base_zero_def, ghost_inv_at_def,
        copy_old_operand_def, op_taint_def, op_prov_def] >> metis_tac[]) >>
  qabbrev_tac `a = bw + n2w (header + k * bytes)` >>
  `w2n a = w2n bw + header + k * bytes` by
    (simp[Abbr `a`] >> decide_tac) >>
  `w2n a + bytes <= w2n bw + type_memory_size (ArrayTV tv bd)` by decide_tac >>
  `c.ce_is_ctor ==> w2n a + bytes <= lo /\
    w2n a + bytes <= s.vs_alloca_next /\
    loweringStateRelDefs$regions_disjoint (w2n a) bytes (w2n dst) bytes` by
    (strip_tac >> PURE_REWRITE_TAC [loweringStateRelDefsTheory.regions_disjoint_def] >>
     qpat_assum `c.ce_is_ctor ==> _ <= lo` (assume_tac o UNDISCH) >>
     decide_tac) >>
  `~c.ce_is_ctor ==> w2n a + bytes <= LENGTH s.vs_data_section /\
      w2n a + bytes < dimword (:256)` by
    (strip_tac >>
     qpat_assum `_ <= (if c.ce_is_ctor then _ else _)` mp_tac >>
     qpat_assum `~c.ce_is_ctor` (fn th => PURE_REWRITE_TAC [th, COND_CLAUSES]) >>
     decide_tac) >>
  qpat_x_assum `bytes = type_memory_size tv` SUBST_ALL_TAC >>
  qpat_x_assum `header = _` SUBST_ALL_TAC >>
  `immutable_holds c cx fty (Value (EL k (array_elements (ArrayTV tv bd) av))) a es s` by
    simp[Abbr `a`] >>
  `type_memory_size tv = 32 \/ ?q. type_memory_size tv = 32*q /\
      32 < type_memory_size tv` by
    (Cases_on `type_slot_size tv = 1` >- simp[type_memory_size_slots] >>
     disj2_tac >> qexists_tac `type_slot_size tv` >> simp[type_memory_size_slots] >>
     `0 < type_slot_size tv` by
       (qpat_assum `0 < type_memory_size tv`
          (mp_tac o PURE_REWRITE_RULE [type_memory_size_slots]) >>
        simp[]) >>
     decide_tac) >>
  qpat_x_assum `et = fty` SUBST_ALL_TAC >>
  `arr_elem_ty = fty` by fs[] >>
  simp[elem_size_in_location_def, is_slot_addressed_def] >>
  qexistsl_tac [`EL k (array_elements (ArrayTV tv bd) av)`, `a`] >>
  fs[EL_MAP, eval_operand_def, copy_old_operand_def, value_has_type_val_wf]
QED

Finalise for_immutable_element_copy_input
