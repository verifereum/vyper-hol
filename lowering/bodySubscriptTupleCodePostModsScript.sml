(* Select a tuple cell in the same immutable backing, at the ADD endpoint. *)
Theory bodySubscriptTupleCodePostMods
Ancestors
  bodyFullPostsMods exprSimAttributeProps exprSimCopy exprSimProps
  reasonEndpointResourcesPtr tupleMemoryLayout vyperTypeDefaults
  loweringPosts bodyPtrDefs ptrDiscipline context valueEncoding valueEncodingDefs
  vyperInterpreter venomState arithmetic words list

Theorem code_tuple_slice[local]:
  values_have_types tvs vs /\ k < LENGTH tvs /\
  off = SUM (MAP type_memory_size (TAKE k tvs)) /\
  off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs) ==>
  value_has_type (EL k tvs) (EL k vs) /\
  sub_layout (TupleTV tvs) (ArrayV (TupleV vs)) off (EL k tvs) (EL k vs)
Proof
  simp[values_have_types_LIST_REL, LIST_REL_EL_EQN] >> strip_tac >>
  simp[sub_layout_def, val_in_memory_def] >> rpt strip_tac >>
  irule tuple_in_memory_element >> simp[]
QED

Theorem code_tuple_base[local]:
  vv_loc bvv = LocCode /\ vv_holds_mods cenv cx ty raw bvv ee t /\
  eval_operand (vv_operand bvv) t = SOME w ==>
  vv_location bvv = SOME LocCode /\ immutable_holds_mods cenv cx ty raw w ee t
Proof
  Cases_on `bvv` >>
  simp[vv_loc_def, vv_location_def, vv_operand_def, vv_holds_mods_def] >>
  strip_tac >> gvs[]
QED

Theorem code_tuple_no_provenance[local]:
  vv_loc bvv = LocCode /\ ptr_vv_ok cx ty raw bvv ee G tn s ==>
  op_prov G (vv_operand bvv) = NONE
Proof
  Cases_on `bvv` >>
  simp[vv_loc_def, vv_location_def, vv_operand_def, ptr_vv_ok_def]
QED

Theorem code_tuple_owner_slice[local]:
  immutable_holds_mods cenv cx (TupleT tys) raw w ee t /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\
  value_has_type (EL k tvs) (EL k vs) /\
  sub_layout (TupleTV tvs) (ArrayV (TupleV vs)) off (EL k tvs) (EL k vs) ==>
  immutable_holds_mods cenv cx (EL k tys) raw' (w + n2w off) ee t
Proof
  simp[immutable_holds_mods_def] >> strip_tac >>
  qexistsl_tac [`src`,`tops`] >> simp[] >>
  irule immutable_holds_sub >> goal_assum (drule_at Any) >>
  qexistsl_tac [`TupleT tys`,`raw`] >> simp[]
QED

Theorem code_tuple_backing_slice[local]:
  immutable_holds_mods cenv cx (TupleT tys) raw w ee t /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  sub_layout (TupleTV tvs) (ArrayV (TupleV vs)) off (EL k tvs) (EL k vs) /\
  w2n w + type_memory_size (TupleTV tvs) <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem) /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem ==>
  w2n (w + n2w off) + type_memory_size (EL k tvs) <= lo /\
  (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
         val_in_memory (EL k tvs) (EL k vs) (w2n (w + n2w off)) mem)
Proof
  strip_tac >> fs[immutable_holds_mods_def] >>
  drule_all_then assume_tac immutable_holds_read_value >>
  drule_all_then strip_assume_tac immutable_holds_bounds >>
  qpat_x_assum `sub_layout _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [sub_layout_def]) >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule field_ptr_w2n >>
     qexistsl_tac [`type_memory_size (EL k tvs)`,`type_memory_size (TupleTV tvs)`] >>
     simp[]) >>
  simp[] >> gen_tac >> strip_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qpat_assum `!b mem. val_in_memory (TupleTV _) _ _ _ ==> _` irule >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem tuple_subscript_code_post_mods:
  vv_loc bvv = LocCode /\
  vv_holds_mods cenv cx (TupleT tys) raw bvv ee t /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs) /\
  read_result cx raw ee = (INL (ArrayV (TupleV vs)),ee) /\
  read_result cx raw' ee = (INL (EL k vs),ee) /\
  values_have_types tvs vs /\ k < LENGTH tvs /\
  off = SUM (MAP type_memory_size (TAKE k tvs)) /\
  off + type_memory_size (EL k tvs) <= type_memory_size (TupleTV tvs) /\
  eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w off) /\
  ptr_vv_ok cx (TupleT tys) raw bvv ee G tn s /\
  dst = Var out /\ FLOOKUP G' out = op_prov G (vv_operand bvv) /\
  op_taint tn' dst = {} /\ t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
   ?v. read_result cx raw ee = (INL v,ee) /\
       !rt a. evaluate_type (get_tenv cx) (TupleT tys) = SOME rt /\
              eval_operand (vv_operand bvv) s = SOME a ==>
              w2n a + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                     val_in_memory rt v (w2n a) mem)) ==>
  let vv = LocatedValue (EL k tys) (mk_ptr dst LocCode) in
  vv_holds_mods cenv cx (EL k tys) raw' vv ee t /\
  ptr_vv_ok cx (EL k tys) raw' vv ee G' tn' t /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx raw' ee = (INL v,ee) /\
       !rt a. evaluate_type (get_tenv cx) (EL k tys) = SOME rt /\
              eval_operand (vv_operand vv) t = SOME a ==>
              w2n a + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                     val_in_memory rt v (w2n a) mem))
Proof
  strip_tac >> drule_all_then strip_assume_tac code_tuple_base >>
  drule_all_then strip_assume_tac code_tuple_slice >>
  drule_all_then assume_tac code_tuple_owner_slice >>
  drule_all_then assume_tac code_tuple_no_provenance >>
  `op_prov G' dst = NONE` by simp[op_prov_def] >>
  qpat_x_assum `dst = Var out` kall_tac >>
  qpat_x_assum `off = SUM _` kall_tac >>
  simp[LET_THM, vv_holds_mods_def, vv_location_def, vv_operand_def,
       ptr_vv_ok_def, mk_ptr_def] >>
  strip_tac >>
  `w2n w + type_memory_size (TupleTV tvs) <= lo /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) (w2n w) mem)` by
    (qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >> simp[]) >>
  drule_all_then strip_assume_tac code_tuple_backing_slice >> simp[]
QED
