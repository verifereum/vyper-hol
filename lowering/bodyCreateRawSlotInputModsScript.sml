(* Materialise the reached RawCreate bytecode at its original slot key. *)
Theory bodyCreateRawSlotInputMods
Ancestors
  bodyFullPostsMods loweringPosts bodyPtrDefs context loweringStateRelDefs
  vyperState valueEncodingProps

Theorem raw_create_slot_input_mods:
  vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G1 tn1 t /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  vv_type vv = BaseT (BytesT (Dynamic k)) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at a x) /\
  cap = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
  vv_location vv = SOME (slot_loc tr) ==>
  ?tag p key.
    vv = LocatedValue tag p /\ p.ptr_location = slot_loc tr /\
    tag = BaseT (BytesT (Dynamic k)) /\
    storage_holds cx tr tag (Value (BytesV bs)) key ee t /\
    ptr_vv_ok cx tag (Value (BytesV bs)) (LocatedValue tag p) ee G1 tn1 t /\
    eval_operand p.ptr_operand t = SOME key /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at a x) /\
    cap = 32 * type_slot_size (BaseTV (BytesT (Dynamic k)))
Proof
  Cases_on `vv` >- simp[vv_location_def] >>
  simp[vv_location_def,vv_type_def,vv_operand_def] >> strip_tac >>
  rename1 `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ (LocatedValue tag p) _` >>
  `p.ptr_location <> LocCode /\ p.ptr_location <> LocMemory` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  `vv_holds_mods cenv cx (post_value_type cenv code) raw (LocatedValue tag p) ee t` by
    fs[vv_post_mods_def] >>
  `tag = post_value_type cenv code /\
   ?key. eval_operand p.ptr_operand t = SOME key /\ storage_holds cx tr tag raw key ee t` by
    (qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >> fs[slot_loc_def] >> simp[vv_holds_mods_def,vv_holds_def] >>
     strip_tac >> simp[] >> rename1 `eval_operand p.ptr_operand t = SOME key` >>
     qexists `key` >> simp[]) >>
  pop_assum strip_assume_tac >>
  `storage_holds cx tr tag (Value (BytesV bs)) key ee t` by
    (qpat_x_assum `storage_holds cx tr tag raw key ee t` mp_tac >>
     simp[storage_holds_def,read_result_def,return_def]) >>
  `ptr_vv_ok cx tag (Value (BytesV bs)) (LocatedValue tag p) ee G1 tn1 t` by
    (qpat_assum `tag = post_value_type cenv code` (fn th =>
       qpat_x_assum `ptr_vv_ok cx _ raw _ ee G1 tn1 t`
         (mp_tac o REWRITE_RULE [GSYM th])) >>
     simp[ptr_vv_ok_def]) >>
  qexists `key` >> gvs[type_memory_size_slots]
QED
