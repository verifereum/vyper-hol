(* Restrict the linked Attribute post at the actual fresh ADD endpoint. *)
Theory bodyAttributeNoncodeFieldMods
Ancestors
  bodyFullPostsMods bodyPtrAttributeCase bodyPtrAttributeStorage
  exprSimAttributeProps exprSimAttributeFields exprSimFieldLayout exprSimVVFrame
  exprSimProps exprSimMemDefs exprSimBuffer loweringPosts stateRelProj
  accountsRelProps vyperPlaceResultTyping vyperLookupStorage
  exprLowering exprLoweringProps compileEnv context vyperAST
  valueEncoding valueEncodingDefs vyperState venomState words finite_map arithmetic

Theorem noncode_holds[local]:
  vv_loc vv <> LocCode ==>
  (vv_holds_mods cenv cx ty raw vv ee s <=> vv_holds cenv cx ty raw vv ee s)
Proof
  Cases_on `vv` >> simp[vv_loc_def, vv_location_def, vv_holds_mods_def]
QED

Theorem struct_at_mem[local]:
  vv_at cenv cx (StructT sid) sa sb ee raw vv t /\
  vv_loc vv = LocMemory /\ eval_operand (vv_operand vv) t = SOME w /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) ==>
  (?aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
               sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
               b <= w2n w /\ w2n w + type_memory_size_fields fs <= b + sz /\
               (!n lb lsz. local_region cenv ee.scopes t n lb lsz ==>
                          b + sz <= lb \/ lb + lsz <= b)) \/
  (?n b sz. local_region cenv ee.scopes t n b sz /\
            b <= w2n w /\ w2n w + type_memory_size_fields fs <= b + sz /\
            local_path_at cenv cx n (w2n w - b) (StructTV fs) /\
            local_place_at cenv cx n (w2n w - b) (StructTV fs) raw) \/
  type_memory_size_fields fs = 0
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_at_def, is_word_type_def, local_val_at_def] >>
  rpt strip_tac >>
  gvs[val_footprint_def, type_memory_size_def, local_place_at_def] >>
  metis_tac[]
QED

Theorem noncode_at_field[local]:
  vv_at cenv cx (StructT sid) sa sb ee raw bvv t /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME dw /\
  (vv_loc bvv = LocMemory ==> w2n dw = w2n w + off) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  off + type_memory_size ftv <= type_memory_size_fields fs /\
  mem_step_offset (StructTV fs) (AttrSubscript fld) = SOME (off,ftv) /\
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) ==>
  vv_at cenv cx ann sa sb ee raw'
    (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t
Proof
  strip_tac >> drule_then assume_tac select_result_memory_place >>
  simp[vv_at_def, mk_ptr_def] >> conj_tac
  >- (rpt strip_tac >>
      `?p0. raw = PlaceR (MemoryPlace id p0)` by metis_tac[] >>
      qpat_x_assum `vv_at _ _ (StructT _) _ _ _ _ _ _` mp_tac >>
      Cases_on `bvv` >>
      gvs[vv_at_def, vv_loc_def, vv_location_def, is_word_type_def]) >>
  strip_tac >> drule_all_then strip_assume_tac struct_at_mem >>
  `val_footprint ftv fv <= type_memory_size ftv` by simp[val_footprint_le] >>
  gvs[]
  >~ [`FLOOKUP t.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_region cenv ee.scopes t n b sz`]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[] >>
      `w2n w - b + off = w2n w + off - b` by decide_tac >>
      `local_place_at cenv cx n (w2n w - b + off) ftv raw'` by
        (irule local_place_at_step >> metis_tac[]) >>
      drule_all local_path_at_step >> gvs[local_path_at_val_at] >> decide_tac) >>
  disj2_tac >> disj2_tac >> decide_tac
QED

Theorem struct_mem_store_bound[local]:
  vv_store_bound cx (StructT sid) lt ee raw bvv s /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) s = SOME w /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) ==>
  type_memory_size_fields fs = 0 \/
  w2n w + type_memory_size_fields fs <= s.vs_alloca_next
Proof
  Cases_on `bvv` >>
  simp[vv_store_bound_def, vv_loc_def, vv_location_def, vv_operand_def,
       is_word_type_def, val_store_size_def, type_memory_size_def] >>
  rpt strip_tac >> gvs[type_memory_size_def]
QED

Theorem field_mem_store_bound[local]:
  read_result cx raw' ee = (INL fv,ee) /\
  eval_operand dst t = SOME dw /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  off + type_memory_size ftv <= type_memory_size_fields fs /\
  w2n dw = w2n w + off /\
  (type_memory_size_fields fs = 0 \/
   w2n w + type_memory_size_fields fs <= t.vs_alloca_next) ==>
  vv_store_bound cx ann ann ee raw' (LocatedValue ann (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> drule_then assume_tac val_store_size_le >>
  simp[vv_store_bound_def, mk_ptr_def] >> decide_tac
QED

Theorem struct_mem_holds[local]:
  vv_holds cenv cx (StructT sid) raw bvv ee t /\
  vv_loc bvv = LocMemory /\ eval_operand (vv_operand bvv) t = SOME w /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) ==>
  val_in_memory (StructTV fs) (StructV vals) (w2n w) t.vs_memory
Proof
  Cases_on `bvv` >>
  simp[vv_holds_def, vv_loc_def, vv_location_def, vv_operand_def,
       expr_val_rel_def, is_word_type_def] >> rpt strip_tac >> gvs[]
QED

Theorem field_mem_holds[local]:
  val_in_memory (StructTV fs) (StructV vals) (w2n w) t.vs_memory /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP vals fld = SOME fv /\ ALOOKUP fs fld = SOME ftv /\
  value_has_type ftv fv /\ read_result cx raw' ee = (INL fv,ee) /\
  eval_operand dst t = SOME dw /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  w2n dw = w2n w + struct_field_offset fields fld ==>
  vv_holds cenv cx ann raw' (LocatedValue ann (mk_ptr dst LocMemory)) ee t
Proof
  strip_tac >>
  `val_in_memory ftv fv (w2n dw) t.vs_memory` by
    (simp[] >> irule fields_in_memory_field >> simp[val_in_memory_def] >>
     goal_assum (drule_at Any) >> qexists_tac `vals` >>
     fs[val_in_memory_def]) >>
  simp[vv_holds_def, mk_ptr_def] >> strip_tac >>
  drule_all val_in_memory_word_type >> simp[]
QED

Theorem struct_slot_holds_live[local]:
  vv_holds cenv cx (StructT sid) raw bvv ee t /\
  vv_loc bvv = slot_loc tr /\ eval_operand (vv_operand bvv) t = SOME w /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  (~expr_has_effect obj ==> vv_storage_live H cx bvv ee t) ==>
  storage_holds cx tr (StructT sid) raw w ee t /\
  (~expr_has_effect obj ==> storage_read_live H tr (get_storage cx ee tr) w (StructTV fs))
Proof
  Cases_on `bvv` >> Cases_on `tr` >>
  simp[vv_loc_def, vv_location_def, vv_operand_def, slot_loc_def] >>
  simp[vv_holds_def, is_bytestring_type_def] >> rpt strip_tac >> gvs[]
QED

Theorem field_slot_holds[local]:
  storage_holds cx tr (StructT sid) raw w ee t /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\ ALOOKUP vals fld = SOME fv /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  eval_operand dst t = SOME (w + n2w off) ==>
  vv_holds cenv cx ann raw' (LocatedValue ann (mk_ptr dst (slot_loc tr))) ee t
Proof
  strip_tac >> fs[storage_holds_def] >>
  drule_all_then strip_assume_tac read_storage_slot_field >>
  drule_all_then assume_tac storage_range_agree_field >>
  drule_all_then assume_tac storage_field_slots_in_range >>
  Cases_on `tr` >> gvs[vv_holds_def, mk_ptr_def, slot_loc_def, storage_holds_def]
QED

Theorem noncode_value_base[local]:
  select_result cx ty raw (AttrSubscript fld) ee = (INL (Value v),ee) ==>
  ?sv. raw = Value sv
Proof
  Cases_on `raw` >> simp[select_result_def, raise_def] >> strip_tac >>
  drule extend_place_result_shape >> simp[]
QED

Theorem struct_own_mem[local]:
  vv_own cenv cx (StructT sid) sa sb ee raw bvv t /\ vv_loc bvv = LocMemory ==>
  vv_own cenv cx (StructT sid) sa sb ee raw
    (LocatedValue (StructT sid) (mk_ptr (vv_operand bvv) LocMemory)) t
Proof
  Cases_on `bvv` >> simp[vv_own_def, expr_val_own_def, mk_ptr_def,
    vv_operand_def, vv_loc_def, vv_location_def, is_word_type_def] >> metis_tac[]
QED

Theorem noncode_field_owned[local]:
  (!v. raw = Value v ==>
       vv_own cenv cx (StructT sid) sa sb ee raw bvv t /\
       vv_loc bvv = LocMemory) /\
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\ val_wf ftv fv /\
  eval_operand (vv_operand bvv) t = SOME w /\ eval_operand dst t = SOME dw /\
  (vv_loc bvv = LocMemory ==> w2n dw = w2n w + off) /\
  off + type_memory_size ftv <= type_memory_size_fields fs /\
  raw' = Value v /\ ~is_word_type ann /\ ~is_bytestring_type ann ==>
  vv_own cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
  vv_loc bvv = LocMemory
Proof
  rpt strip_tac >> gvs[] >>
  drule_then strip_assume_tac noncode_value_base >>
  first_x_assum (drule_then strip_assume_tac) >>
  drule_all_then assume_tac struct_own_mem >>
  simp[] >> irule vv_own_memory_slice >>
  goal_assum (drule_at Any) >> simp[] >>
  `val_footprint ftv fv <= type_memory_size ftv` by simp[val_footprint_le] >>
  qexists_tac `StructV vals` >> fs[] >>
  `val_footprint (StructTV fs) (StructV vals) = type_memory_size_fields fs` by
    simp[val_footprint_def, type_memory_size_def] >>
  simp[] >> decide_tac
QED

Theorem noncode_is_memory_or_slot[local]:
  vv_holds cenv cx ty raw bvv ee t /\ vv_loc bvv <> LocCode ==>
  vv_loc bvv = LocMemory \/ ?tr. vv_loc bvv = slot_loc tr
Proof
  Cases_on `bvv` >> simp[vv_loc_def, vv_location_def, vv_holds_def] >>
  rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[slot_loc_def] >> strip_tac
  >- (qexists_tac `F` >> simp[]) >> qexists_tac `T` >> simp[]
QED

Theorem noncode_memory_endpoint[local]:
  vv_loc bvv = LocMemory /\
  vv_holds cenv cx (StructT sid) raw bvv ee t /\
  ptr_vv_ok cx (StructT sid) raw bvv ee G tn s /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout fields fs /\ struct_has_type fs vals /\
  ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  val_wf ftv fv /\ value_has_type ftv fv /\
  type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
    type_memory_size ftv /\
  eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (struct_field_offset fields fld)) /\
  w2n (w + n2w (struct_field_offset fields fld)) = w2n w + struct_field_offset fields fld /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\ op_taint tn' dst = {} /\
  (!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. dst = Var y /\ FLOOKUP G' y = SOME (b,sz)) ==>
  (type_memory_size_fields fs = 0 \/
   w2n w + type_memory_size_fields fs <= t.vs_alloca_next) ==>
  vv_holds cenv cx ann raw' (LocatedValue ann (mk_ptr dst LocMemory)) ee t /\
  vv_store_bound cx ann ann ee raw' (LocatedValue ann (mk_ptr dst LocMemory)) t /\
  ptr_vv_ok cx ann raw' (LocatedValue ann (mk_ptr dst LocMemory)) ee G' tn' t /\
  ptr_buf_ok cenv (Attribute ann obj fld) dst G' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >>
  drule_all_then assume_tac struct_mem_holds >>
  conj_tac >- (drule_all field_mem_holds >> simp[]) >>
  conj_tac
  >- (drule_all_then assume_tac struct_field_offset_le >>
      drule_all field_mem_store_bound >> simp[]) >>
  drule_all attribute_memory_field_ptr >> simp[]
QED

Theorem noncode_slot_endpoint[local]:
  vv_loc bvv = slot_loc tr /\
  vv_holds cenv cx (StructT sid) raw bvv ee t /\
  (~expr_has_effect obj ==> vv_storage_live H cx bvv ee t) /\
  ptr_vv_ok cx (StructT sid) raw bvv ee G tn s /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  ALOOKUP fs fld = SOME ftv /\ fields_layout fields fs /\
  read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\ ALOOKUP vals fld = SOME fv /\
  eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst t = SOME (w + n2w (struct_field_offset_slots fields fld)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_transient = s.vs_transient /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ op_taint tn' dst = {} ==>
  vv_holds cenv cx ann raw' (LocatedValue ann (mk_ptr dst (slot_loc tr))) ee t /\
  (~expr_has_effect (Attribute ann obj fld) ==>
   vv_storage_live H cx (LocatedValue ann (mk_ptr dst (slot_loc tr))) ee t) /\
  vv_store_bound cx ann ann ee raw' (LocatedValue ann (mk_ptr dst (slot_loc tr))) t /\
  ptr_vv_ok cx ann raw' (LocatedValue ann (mk_ptr dst (slot_loc tr))) ee G' tn' t
Proof
  strip_tac >> drule_all_then strip_assume_tac struct_slot_holds_live >>
  drule_then strip_assume_tac struct_field_slot_exists >>
  drule_all_then assume_tac struct_field_offset_slots_eq >>
  gvs[] >> conj_tac >- (drule_all field_slot_holds >> simp[]) >>
  conj_tac
  >- (Cases_on `tr` >> gvs[slot_loc_def, mk_ptr_def] >> strip_tac >>
      irule storage_read_live_field >> qexistsl_tac [`fs`,`fld`] >> simp[]) >>
  conj_tac >- (Cases_on `tr` >> simp[vv_store_bound_def, mk_ptr_def, slot_loc_def]) >>
  qabbrev_tac `off = struct_field_offset_slots fields fld` >>
  `(vv_loc bvv = LocStorage \/ vv_loc bvv = LocTransient) /\
   0 < type_slot_size ftv ==> w2n (w + n2w off) = w2n w + off` by
    (strip_tac >> drule_all attribute_storage_field_address >> simp[]) >>
  `vv_loc bvv <> LocMemory /\ vv_loc bvv <> LocCode` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  `vv_loc bvv = LocCode ==> op_prov G' dst = NONE` by simp[] >>
  drule_all attribute_nonmemory_field_ptr >> simp[]
QED

Theorem attribute_noncode_field_endpoint_mods:
  vv_loc bvv <> LocCode /\
  vv_post_mods H ctx func cenv cx obj es sa sb s0 ee raw bvv t /\
  post_value_type cenv obj = StructT sid /\
  evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
  evaluate_type (get_tenv cx) ann = SOME ftv /\
  fields_layout (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fs /\
  struct_has_type fs vals /\ ALOOKUP fs fld = SOME ftv /\ ALOOKUP vals fld = SOME fv /\
  val_wf ftv fv /\ read_result cx raw ee = (INL (StructV vals),ee) /\
  read_result cx raw' ee = (INL fv,ee) /\
  select_result cx (StructT sid) raw (AttrSubscript fld) ee = (INL raw',ee) /\
  type_memory_bytes cenv (lowered_value_type cenv (Attribute ann obj fld)) =
    type_memory_size ftv /\
  eval_operand (vv_operand bvv) t = SOME w /\ eval_operand (vv_operand bvv) s = SOME w /\
  eval_operand dst t = SOME (w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)) /\
  vv_place_ptr_mods cenv cx ee t raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) /\
  vv_store_bound cx (StructT sid) (lowered_value_type cenv obj) ee raw bvv s /\
  ptr_vv_ok cx (StructT sid) raw bvv ee G tn s /\
  (!v. raw = Value v ==>
       vv_own cenv cx (StructT sid) sa sm ee raw bvv s /\ vv_loc bvv = LocMemory) /\
  sm.cs_next_id <= sb.cs_next_id /\ t.vs_allocas = s.vs_allocas /\
  (!n b sz. local_region cenv ee.scopes t n b sz ==> local_region cenv ee.scopes s n b sz) /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_memory = s.vs_memory /\
  t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\ t.vs_transient = s.vs_transient /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
  op_taint tn' dst = {} /\
  (!x b sz. vv_operand bvv = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
     ?y. dst = Var y /\ FLOOKUP G' y = SOME (b,sz)) ==>
  let vv = LocatedValue ann (mk_ptr dst (vv_loc bvv)) in
    vv_post_mods H ctx func cenv cx (Attribute ann obj fld) es sa sb s0 ee raw' vv t /\
    vv_store_bound cx (post_value_type cenv (Attribute ann obj fld))
      (lowered_value_type cenv (Attribute ann obj fld)) ee raw' vv t /\
    ptr_vv_ok cx (post_value_type cenv (Attribute ann obj fld)) raw' vv ee G' tn' t /\
    (!v. raw' = Value v /\ ~is_word_type (post_value_type cenv (Attribute ann obj fld)) /\
         ~is_bytestring_type (post_value_type cenv (Attribute ann obj fld)) ==>
       vv_own cenv cx (post_value_type cenv (Attribute ann obj fld)) sa sb ee raw' vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
    (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx raw' ee = (INL v,ee) /\
         !rt a. evaluate_type (get_tenv cx) (post_value_type cenv (Attribute ann obj fld)) = SOME rt /\
                eval_operand (vv_operand vv) t = SOME a ==>
                w2n a + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                       val_in_memory rt v (w2n a) mem)) /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Attribute ann obj fld)) ==>
             ptr_buf_ok cenv (Attribute ann obj fld) op G' t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
            ptr_buf_ok cenv (Attribute ann obj fld) p.ptr_operand G' t)
Proof
  strip_tac >> simp[LET_THM, expr_type_def, lowered_value_type_def,
                   vv_location_def, vv_operand_def, mk_ptr_def] >>
  qabbrev_tac `fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)` >>
  qabbrev_tac `off = struct_field_offset fields fld` >>
  qabbrev_tac `dw = w + n2w (attr_offset cenv (StructT sid) (vv_loc bvv) fld)` >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_assum `post_value_type _ _ = StructT _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  `vv_holds cenv cx (StructT sid) raw bvv ee t` by
    (drule_then (fn th => simp[GSYM th]) noncode_holds) >>
  drule_all_then assume_tac struct_field_offset_le >>
  `off + type_memory_size ftv <= type_memory_size_fields fs` by simp[Abbr `off`] >>
  `mem_step_offset (StructTV fs) (AttrSubscript fld) = SOME (off,ftv)` by
    simp[Abbr `off`, mem_step_offset_def, mem_field_offset_layout] >>
  `vv_loc bvv = LocMemory ==>
    (type_memory_size_fields fs = 0 \/ w2n w + type_memory_size_fields fs <= t.vs_alloca_next) /\
    w2n dw = w2n w + off` by
    (strip_tac >> drule_all_then assume_tac struct_mem_store_bound >>
     conj_tac >- simp[] >>
     drule stmt_state_rel_alloca_room >> strip_tac >>
     drule alloca_room_next_lt >> strip_tac >>
     simp[Abbr `dw`, Abbr `off`, Abbr `fields`, attr_offset_def] >>
     irule field_ptr_w2n >> qexistsl_tac [`type_memory_size ftv`,`type_memory_size_fields fs`] >>
     simp[] >> fs[Abbr `off`, Abbr `fields`] >> decide_tac) >>
  `vv_at cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t` by
    (irule noncode_at_field >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`raw`,`sid`,`vals`] >> simp[]) >>
  `!v. raw = Value v ==> vv_own cenv cx (StructT sid) sa sb ee raw bvv t /\
                         vv_loc bvv = LocMemory` by
    (rpt strip_tac >> gvs[] >> irule vv_own_vars_frame >>
     qexistsl_tac [`s`,`sm`] >> simp[]) >>
  `!v. raw' = Value v /\ ~is_word_type ann /\ ~is_bytestring_type ann ==>
       vv_own cenv cx ann sa sb ee raw' (LocatedValue ann (mk_ptr dst (vv_loc bvv))) t /\
       vv_loc bvv = LocMemory` by
    (`vv_loc bvv = LocMemory ==> w2n dw = w2n w + off` by simp[] >>
     gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     drule_all noncode_field_owned >> simp[]) >>
  drule_all_then strip_assume_tac noncode_is_memory_or_slot
  >- (`value_has_type ftv fv` by
        (drule_all_then strip_assume_tac vyperAssignPreservesTypeTheory.struct_field_has_type >> gvs[]) >>
      `w2n (w + n2w (struct_field_offset fields fld)) =
       w2n w + struct_field_offset fields fld` by
        fs[Abbr `fields`, Abbr `off`, Abbr `dw`, attr_offset_def] >>
      `eval_operand dst t = SOME (w + n2w (struct_field_offset fields fld))` by
        fs[Abbr `fields`, Abbr `dw`, attr_offset_def] >>
      `(type_memory_size_fields fs = 0 \/
        w2n w + type_memory_size_fields fs <= t.vs_alloca_next)` suffices_by
        (disch_tac >> drule_all_then strip_assume_tac noncode_memory_endpoint >>
         simp[vv_post_mods_def, vv_holds_mods_def, expr_type_def, mk_ptr_def] >>
         fs[mk_ptr_def] >>
         qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _` mp_tac >> simp[]) >>
      fs[]) >>
  gvs[Abbr `dw`, Abbr `fields`] >>
  `attr_offset cenv (StructT sid) (slot_loc tr) fld =
   struct_field_offset_slots (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` by
    (Cases_on `tr` >> simp[slot_loc_def, attr_offset_def]) >>
  `eval_operand dst t = SOME (w + n2w (struct_field_offset_slots
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by fs[] >>
  drule_all_then strip_assume_tac noncode_slot_endpoint >>
  `slot_loc tr <> LocMemory /\ slot_loc tr <> LocCode` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  `!v. raw' <> Value v` by
    (rpt strip_tac >>
     qpat_assum `raw' = Value v` (fn eq =>
       qpat_assum `select_result _ _ _ _ _ = _`
         (strip_assume_tac o MATCH_MP noncode_value_base o REWRITE_RULE [eq])) >> fs[]) >>
  simp[vv_post_mods_def, vv_holds_mods_def, expr_type_def, mk_ptr_def] >>
  fs[mk_ptr_def] >>
  qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz _.vs_memory = _` mp_tac >> simp[]
QED
