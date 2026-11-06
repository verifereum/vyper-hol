(* Selected struct fields preserve robust representation and dead-byte bounds. *)
Theory bodyPtrAttributeFields
Ancestors
  bodyPtrDefs exprSimFieldLayout accountsRelProps vyperStoragePlaceRegion
  compileEnv valueEncodingProps vyperState list arithmetic

(* The equivalence also supplies the converse embedding into the parent. *)
Theorem struct_field_dead_bytes_iff:
  !fs id off ftv st base j b.
    struct_field_slot fs id = SOME (off, ftv) /\
    base + off <= j /\ j < base + off + type_slot_size ftv ==>
    (dead_bytes st base (StructTV fs) j b <=>
     dead_bytes st (base + off) ftv j b)
Proof
  simp_tac bool_ss [Once dead_bytes_def] >>
  Induct_on `fs` >- simp[struct_field_slot_def] >>
  Cases >> rpt gen_tac >> rename1 `(fid, fty) :: fs` >>
  simp[struct_field_slot_def] >> Cases_on `fid = id`
  >- (rpt strip_tac >> gvs[Once dead_bytes_def] >>
      eq_tac >- (strip_tac >> simp[] >>
        drule (cj 3 dead_bytes_range) >> simp[]) >> simp[]) >>
  Cases_on `struct_field_slot fs id` >> simp[] >>
  rename1 `struct_field_slot fs id = SOME fsl` >> Cases_on `fsl` >>
  rename1 `struct_field_slot fs id = SOME (foff, fty')` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  qmatch_goalsub_rename_tac `dead_bytes_fields st addr ((fid, fty)::fs) j b` >>
  `addr + foff + type_slot_size fty = addr + type_slot_size fty + foff`
    by decide_tac >>
  `~dead_bytes st addr fty j b` by
    (strip_tac >> drule (cj 1 dead_bytes_range) >> simp[] >> decide_tac) >>
  simp[Once dead_bytes_def] >>
  qpat_x_assum `!id off ftv st base j b. _` drule >>
  disch_then (qspecl_then [`st`, `addr + type_slot_size fty`, `j`, `b`] mp_tac) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem struct_field_taint_bound:
  !fs id off ftv st base T.
    struct_field_slot fs id = SOME (off, ftv) /\
    (!j b. (j,b) IN T /\ base <= j /\
       j < base + type_slot_size (StructTV fs) /\ b < 32 ==>
       dead_bytes st base (StructTV fs) j b) ==>
    !j b. (j,b) IN T /\ base + off <= j /\
       j < base + off + type_slot_size ftv /\ b < 32 ==>
       dead_bytes st (base + off) ftv j b
Proof
  rpt gen_tac >> strip_tac >>
  drule struct_field_slot_end_bound >> strip_tac >>
  rpt strip_tac >>
  qmatch_goalsub_rename_tac `dead_bytes st (addr + off) ftv j b` >>
  `addr <= j /\ j < addr + type_slot_size (StructTV fs)` by decide_tac >>
  `dead_bytes st addr (StructTV fs) j b` by metis_tac[] >>
  drule struct_field_dead_bytes_iff >>
  disch_then (qspecl_then [`st`, `addr`, `j`, `b`] mp_tac) >> simp[]
QED

Theorem struct_field_robust_memory:
  !fields fs vals addr tainted mem id fv ftv.
    fields_layout fields fs /\ struct_has_type fs vals /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv /\
    (!m. mem_agree_outside tainted mem m ==>
      val_in_memory (StructTV fs) (StructV vals) addr m) ==>
    !m. mem_agree_outside tainted mem m ==>
      val_in_memory ftv fv (addr + struct_field_offset fields id) m
Proof
  rpt strip_tac >> irule fields_in_memory_field >>
  goal_assum (drule_at Any) >> simp[] >>
  first_x_assum drule >> simp[valueEncodingTheory.val_in_memory_def] >>
  strip_tac >> qexists_tac `vals` >> simp[]
QED

(* Buffer restriction does not need a positive value footprint.  In
   particular, a zero-sized trailing field is allowed. *)
Theorem ptr_buf_ok_offset:
  !cenv e field src dst G H s t w off.
    ptr_buf_ok cenv e src G s /\
    eval_operand src s = SOME w /\
    (!v. eval_operand dst t = SOME v ==> v = w + n2w off) /\
    off + type_memory_bytes cenv (lowered_value_type cenv field) <=
      type_memory_bytes cenv (lowered_value_type cenv e) /\
    w2n (w + n2w off) = w2n w + off /\
    (!x b sz. src = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
      ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
    ptr_buf_ok cenv field dst H t
Proof
  rpt gen_tac >> strip_tac >> simp[ptr_buf_ok_def] >> rpt strip_tac >>
  `type_memory_bytes cenv (lowered_value_type cenv e) <> 0` by decide_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_buf_ok_def] >>
  disch_then (qspec_then `w` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  `w' = w + n2w off` by metis_tac[] >> gvs[] >> decide_tac
QED

Theorem ptr_mem_ok_of_buffer:
  !cx cenv e ty v op G tn s tv.
    evaluate_type (get_tenv cx) ty = SOME tv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
    val_wf tv v /\ ptr_buf_ok cenv e op G s /\
    (!w mem. eval_operand op s = SOME w /\
       mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory tv v (w2n w) mem) ==>
    ptr_mem_ok cx ty v op G tn s
Proof
  rpt gen_tac >> strip_tac >> simp[ptr_mem_ok_def] >> rpt strip_tac >>
  gvs[] >>
  drule exprSimPropsTheory.val_store_size_le >> strip_tac >>
  `val_footprint tv v <= val_store_size tv v` by
    simp[exprSimPropsTheory.val_footprint_le_store_size] >>
  `type_memory_size tv <> 0` by decide_tac >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_buf_ok_def] >> disch_then drule >>
  simp[] >> strip_tac >> goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem struct_ptr_mem_ok_field_buffer:
  !cx cenv e ty vals fs src dst G H tn s t w off.
    ptr_mem_ok cx ty (StructV vals) src G tn s /\
    evaluate_type (get_tenv cx) ty = SOME (StructTV fs) /\
    eval_operand src s = SOME w /\
    (!u. eval_operand dst t = SOME u ==> u = w + n2w off) /\
    off + type_memory_bytes cenv (lowered_value_type cenv e) <=
      type_memory_size (StructTV fs) /\
    w2n (w + n2w off) = w2n w + off /\
    (!x b sz. src = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
      ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
    ptr_buf_ok cenv e dst H t
Proof
  rpt gen_tac >> strip_tac >> simp[ptr_buf_ok_def] >> rpt strip_tac >>
  `type_memory_size (StructTV fs) <> 0` by decide_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ptr_mem_ok_def] >>
  disch_then (qspecl_then [`StructTV fs`, `w`] mp_tac) >>
  simp[loweringPostsTheory.val_footprint_def,
       exprSimPropsTheory.val_store_size_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Theorem struct_ptr_mem_ok_field:
  !cx cenv e ty fty vals fs fields id fv ftv src dst G H tn tn' s t w.
    ptr_mem_ok cx ty (StructV vals) src G tn s /\
    evaluate_type (get_tenv cx) ty = SOME (StructTV fs) /\
    eval_operand src s = SOME w /\
    (!u. eval_operand dst t = SOME u ==>
      u = w + n2w (struct_field_offset fields id)) /\
    fields_layout fields fs /\ struct_has_type fs vals /\
    ALOOKUP vals id = SOME fv /\ ALOOKUP fs id = SOME ftv /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size ftv /\
    val_wf ftv fv /\ t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    w2n (w + n2w (struct_field_offset fields id)) =
      w2n w + struct_field_offset fields id /\
    (!x b sz. src = Var x /\ FLOOKUP G x = SOME (b,sz) ==>
      ?y. dst = Var y /\ FLOOKUP H y = SOME (b,sz)) ==>
    ptr_mem_ok cx fty fv dst H tn' t
Proof
  rpt gen_tac >> strip_tac >>
  `struct_field_offset fields id +
     type_memory_bytes cenv (lowered_value_type cenv e) <=
     type_memory_size (StructTV fs)` by
    (drule_all struct_field_offset_le >> simp[valueEncodingTheory.type_memory_size_def]) >>
  `ptr_buf_ok cenv e dst H t` by
    (drule_all struct_ptr_mem_ok_field_buffer >> simp[]) >>
  irule ptr_mem_ok_of_buffer >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (StructTV fs) (StructV vals) (w2n w) mem` by
    (qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[ptr_mem_ok_def] >>
     disch_then (qspecl_then [`StructTV fs`, `w`] mp_tac) >> simp[]) >>
  drule_all struct_field_robust_memory >> simp[]
QED

Theorem ptr_vv_ok_memory:
  !cx ty tv lowty p es G tn s v.
    p.ptr_location = LocMemory /\ op_taint tn p.ptr_operand = {} /\
    read_result cx tv es = (INL v, es) /\
    ptr_mem_ok cx ty v p.ptr_operand G tn s ==>
    ptr_vv_ok cx ty tv (LocatedValue lowty p) es G tn s
Proof
  rpt strip_tac >> simp[ptr_vv_ok_def] >> metis_tac[]
QED

Theorem ptr_vv_ok_nonmemory:
  !cx ty tv lowty p es G tn s ftv.
    p.ptr_location <> LocMemory /\ op_taint tn p.ptr_operand = {} /\
    evaluate_type (get_tenv cx) ty = SOME ftv /\
    (!w k b. eval_operand p.ptr_operand s = SOME w /\
      w2n w <= w2n k /\ w2n k < w2n w + type_slot_size ftv /\ b < 32 ==>
      (p.ptr_location = LocStorage /\ (k,b) IN tn.t_stor ==>
        dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage
          (w2n w) ftv (w2n k) b) /\
      (p.ptr_location = LocTransient /\ (k,b) IN tn.t_trans ==>
        dead_bytes (s.vs_transient s.vs_call_ctx.cc_address)
          (w2n w) ftv (w2n k) b)) ==>
    ptr_vv_ok cx ty tv (LocatedValue lowty p) es G tn s
Proof
  rpt strip_tac >> simp[ptr_vv_ok_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED
