Theory bodyFullStoreSlotsTuple
Ancestors
  bodyFullStoreSlotsMembers bodyFullStoreSlotsTaintFold
  typedCopyLayoutPtr typedCopyDomain placeStoreSlots valueEncodingDefs
  valueEncodingTyping valueEncodingProofs vyperTypeValues vyperTypeDefaults
  vyperStorageRegionWrite compileEnv context

(* The recursive child contract stays explicit until rank assembly. *)
val tuple_child = ``
 !ty tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (TupleT tys) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts``;

Theorem compile_store_slots_tuple_origin_ptr_path:
 !cenv tenv tys. (^tuple_child) ==>
 !tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  is_abi_dynamic cenv.ce_struct_fields (TupleT tys) /\
  evaluate_type tenv (TupleT tys) = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst (TupleT tys) tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t ks Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw+n2w j)
         (mload (w2n sw+32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if tr then tnf.t_stor = tn.t_stor else tnf.t_trans = tn.t_trans) /\
    (if tr then tnf.t_trans else tnf.t_stor) SUBSET
      FOLDL (\X j. key_update X (dw+n2w j)
         (mem_word_taint tn.t_mem (w2n sw+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (mk_asm "child") >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV av)` >>
  Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `values_have_types tvs vs` >>
  `LENGTH vs = LENGTH tvs` by metis_tac[vyperTypingTheory.values_have_types_length] >>
  suspend "alignment"
QED

Resume compile_store_slots_tuple_origin_ptr_path[alignment]:
  markerLib.RESUME_TAC >>
  `LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
       type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (TupleT tys) /\
       evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
       IS_SOME (encode_value tv v))
       (MAP (\ty. (ty,type_memory_bytes cenv ty)) tys) (ZIP (tvs,vs))` by
    (gvs[values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >>
     simp[listTheory.LIST_REL_EL_EQN, listTheory.EL_MAP, listTheory.EL_ZIP] >>
     rpt strip_tac >> rename1 `idx < LENGTH tvs` >>
     `evaluate_type tenv (EL idx tys) = SOME (EL idx tvs)` by metis_tac[] >>
     `value_has_type (EL idx tvs) (EL idx vs)` by metis_tac[] >>
     rpt conj_tac
     >- (irule typedMemoryCopyTheory.typed_copy_memory_size >> qexists_tac `tenv` >> simp[] >> metis_tac[])
     >- (irule member_rank_lt_tuple >> simp[listTheory.EL_MEM])
     >> metis_tac[vyperTypingTheory.value_has_type_equiv]) >>
  suspend "members"
QED

Resume compile_store_slots_tuple_origin_ptr_path[members]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def,
       compileEnvTheory.is_bytestring_type_def] >> strip_tac >>
  mp_tac compile_store_slots_members_origin_ptr_path_conditional >>
  (impl_tac >- (rpt strip_tac >> irule store_slots_taint_fold_mono >> simp[])) >>
  disch_then (qspecl_then [`cenv`,`tenv`,`type_rank cenv.ce_struct_fields (TupleT tys)`] mp_tac) >>
  (impl_tac >- (asm_x "child" mp_tac >> rpt (pop_assum kall_tac) >>
    disch_then (mk_asm "child") >> rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >> asm "child" irule >>
    asm_rewrite_tac[] >> qexistsl [`dst`,`src`,`tv`,`ty`,`v`] >>
    simp[arithmeticTheory.ADD_COMM] >> metis_tac[])) >>
  disch_then (mk_asm "members") >> suspend "payload"
QED

Resume compile_store_slots_tuple_origin_ptr_path[payload]:
  markerLib.RESUME_TAC >>
  gnvs[valueEncodingDefsTheory.val_in_memory_def,
       valueEncodingTheory.type_memory_size_def,
       vyperValueTheory.type_slot_size_def] >>
  asm_x "members" (qspecl_then
    [`MAP (\ty. (ty,type_memory_bytes cenv ty)) tys`,`tvs`,`vs`,`0`,`0`,
     `src`,`dst`,`tr`,`sa`,`sb`,`func`,`s`,`sw`,`dw`,`tn`,`G`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_rewrite_tac[] >> simp[])) >>
  strip_tac >> qexistsl [`t`,`ks`,`Gf`,`tf`] >> asm_rewrite_tac[] >>
  simp_tac bool_ss [arithmeticTheory.ADD_COMM] >> asm_rewrite_tac[] >>
  qpat_x_assum `encode_value _ _ = SOME writes` mp_tac >>
  simp[vyperStorageTheory.encode_value_def] >> strip_tac >>
  drule_all store_slots_tuple_support >>
  simp[arithmeticTheory.ADD_COMM, SF CONJ_ss]
QED

Finalise compile_store_slots_tuple_origin_ptr_path
