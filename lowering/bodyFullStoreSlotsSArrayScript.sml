Theory bodyFullStoreSlotsSArray
Ancestors
  bodyFullStoreSlotsElements bodyFullStoreSlotsAddresses bodyFullStoreSlotsTaintFold
  typedCopyLayoutPtr placeStoreSlots

(* The recursive child contract stays explicit until rank assembly. *)
val sarray_child = ``
 !ty tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  type_rank cenv.ce_struct_fields ty < type_rank cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
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

Theorem compile_store_slots_sarray_origin_ptr_path:
 !cenv tenv elem n. (^sarray_child) ==>
 !tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  is_abi_dynamic cenv.ce_struct_fields (ArrayT elem (Fixed n)) /\
  evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst (ArrayT elem (Fixed n)) tr sa = ((),sb) /\
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
  `n < dimword (:256)` by metis_tac[store_slots_fixed_count_bound] >>
  qpat_x_assum `evaluate_type tenv (ArrayT elem (Fixed n)) = SOME tv` mp_tac >>
  simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `evaluate_type tenv elem = SOME etv` >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `value_has_type (ArrayTV etv (Fixed n)) (ArrayV av)` >>
  Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `sparse_has_type etv n sparse` >>
  `type_memory_bytes cenv elem = type_memory_size etv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def,
       compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def] >>
  strip_tac >>
  mp_tac compile_copy_elements_to_slots_origin_ptr_path_conditional >>
  (impl_tac >- (rpt (pop_assum kall_tac) >> conj_tac
    >- (rpt gen_tac >> strip_tac >>
        drule_all store_slots_addresses_origin_ptr_path >> simp[]) >>
    rpt gen_tac >> strip_tac >> irule store_slots_taint_fold_mono >> simp[])) >>
  disch_then (qspecl_then [`cenv`,`tenv`,`elem`,`etv`] mp_tac) >>
  (impl_tac >- (rpt gen_tac >> strip_tac >>
    asm "child" (qspec_then `elem` irule) >>
    simp[typedCopyDomainTheory.type_rank_def] >> metis_tac[])) >>
  disch_then (mk_asm "elements") >> suspend "payload"
QED

Resume compile_store_slots_sarray_origin_ptr_path[payload]:
  markerLib.RESUME_TAC >>
  `!i. i < n ==> value_has_type etv
     (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)` by
    (rpt strip_tac >> Cases_on `ALOOKUP sparse i` >>
     simp[vyperTypingTheory.default_value_well_typed] >>
     metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
  `!i. i < n ==> value_has_type etv
     (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v) /\
     IS_SOME (encode_value etv
       (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)) /\
     !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory etv
         (case ALOOKUP sparse i of NONE => default_value etv | SOME v => v)
         (w2n sw+i*type_memory_size etv) mem` by
    (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[vyperTypingTheory.value_has_type_equiv] >>
     rpt strip_tac >> irule sarray_in_memory_robust_element >>
     qexistsl_tac [`n`,`sparse`,`s.vs_memory`,`tn`] >> simp[]) >>
  asm_x "elements" (qspecl_then
    [`\i. case ALOOKUP sparse i of NONE => default_value etv | SOME v => v`,
     `n`,`src`,`dst`,`Lit (n2w n)`,`tr`,`sa`,`sb`,`func`,`s`,`sw`,`dw`,
     `tn`,`G`,`ctx`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >>
    gvs[valueEncodingTheory.type_memory_size_def, vyperValueTheory.type_slot_size_def,
        venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
        ptrDisciplineTheory.op_prov_def] >> metis_tac[])) >>
  strip_tac >> qexistsl_tac [`t`,`ks`,`Gf`,`tnf`] >>
  simp_tac bool_ss [arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac[] >>
  `value_has_type (ArrayTV etv (Fixed n)) (ArrayV (SArrayV sparse))` by
    simp[vyperTypingTheory.value_has_type_def] >>
  drule_all store_slots_sarray_support >> simp[]
QED

Finalise compile_store_slots_sarray_origin_ptr_path
