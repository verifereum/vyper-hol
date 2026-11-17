Theory bodyFullStoreSlotsPath
Ancestors
  bodyFullStoreSlotsBase bodyFullStoreSlotsDArray bodyFullStoreSlotsSArray
  bodyFullStoreSlotsTuple bodyFullStoreSlotsStruct typedCopyDomain

(* The sole recursive join: endpoint and ghosts precede every horizon. *)
val slots_path = ``
 !tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
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
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
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

Theorem compile_store_slots_rank_origin_ptr_path:
 !rank cenv tenv ty.
  type_rank cenv.ce_struct_fields ty = rank ==> ^slots_path
Proof
  completeInduct_on `rank` >> pop_assum (mk_asm "ih") >>
  rpt gen_tac >> disch_tac >>
  `!ty. type_rank cenv.ce_struct_fields ty < rank ==> ^slots_path` by
    (gen_tac >> disch_tac >>
     asm "ih" (qspec_then `type_rank cenv.ce_struct_fields ty'` mp_tac) >>
     asm_rewrite_tac[] >>
     disch_then (qspecl_then [`cenv`,`tenv`,`ty'`] mp_tac) >> simp[]) >>
  pop_assum (mk_asm "child") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `~is_abi_dynamic cenv.ce_struct_fields ty \/ is_bytestring_type ty`
  >- (match_mp_tac (Q.SPECL [`cenv`,`tenv`,`ty`] compile_store_slots_base_origin_ptr_path) >>
      asm_rewrite_tac[] >> qexistsl [`tv`,`v`,`src`,`dst`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `~(_ \/ _)` (strip_assume_tac o REWRITE_RULE [boolTheory.DE_MORGAN_THM]) >>
  Cases_on `ty`
  >- (Cases_on `b` >>
      fs[compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def] >>
      rename1 `BytesT len` >> Cases_on `len` >>
      fs[compileEnvTheory.is_abi_dynamic_def, compileEnvTheory.is_bytestring_type_def]) >>
  TRY (rename1 `ArrayT elem len` >> suspend "array" >> NO_TAC) >>
  TRY (rename1 `TupleT tys` >> suspend "tuple" >> NO_TAC) >>
  TRY (rename1 `StructT nsid` >> suspend "struct" >> NO_TAC) >>
  qpat_x_assum `is_abi_dynamic _ _` mp_tac >>
  simp[Once compileEnvTheory.is_abi_dynamic_def]
QED

Resume compile_store_slots_rank_origin_ptr_path[array]:
  markerLib.RESUME_TAC >> Cases_on `len`
  >- suspend "sarray" >> suspend "darray"
QED

Resume compile_store_slots_rank_origin_ptr_path[sarray]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`elem`,`n`] compile_store_slots_sarray_origin_ptr_path) >>
  (impl_tac >- (
    asm_x "child" mp_tac >>
    qpat_x_assum `type_rank _ _ = rank` mp_tac >>
    rpt (pop_assum kall_tac) >> disch_then (fn th => rewrite_tac[GSYM th]) >>
    pure_rewrite_tac[GSYM boolTheory.AND_IMP_INTRO] >>
    disch_tac >> rpt gen_tac >> disch_tac >>
    first_x_assum drule >>
    disch_then (MATCH_ACCEPT_TAC o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]))) >>
  disch_then irule >> asm_rewrite_tac[] >>
  qexistsl [`dst`,`src`,`tv`,`v`] >> asm_rewrite_tac[]
QED

Resume compile_store_slots_rank_origin_ptr_path[darray]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`elem`,`n`] compile_store_slots_dynarray_origin_ptr_path) >>
  (impl_tac >- (
    asm_x "child" mp_tac >>
    qpat_x_assum `type_rank _ _ = rank` mp_tac >>
    rpt (pop_assum kall_tac) >> disch_then (fn th => rewrite_tac[GSYM th]) >>
    pure_rewrite_tac[GSYM boolTheory.AND_IMP_INTRO] >>
    disch_tac >> rpt gen_tac >> disch_tac >>
    first_x_assum drule >>
    disch_then (MATCH_ACCEPT_TAC o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]))) >>
  disch_then irule >> asm_rewrite_tac[] >>
  qexistsl [`dst`,`src`,`tv`,`v`] >> asm_rewrite_tac[]
QED
Resume compile_store_slots_rank_origin_ptr_path[tuple]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`tys`] compile_store_slots_tuple_origin_ptr_path) >>
  (impl_tac >- (
    asm_x "child" mp_tac >>
    qpat_x_assum `type_rank _ _ = rank` mp_tac >>
    rpt (pop_assum kall_tac) >> disch_then (fn th => rewrite_tac[GSYM th]) >>
    pure_rewrite_tac[GSYM boolTheory.AND_IMP_INTRO] >>
    disch_tac >> rpt gen_tac >> disch_tac >>
    first_x_assum drule >>
    disch_then (MATCH_ACCEPT_TAC o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]))) >>
  disch_then irule >> asm_rewrite_tac[] >>
  qexistsl [`dst`,`src`,`tv`,`v`] >> asm_rewrite_tac[]
QED
Resume compile_store_slots_rank_origin_ptr_path[struct]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`nsid`] compile_store_slots_struct_origin_ptr_path) >>
  (impl_tac >- (
    asm_x "child" mp_tac >>
    qpat_x_assum `type_rank _ _ = rank` mp_tac >>
    rpt (pop_assum kall_tac) >> disch_then (fn th => rewrite_tac[GSYM th]) >>
    pure_rewrite_tac[GSYM boolTheory.AND_IMP_INTRO] >>
    disch_tac >> rpt gen_tac >> disch_tac >>
    first_x_assum drule >>
    disch_then (MATCH_ACCEPT_TAC o REWRITE_RULE [GSYM boolTheory.AND_IMP_INTRO]))) >>
  disch_then irule >> asm_rewrite_tac[] >>
  qexistsl [`dst`,`src`,`tv`,`v`] >> asm_rewrite_tac[]
QED
Finalise compile_store_slots_rank_origin_ptr_path

Theorem compile_store_slots_origin_ptr_path:
 !cenv tenv ty. ^slots_path
Proof
  ntac 3 gen_tac >>
  qspec_then `type_rank cenv.ce_struct_fields ty` mp_tac
    compile_store_slots_rank_origin_ptr_path >>
  disch_then (qspecl_then [`cenv`,`tenv`,`ty`] mp_tac) >> simp[]
QED
