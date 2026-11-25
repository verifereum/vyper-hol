(* Physical payload cut for a widened default external return. *)
Theory bodyExtReturnDefaultWidenedMods
Ancestors
  extcallReturnDefaultControlJoint extcallReturnDefaultTypes
  exprSimExtCallCase bodyFullAllocaFresh stateRelProj
  abiCallerAllocation abiCallerLocalScratch exprSimWordArgs
  fragGasOriginPtr loweringPosts loweringStateRelDefs
  codegenRel compileEnv context venomState venomMemDefs finite_map words
  exprSafeOperand ptrDiscipline logStoreDataOriginPtr
  bodyFullExtCallDefaultCopy bodyFullExtCallDefaultBytesStore
  bodyPtrBopRepresentationFrame bodyPtrBopHashFootprint
  actualAllocExec exprSimIfExpWidenedCounted bodyFullExtCallPrecheck
  bodyFullUnwrapSlotPost exprSimHash extcallReturnInterface
  annassignRelayoutPost[qualified,ignore_grammar]
  aggregateEvaluatedLayout[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem extcall_default_widened_payload:
  compile_store_memory cenv (Var src) (Var q) ret_type default_ty ds = ((),de) /\
  ~is_word_type ret_type /\
  (is_bytestring_type ret_type ==> is_bytestring_type default_ty) /\
  type_memory_bytes cenv ret_type = type_memory_size rtv /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
       sz = type_memory_size tv) fields) /\
  type_widens_to tenv default_ty ret_type /\
  evaluate_type tenv default_ty = SOME tv /\
  evaluate_type tenv ret_type = SOME rtv /\
  value_has_type tv dv /\
  value_has_type rtv dv /\
  val_wf tv dv /\ val_wf rtv dv /\
  not_fresh_at ds src /\ not_fresh_at ds q /\
  lookup_var src u = SOME w /\ lookup_var q u = SOME dw /\
  (!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
         val_in_memory tv dv (w2n w) mem) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  w2n dw + type_memory_size rtv < dimword (:256) /\
  (type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= u.vs_alloca_next) /\
  (type_memory_size rtv = 0 \/ w2n dw + type_memory_size rtv <= u.vs_alloca_next) /\
  (w2n w + type_memory_size tv <= w2n dw \/
   w2n dw + type_memory_size rtv <= w2n w) /\
  ptr_covers Gu tu src u (type_memory_size tv) /\
  ptr_covers Gu tu q u (type_memory_size rtv) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code ds de func /\ fn_inst_ids_distinct func /\
  ~u.vs_halted /\ u.vs_current_bb = ds.cs_current_bb /\
  u.vs_inst_idx = LENGTH ds.cs_current_insts ==>
  ?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,Gu,tu) [] (OK p,Gp,tp)) /\
    val_in_memory rtv dv (w2n dw) p.vs_memory /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u p /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts /\
    tp.t_imm = tu.t_imm /\ tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
         (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
           val_in_memory rtv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
       FLOOKUP Gp x = FLOOKUP Gu x /\
       op_taint tp (Var x) = op_taint tu (Var x))
Proof
  strip_tac >>
  irule logStoreDataOriginPtrTheory.compile_store_memory_origin_ptr_path >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `type_memory_size rtv = 0 \/ _` ACCEPT_TAC) >>
  metis_tac[]
QED
