Theory bodyFullEmptyPost
Ancestors
  bodyPtrTypeBuiltinsEmptyMemoryPost exprSimBufferEmptyExec exprSimBuffer
  loweringPosts
  exprSimAggregateLayout exprSimMemDefs bodyMemAggregateBounds
  exprSimHyps exprSimProps valueEncodingProofs valueEncoding
  exprLowering compileEnv venomState ptrDiscipline finite_map pred_set context

Theorem empty_memory_full_post:
  !cenv cx env es typ rt sa sb buf func ctx s t p w G tn.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) typ = SOME rt /\ ~is_word_type typ /\
    compile_builtin_empty_complex (type_memory_bytes cenv typ)
      (is_bytestring_type typ \/ (case typ of ArrayT _ (Dynamic _) => T | _ => F))
      sa = (buf,sb) /\
    fn_has_code sa sb func /\ stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    type_memory_bytes cenv typ < dimword (:256) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
    ptr_covers G tn p t (type_memory_bytes cenv typ) /\
    (!i. w2n w <= i /\
      i < w2n w + (if is_bytestring_type typ \/
        (case typ of ArrayT _ (Dynamic _) => T | _ => F)
        then 32 else type_memory_bytes cenv typ) ==> i NOTIN tn.t_mem) ==>
    vv_post H ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s es
      (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t /\
    vv_store_bound cx typ typ es (Value (default_value rt))
      (LocatedValue typ (base_ptr buf)) t /\
    ptr_vv_ok cx typ (Value (default_value rt))
      (LocatedValue typ (base_ptr buf)) es G tn t /\
    ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) (Var p) G t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  gvs[eval_operand_def] >>
  `val_in_memory rt (default_value rt) (w2n w) t.vs_memory` by
    (irule empty_type_default_memory >> goal_assum (drule_at Any) >>
     qexistsl_tac [`cx`, `env`, `es`] >>
     gvs[eval_operand_def]) >>
  `type_memory_bytes cenv typ = type_memory_size rt` by
    metis_tac[expr_sim_inv_memory_size] >>
  `vv_post H ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s es
    (Value (default_value rt)) (LocatedValue typ (base_ptr buf)) t` by
    suspend "post" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "bound" >>
  `ptr_vv_ok cx typ (Value (default_value rt))
      (LocatedValue typ (base_ptr <|buf_operand := Var p;
        buf_size := type_memory_bytes cenv typ|>)) es G tn t /\
    ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) (Var p) G t` by
    (irule empty_memory_pointer_post >> goal_assum (drule_at Any) >>
     simp[] >>
     reverse conj_tac >- metis_tac[] >>
     Cases_on `is_bytestring_type typ \/
       (case typ of ArrayT _ (Dynamic _) => T | _ => F)` >> gvs[]) >>
  gvs[base_ptr_def, bodyPtrDefsTheory.ptr_vv_ok_def]
QED
Resume empty_memory_full_post[post]:
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.SPECL [`func`, `cenv`, `cx`, `TypeBuiltin typ Empty typ []`] buffer_memory_vv_post)) >>
  simp[post_value_type_def, lowered_value_type_def, vyperASTTheory.expr_type_def,
    val_wf_default_value_proof, base_ptr_def, eval_operand_def,
    val_footprint_le] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s n lb lsz` by
    (irule local_region_frame >> conj_tac
     >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
          loweringStateRelDefsTheory.state_rel_def] >>
     qexistsl_tac [`sa`, `es.scopes`, `t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s _ _ _ ==> _` drule >> simp[]
QED
Resume empty_memory_full_post[bound]:
  drule_all aggregate_alloca_capacity_mem >> strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`] vv_store_bound_capacity)) >>
  conj_tac
  >- (qexistsl_tac [`rt`, `w`] >> simp[base_ptr_def, eval_operand_def]) >>
  metis_tac[]
QED
Finalise empty_memory_full_post
