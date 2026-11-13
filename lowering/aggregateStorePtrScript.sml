(* The public aggregate-store dispatch preserves the checked copy's frame. *)
Theory aggregateStorePtr
Ancestors aggregateCopyPtr memoryLayoutDefs memoryLayoutSource memoryLayoutRel memoryValueEncoding
  widenedAssignPtrCopyRecursive assignBasePtrCopyPath assignBasePtrBytesPost
  typedMemoryCopy typedCopyPtr valueCopy valueEncoding valueEncodingDefs
  valueEncodingProps context contextProps compileEnv bodyPtrDefs
  exprLoweringProps exprSimProps exprSimBufferStore fragGasPathPtr ptrDiscipline
  venomState venomExecSemantics
  venomInst emitHelper emitHelperProps words finite_map pred_set list arithmetic

Theorem compile_store_memory_aggregate_counted_ptr:
  !cenv tenv ctx D PG dty sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\ ~is_word_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v ==>
    !a b dst src dw sw fn G tn s.
      compile_store_memory cenv src (Var dst) dty sty a = ((),b) /\
      not_fresh_at a dst /\ (!x. src = Var x ==> not_fresh_at a x) /\
      lookup_var dst s = SOME dw /\ eval_operand src s = SOME sw /\
      op_taint tn (Var dst) = {} /\ op_taint tn src = {} /\
      (0 < type_memory_size dtv ==>
        ptr_covers G tn dst s (type_memory_size dtv)) /\
      (0 < type_memory_size stv ==>
        ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      (w2n dw + type_memory_size dtv <= w2n sw \/
       w2n sw + type_memory_size stv <= w2n dw) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n sw) m) /\
      fn_has_code a b fn /\ 
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      ?G' tn' t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
        (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n dw) m) /\
        typed_copy_state_frame a (w2n dw) (type_memory_size dtv) s t /\
        (!x. not_fresh_at a x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
        tn'.t_imm = tn.t_imm /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
          (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(dty = sty \/ tuple_memory_layout_eq dty sty) /\ ~is_bytestring_type dty`
  >- suspend "flat" >>
  `is_bytestring_type dty ==> is_bytestring_type sty` by
    metis_tac[typed_copy_bytestring_source] >>
  `compile_store_memory_typed cenv (Var dst) dty src sty a = ((),b)` by
    (Cases_on `is_bytestring_type dty`
     >- (gvs[compile_store_memory_def] >>
         once_rewrite_tac[compile_store_memory_typed_def] >> simp[]) >>
     gvs[compile_store_memory_def]) >>
  mp_tac (Q.SPECL [`cenv`,`tenv`,`ctx`,`D`,`PG`,`dty`,`sty`,`dtv`,`stv`,`v`]
    widened_assign_typed_store_counted_ptr) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`a`,`b`,`Var dst`,`src`,`dw`,`sw`,`fn`,`G`,`tn`,`s`] mp_tac) >>
  simp[eval_operand_def] >> disch_then irule >> simp[]
QED

Resume compile_store_memory_aggregate_counted_ptr[flat]:
  qpat_x_assum `(_ \/ _) /\ _` (map_every assume_tac o CONJUNCTS) >>
  `compile_copy_memory (Var dst) src (type_memory_size dtv) a = ((),b)` by
    gvs[compile_store_memory_def] >>
  `tuple_memory_layout_eq dty sty ==>
    memory_layout_key dty = memory_layout_key sty` by
    (Cases_on `dty` >> Cases_on `sty` >>
     simp[tuple_memory_layout_eq_def, memory_layout_key_tuple]) >>
  `memory_layout_key dty = memory_layout_key sty` by metis_tac[] >>
  `memory_layout_rel dtv stv` by metis_tac[memory_layout_key_evaluated] >>
  `type_memory_size dtv = type_memory_size stv` by
    gvs[memory_layout_rel_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory dtv v (w2n sw) m` by
    (rpt strip_tac >> irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists_tac `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  mp_tac (Q.SPECL [`dtv`,`v`,`type_memory_size dtv`,`a`,`b`,`dst`,`src`,
    `dw`,`sw`,`fn`,`G`,`tn`,`s`,`ctx`,`D`,`PG`]
      compile_copy_memory_counted_frame_ptr) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> disch_then ACCEPT_TAC
QED

Finalise compile_store_memory_aggregate_counted_ptr
