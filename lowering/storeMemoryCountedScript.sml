(* Counted execution for the actual generic memory-store dispatch. *)
Theory storeMemoryCounted
Ancestors
  typedMemoryRankCounted memoryLayoutSource memoryLayoutRel memoryValueEncoding
  layoutStoreProps valueEncodingProps exprSimProps fragGasMode
  context compileEnv typedCopyAgreement typedCopyDomain vyperTypeSystem typedCopyCounted
  typedCopyAggregateCounted placeMemoryCopyEffect venomState memoryLayoutDefs fragGasPathMem

Theorem compile_store_memory_nonword_effect_mem:
  compile_store_memory cenv sp dp dt st a = ((),b) /\
  ~is_word_type dt /\ ~is_word_type st /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) /\
  fn_inst_ids_distinct func /\ type_widens_to tenv st dt /\
  evaluate_type tenv dt = SOME dtv /\ evaluate_type tenv st = SOME stv /\
  value_has_type dtv v /\ val_wf dtv v /\
  value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v (w2n sw) u.vs_memory /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (!x. dp = Var x ==> not_fresh_at a x) /\
  (!x. sp = Var x ==> not_fresh_at a x) /\
  eval_operand dp u = SOME dw /\ eval_operand sp u = SOME sw /\
  fn_has_code a b func /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts /\
  alloca_history func u /\ alloca_inv u /\
  w2n sw + type_memory_size stv <= u.vs_alloca_next /\
  w2n dw + type_memory_size dtv <= u.vs_alloca_next ==>
  ?t. val_in_memory dtv v (w2n dw) t.vs_memory /\
      typed_copy_effect ctx func a b u t (w2n dw) (type_memory_size dtv) /\
      gas_path_mem ctx func u 0 (OK t) /\ alloca_history func t
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `is_bytestring_type dt`
  >- (`is_bytestring_type st` by
        (gvs[type_widens_to_def] >> metis_tac[arg_type_fits_bytestring_source]) >>
      `compile_store_memory_typed cenv dp dt sp st a = ((),b)` by
        gvs[compile_store_memory_def, compile_store_memory_typed_bytes] >>
      irule typed_memory_rank_forward_counted >> simp[] >>
      goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
      qexistsl [`stv`,`sw`,`tenv`] >> simp[] >> metis_tac[]) >>
  Cases_on `dt <> st /\ ~tuple_memory_layout_eq dt st`
  >- (gvs[compile_store_memory_def] >>
      irule typed_memory_rank_forward_counted >> simp[] >>
      goal_assum (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
      qexistsl [`stv`,`sw`,`tenv`] >> simp[] >> metis_tac[]) >>
  suspend "bulk"
QED

Resume compile_store_memory_nonword_effect_mem[bulk]:
  markerLib.RESUME_TAC >>
  `dt = st \/ tuple_memory_layout_eq dt st` by metis_tac[] >>
  `type_memory_size dtv = type_memory_size stv` by
    metis_tac[tuple_memory_layout_eq_bytes] >>
  `memory_layout_key dt = memory_layout_key st` by
    metis_tac[bulk_store_layout_keys] >>
  `memory_layout_rel dtv stv` by metis_tac[memory_layout_key_evaluated] >>
  `val_in_memory dtv v (w2n sw) u.vs_memory` by
    (irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  `compile_copy_memory dp sp (type_memory_size dtv) a = ((),b)` by
    (gvs[compile_store_memory_def] >> metis_tac[]) >>
  `type_memory_size dtv < dimword (:256)` by decide_tac >>
  `val_footprint dtv v <= type_memory_size dtv` by
    metis_tac[val_footprint_le] >>
  `w2n sw + type_memory_size dtv <= u.vs_alloca_next` by decide_tac >>
  drule_at (Pat `compile_copy_memory _ _ _ _ = _`) copy_memory_window_path_length >>
  disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func u 0 (OK t)` by
    (simp[gas_marked_path_def] >> metis_tac[gas_path_mem_exec]) >>
  qexists `t` >> simp[typed_copy_effect_def] >>
  qpat_x_assum `(_ with <|vs_memory := _; vs_inst_idx := _|>) = _` mp_tac >>
  simp[venom_state_component_equality] >> rpt strip_tac >> simp[]
QED
Finalise compile_store_memory_nonword_effect_mem
