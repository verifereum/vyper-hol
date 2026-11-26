Theory bodyExtReturnDefaultBytesMods
Ancestors
  bodyFullExtCallDefaultBytesStore bodyPtrBopHashFootprint
  compileEnv typedMemoryCopy valueCopyBytes valueEncoding vfmConstants
  vyperTypeSystem fragGasOriginPtr venomState

Theorem extcall_default_bytes_payload:
  compile_store_memory cenv default_op (Var q) ret_type default_ty ds = ((),de) /\
  is_bytestring_type ret_type /\
  type_widens_to (get_tenv cx) default_ty ret_type /\
  evaluate_type (get_tenv cx) ret_type = SOME rtv /\
  evaluate_type (get_tenv cx) default_ty = SOME tv /\
  value_has_type rtv dv /\ value_has_type tv dv /\ val_wf tv dv /\
  type_memory_size rtv + 64 < dimword (:256) /\
  not_fresh_at ds q /\ (!x. default_op = Var x ==> not_fresh_at ds x) /\
  lookup_var q u = SOME dw /\ eval_operand default_op u = SOME w /\
  ptr_mem_ok cx default_ty dv default_op Gu tu u /\
  (type_memory_size tv <> 0 ==>
    (?x. default_op = Var x /\ ptr_covers Gu tu x u (type_memory_size tv)) /\
    w2n w + type_memory_size tv <= u.vs_alloca_next) /\
  ptr_covers Gu tu q u (type_memory_size rtv) /\
  w2n dw + type_memory_size rtv <= u.vs_alloca_next /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  fn_has_code ds de func /\ ~u.vs_halted /\
  u.vs_current_bb = ds.cs_current_bb /\ u.vs_inst_idx = LENGTH ds.cs_current_insts ==>
  ?p Gp tp.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK p,Gp,tp)) /\
    typed_copy_state_frame ds (w2n dw) (type_memory_size rtv) u p /\
    (!mem. mem_agree_outside tp.t_mem p.vs_memory mem ==>
      val_in_memory rtv dv (w2n dw) mem) /\
    (!x. not_fresh_at ds x ==>
      FLOOKUP Gp x = FLOOKUP Gu x /\ op_taint tp (Var x) = op_taint tu (Var x)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size rtv) ==>
      (i IN tp.t_mem <=> i IN tu.t_mem)) /\
    tp.t_stor = tu.t_stor /\ tp.t_trans = tu.t_trans /\ tp.t_imm = tu.t_imm /\
    ~p.vs_halted /\ p.vs_current_bb = de.cs_current_bb /\
    p.vs_inst_idx = LENGTH de.cs_current_insts
Proof
  strip_tac >>
  `is_bytestring_type default_ty` by
    metis_tac[type_widens_to_def,compileEnvTheory.arg_type_fits_bytestring_source] >>
  `type_memory_size tv <> 0` by
    (drule_all bytestring_type_value >> strip_tac >>
     gvs[type_memory_size_def,word_size_def]) >>
  `!mem. mem_agree_outside tu.t_mem u.vs_memory mem ==>
     val_in_memory tv dv (w2n w) mem` by
    (rpt strip_tac >> drule_all ptr_mem_ok_robust >> simp[]) >>
  qpat_x_assum `type_memory_size tv <> 0 ==> _`
    (drule_then strip_assume_tac) >>
  rename1 `default_op = Var src` >>
  `not_fresh_at ds src /\ lookup_var src u = SOME w` by
    fs[eval_operand_def] >>
  qpat_x_assum `default_op = Var src` SUBST_ALL_TAC >>
  drule_all extcall_default_bytes_store_capacity_joint >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`p`,`Gp`,`tp`] strip_assume_tac)) >>
  qexistsl_tac [`p`,`Gp`,`tp`] >> simp[] >>
  conj_tac
  >- (simp[typed_copy_state_frame_def,typed_copy_frame_def] >>
      conj_tac >- gvs[venom_state_component_equality] >>
      rpt strip_tac >> simp[]) >>
  qx_gen_tac `i` >> disch_tac >>
  `i < w2n dw \/ w2n dw + type_memory_size rtv <= i` by decide_tac >>
  qpat_assum `!i. i < w2n dw \/ _ ==> _` (qspec_then `i` mp_tac) >> simp[]
QED
