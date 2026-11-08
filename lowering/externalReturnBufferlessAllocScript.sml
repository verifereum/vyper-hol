(* Allocated zero-layout normalization of the actual returned value. *)
Theory externalReturnBufferlessAlloc
Ancestors externalReturnIntcallMetadata externalReturnBufferlessNormalize externalReturnSiteSemantics
  externalReturnZeroWidening externalReturnCopyAlloc externalReturnCopyRecursive
  externalReturnCopyFrame exprSimAlloc localPtrsProps loweringSlice
  compileEnv context venomState fragExec runFromGasPath vyperTypeSystem exprLoweringProps

Theorem return_bufferless_site_zero_semantics:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env dst (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  (phy = NoneT \/ type_memory_bytes ce phy = 0) /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  evaluate_type (get_tenv cx) phy = SOME stv ==>
  ?atv dtv. evaluate_type (get_tenv cx) (expr_type e) = SOME atv /\
    evaluate_type (get_tenv cx) dst = SOME dtv /\
    type_widens_to (get_tenv cx) (expr_type e) dst /\
    type_memory_bytes ce phy = 0 /\
    type_memory_bytes ce (expr_type e) = 0 /\ type_memory_bytes ce dst = 0 /\
    type_memory_size stv = 0 /\ type_memory_size dtv = 0 /\
    val_wf dtv v /\ safe_cast dtv v = SOME v
Proof
  rpt strip_tac >> drule_all return_site_value_semantics >> strip_tac >>
  `type_memory_bytes ce phy = 0` by gvs[type_memory_bytes_def] >>
  `type_memory_bytes ce (expr_type e) = 0 /\
   type_memory_bytes ce dst = 0` by
    metis_tac[return_bufferless_widenings_zero_layout] >>
  `type_memory_size stv = 0` by metis_tac[return_copy_memory_size] >>
  `type_memory_size dtv = 0` by metis_tac[return_copy_memory_size] >>
  metis_tac[]
QED

Theorem return_zero_run_copy_frame[local]:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!a len. mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory ==>
  return_copy_frame sa b sz s t
Proof
  simp[return_copy_frame_def, return_copy_memory_frame_def]
QED

Theorem return_alloc_zero_value_run:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dst (Lit 0w) phy sm = ((),sb) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to (get_tenv cx) phy dst /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  evaluate_type (get_tenv cx) dst = SOME dtv /\
  type_memory_size stv = 0 /\ type_memory_size dtv = 0 /\ val_wf dtv v /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t w. stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory dtv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
    (!fuel r. run_from fuel ctx func t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx func s = r)
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sa x` by simp[] >>
  `type_memory_size dtv < dimword (:256)` by simp[] >>
  drule_all alloc_buffer_source_frag >>
  disch_then (qspec_then `\r. F` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def] >> disch_then drule_all >> strip_tac >> gvs[] >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[] >>
     qspecl_then [`type_memory_size dtv`,`sa`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[ci_mono_def]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by simp[] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sm x` by simp[] >>
  `!x. Var p = Var x ==> not_fresh_at sm x` by simp[] >>
  drule_all return_zero_typed_copy_value_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `return_copy_frame sm (w2n w) 0 u t` by
    (irule return_zero_run_copy_frame >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME w` by simp[] >>
  drule_all return_alloc_copy_post >> strip_tac >>
  qexistsl_tac [`t`,`w`] >> simp[] >> metis_tac[]
QED

Theorem return_bufferless_site_alloc_exit:
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env dst (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  (phy = NoneT \/ type_memory_bytes ce phy = 0) /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  compile_alloc_buffer (type_memory_bytes ce dst) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dst (Lit 0w) phy sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dtv t w. evaluate_type (get_tenv cx) dst = SOME dtv /\
    safe_cast dtv v = SOME v /\ stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory dtv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) ==>
    ?fuel r. run_from fuel ctx func t = r /\ exit_result r /\ R r) ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\ R r
Proof
  strip_tac >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields` by metis_tac[] >>
  (Q.SUBGOAL_THEN `(phy = NoneT \/ type_memory_bytes ce phy = 0)` assume_tac
    >- simp[]) >>
  drule_all return_bufferless_site_zero_semantics >> strip_tac >>
  `type_widens_to (get_tenv cx) phy dst` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_trans] >>
  fs[] >>
  `compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm)` by simp[] >>
  drule_all return_alloc_zero_value_run >> strip_tac >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0)` by
    (qpat_x_assum `FLOOKUP t.vs_allocas _ = _` mp_tac >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `!err. run_from fuel ctx func t <> Error err` by
    metis_tac[exit_result_not_error] >>
  qpat_x_assum `!fuel r. _` (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all run_from_gas_path >> metis_tac[]
QED

Theorem return_selected_bufferless_alloc_exit:
  set_external_package_target target
    (package_external_fn tops F nkey_map (mut,F,rr,fname,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ ce.ce_func_info name = (0,0,pvs) /\
  phy = ce.ce_func_return_type name /\
  expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env dst (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  type_widens_to (get_tenv cx) phy (expr_type e) /\
  evaluate_type (get_tenv cx) phy = SOME stv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname, fty, sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  compile_alloc_buffer (type_memory_bytes ce dst) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dst (Lit 0w) phy sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!dtv t w. evaluate_type (get_tenv cx) dst = SOME dtv /\
    safe_cast dtv v = SOME v /\ stmt_state_rel ctx func ce cx ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory dtv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) ==>
    ?fuel r. run_from fuel ctx func t = r /\ exit_result r /\ R r) ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\ R r
Proof
  strip_tac >> drule_all return_selected_bufferless >> disch_tac >>
  (Q.SUBGOAL_THEN `(phy = NoneT \/ type_memory_bytes ce phy = 0)` assume_tac
    >- metis_tac[]) >>
  drule_all return_bufferless_site_alloc_exit >> simp[]
QED
