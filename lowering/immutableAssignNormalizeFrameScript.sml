(* Allocation plus typed normalization, with the old-allocation frame exposed. *)
Theory immutableAssignNormalizeFrame
Ancestors
  immutableDeployNormalize placeStoreAllocPath placeStoreDynPrepare
  placeTypedCopyRecursivePath exprSimBufferStore exprLoweringProps compileEnv
  typedMemoryCopy venomState stmtSimDefs fragGasMode fragExec venomInst
  exprSimAlloc valueEncodingProps finite_map loweringHalt

Theorem immutable_assign_normalize_prefix:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields tenv /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  stmt_state_rel ctx func ce cx es s /\
  eval_operand src s = SOME sw /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  type_memory_size dtv < dimword (:256) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r pw. gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func ce cx es r /\
    val_in_memory dtv v (w2n pw) r.vs_memory /\
    eval_operand buf.buf_operand r = SOME pw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n pw,type_memory_size dtv) /\
    w2n pw + type_memory_size dtv < dimword (:256) /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP r.vs_allocas aid = SOME entry) /\
    alloca_frame ce es sa s ce es r
Proof
  strip_tac >>
  `cs_extends sa mid` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends mid sm` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa mid func /\ fn_has_code mid sm func` by
    metis_tac[fn_has_code_split] >>
  drule_all place_alloc_buffer_source_path >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `w2n sw + type_memory_size stv <= w2n w \/
   w2n w + type_memory_size dtv <= w2n sw` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ u` kall_tac >>
     irule place_alloca_source_disjoint >> simp[] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
     qexistsl_tac [
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`,
       `STRING #"%" (toString sa.cs_next_var)`, `raw`] >>
     gvs[run_inst_seq_def, mk_inst_def, venomExecSemanticsTheory.step_inst_base_def,
         eval_operands_def, eval_operand_def, lookup_var_def, AllCaseEqs()] >>
     rpt strip_tac >>
     qpat_x_assum `!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = _ ==> _` drule >> simp[]) >>
  qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
  qpat_x_assum `u = raw with vs_inst_idx := _` kall_tac >>
  `!x. src = Var x ==> not_fresh_at mid x` by metis_tac[] >>
  `val_in_memory stv v (w2n sw) u.vs_memory` by simp[] >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (qspec_then `tenv` mp_tac) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ u.vs_memory`)) >>
  disch_then (drule_at (Pat `fn_has_code mid sm _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `eval_operand buf.buf_operand u = _`)) >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `local_ptrs_reserved ce mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule place_typed_copy_alloca_state_frame >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
     qexistsl_tac [`type_memory_size dtv`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size dtv))]
         [STRING #"%" (toString sa.cs_next_var)]`] >>
     simp[mk_inst_def] >> rpt conj_tac >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >>
     qpat_x_assum `!name b len. _` (qspecl_then [`name`,`b`,`sz`] mp_tac) >>
     simp[]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (irule (gas_marked_path_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     qexists_tac `u` >> simp[gas_marked_path_def]) >>
  `eval_operand buf.buf_operand t = SOME w` by
    (drule typed_copy_state_frame_operand >>
     disch_then (qspec_then `buf.buf_operand` mp_tac) >> simp[]) >>
  `t.vs_allocas = u.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def,
          venom_state_component_equality]) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o SRULE [typed_copy_state_frame_def]) >>
     `not_fresh_at mid x` by simp[] >>
     qpat_x_assum `!x. not_fresh_at mid x ==> _` drule >> simp[]) >>
  `alloca_frame ce es sa s ce es t` by
    (irule alloca_frame_of_mem_frame >>
     simp[] >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `regions_disjoint (w2n w) (type_memory_size dtv) off sz` by
       (qpat_x_assum `!aid b len. _` (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
     qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
     simp[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def] >>
     metis_tac[]) >>
  qexistsl_tac [`t`,`w`] >> simp[] >> metis_tac[]
QED
