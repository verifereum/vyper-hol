(* Pure location boundaries for forcing, independent of the execution path. *)
Theory bodyIntCallWindowPosts
Ancestors
  loweringPosts context exprSimProps valueEncoding vyperInterpreter vyperState
  exprLoweringProps exprLowering exprSimCopy exprSimUnwrap loweringHalt
  compileEnv loweringStateRelDefs finite_map words valueCopy exprSimStorageCopy

Theorem vv_identity_location:
  read_result cx r es = (INL v,es) /\
  (case vv of StackValue _ _ => T
   | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  (vv_at ce cx ty sa sb es r vv s ==>
     expr_val_at ce cx ty sa sb es v (vv_operand vv) s) /\
  (vv_own ce cx ty sa sb es r vv s ==>
     expr_val_own ce cx ty sa sb es v (vv_operand vv) s)
Proof
  strip_tac >> Cases_on `vv` >>
  simp[vv_at_def, vv_own_def, vv_operand_def, expr_val_at_def, expr_val_own_def] >>
  gvs[] >> rpt strip_tac >> first_x_assum drule >> metis_tac[]
QED

Theorem allocated_value_location:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand op s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b+sz /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    b+sz <= lb \/ lb+len <= b) ==>
  expr_val_at ce cx ty sa sb es v op s /\
  expr_val_own ce cx ty sa sb es v op s
Proof
  strip_tac >> simp[expr_val_at_def, expr_val_own_def] >> metis_tac[]
QED

Theorem materialized_value_location:
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand op u = SOME w /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
  sa.cs_next_id < sb.cs_next_id /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    regions_disjoint (w2n w) (type_memory_size tv) b sz) /\
  (!name b sz. local_region ce es.scopes u name b sz <=>
                local_region ce es.scopes s name b sz) ==>
  !sv. sv.cs_next_id <= sa.cs_next_id ==>
    expr_val_at ce cx ty sv sb es v op u /\
    expr_val_own ce cx ty sv sb es v op u
Proof
  strip_tac >> gen_tac >> strip_tac >> irule allocated_value_location >>
  qexistsl_tac [`sa.cs_next_id`, `w2n w`, `type_memory_size tv`, `tv`, `w`] >>
  simp[] >> drule val_footprint_le >> fs[regions_disjoint_def] >> metis_tac[]
QED

Theorem unwrap_materialization_id:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  ~is_word_type ty /\ p.ptr_location <> LocMemory /\
  p.ptr_location <> LocCalldata ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> Cases_on `p.ptr_location = LocCode`
  >- (fs[unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
      pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
      gvs[] >> rename1 `compile_alloc_buffer _ sa = (buf,mid)` >>
      qmatch_goalsub_rename_tac `_ < final.cs_next_id` >>
      `ci_mono mid final` by metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND] >>
      drule compile_alloc_buffer_parts >> fs[ci_mono_def]) >>
  `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  qspec_then `p.ptr_location` mp_tac ensure_storage_memory_layout >>
  disch_then (qspecl_then [`p.ptr_operand`, `type_memory_bytes ce ty`,
    `(type_memory_bytes ce ty + 31) DIV 32`, `ce.ce_is_ctor`, `ce.ce_imm_alloca`]
    mp_tac) >> simp[] >> strip_tac >>
  fs[unwrap_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> fs[] >> pairarg_tac >> fs[] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qpat_assum `p.ptr_location = _` (fn th =>
    drule (SRULE [th, comp_ignore_bind_def]
      (Q.SPEC `p.ptr_location` storage_copy_suffix_ci_mono))) >>
  fs[ci_mono_def]
QED
