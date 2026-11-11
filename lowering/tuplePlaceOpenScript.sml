Theory tuplePlaceOpen
Ancestors
  stmtLowering exprLowering exprSimHypsDefs exprOpenCopies
  exprOpenPrimitives exprOpenTerminals aggregateEvaluatedLayout
  vyperTypeEnv compileEnv context venomInst loweringPosts

Theorem tuple_place_name_descriptor:
  expr_sim_inv cenv cx env es /\
  type_place_target env (NameTarget id) = SOME (Type ty) /\
  compile_get_target_ptr compile_expr cenv (NameTarget id) sa = (r,sb) ==>
  sb = sa /\ SND (SND r) = SOME (ValPT ty) /\
  FST (SND r) = SOME LocMemory
Proof
  simp[vyperTypeEnvTheory.type_place_target_NameTarget] >> strip_tac >>
  `cenv.ce_var_type id = SOME ty /\
   ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_inv_def] >>
  gvs[compile_get_target_ptr_def, comp_return_def]
QED

Theorem tuple_place_memory_assign_open_probe:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  ~block_is_terminated sa /\
  compile_assign_value cenv dst LocMemory src F NONE dty sty info bytes sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  simp[compile_assign_value_def] >> strip_tac >>
  metis_tac[compile_store_memory_open]
QED

Theorem tuple_place_word_fit_probe:
  arg_type_fits sty dty /\ is_word_type sty ==> is_word_type dty
Proof
  metis_tac[arg_type_fits_word_type]
QED

Theorem tuple_place_load_open_probe:
  !tys cenv src off sa vals sb.
    compile_tuple_load_all cenv src tys off sa = (vals,sb) /\
    (tys <> [] \/ ~block_is_terminated sa) ==>
    ~block_is_terminated sb
Proof
  Induct >> simp[compile_tuple_load_all_def, comp_return_def] >>
  rpt gen_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  gvs[] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> strip_tac >>
  Cases_on `is_word_type h` >>
  gvs[compile_load_memory_def, comp_return_def] >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Theorem tuple_place_success_descriptor_probe:
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type dty) r s ==>
  SND (SND r) = SOME (ValPT dty) /\
  ?loc. FST (SND r) = SOME loc /\
    (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient)
Proof
  strip_tac >>
  conj_tac >- fs[target_post_def, value_type_place_def] >>
  Cases_on `p` >> fs[target_post_def, place_ptr_rel_def] >>
  Cases_on `b` >> fs[slot_loc_def]
QED

Theorem tuple_place_target_ptr_open:
  !bt cfn cenv sa r sb.
    ~block_is_terminated sa /\
    compile_get_target_ptr cfn cenv bt sa = (r,sb) ==>
    ~block_is_terminated sb
Proof
  Cases >> rpt gen_tac
  >- (simp[compile_get_target_ptr_def] >>
      rpt CASE_TAC >> simp[comp_return_def] >> metis_tac[])
  >- (simp[compile_get_target_ptr_def] >>
      rpt CASE_TAC >> simp[comp_return_def] >> metis_tac[])
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume tuple_place_target_ptr_open[subscript]:
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `SND (SND result)`
  >- (simp[comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[compile_array_subscript_open]) >>
  Cases_on `x` >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  metis_tac[compile_mapping_subscript_open, compile_array_subscript_open]
QED

Resume tuple_place_target_ptr_open[attribute]:
  simp[compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule emit_op_nonterminator_open >> simp[is_terminator_def]
QED

Finalise tuple_place_target_ptr_open

Theorem tuple_place_dynarray_store_open[local]:
  !src dst ew em tr sa u sb.
    compile_dynarray_to_storage src dst ew em tr sa = (u,sb) ==>
    ~block_is_terminated sb
Proof
  rpt gen_tac >>
  simp[compile_dynarray_to_storage_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `ew = 1` >> simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  Cases_on `tr` >> strip_tac >> gvs[] >>
  drule emit_void_terminated >> simp[is_terminator_def]
QED

Theorem tuple_place_bulk_storage_open[local]:
  (!src dst n sa u sb. compile_memory_to_storage src dst n sa = (u,sb) ==>
    ~block_is_terminated sb) /\
  (!src dst n sa u sb. compile_memory_to_transient src dst n sa = (u,sb) ==>
    ~block_is_terminated sb)
Proof
  simp[compile_memory_to_storage_def, compile_memory_to_transient_def] >>
  metis_tac[compile_word_copy_loop_open]
QED

Theorem tuple_place_assign_value_open:
  acyclic_struct_metadata cenv.ce_struct_fields /\ ~block_is_terminated sa /\
  (loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient) /\
  compile_assign_value cenv dst loc src prim NONE dty sty arr bytes sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> gvs[]
  >- suspend "memory"
  >- suspend "storage"
  >> suspend "transient"
QED

Resume tuple_place_assign_value_open[memory]:
  Cases_on `prim` >> gvs[compile_assign_value_def]
  >- (drule emit_void_terminated >> simp[is_terminator_def]) >>
  metis_tac[compile_store_memory_open]
QED

Resume tuple_place_assign_value_open[storage]:
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `prim`
  >- (strip_tac >> gvs[] >> drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `arr` >> simp[]
  >- (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[emit_void_terminated, is_terminator_def, tuple_place_bulk_storage_open]) >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  metis_tac[tuple_place_dynarray_store_open]
QED

Resume tuple_place_assign_value_open[transient]:
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_assign_value_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >>
  Cases_on `prim`
  >- (strip_tac >> gvs[] >> drule emit_void_terminated >> simp[is_terminator_def]) >>
  Cases_on `arr` >> simp[]
  >- (IF_CASES_TAC >> simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      metis_tac[emit_void_terminated, is_terminator_def, tuple_place_bulk_storage_open]) >>
  PairCases_on `x` >> simp[] >> strip_tac >>
  metis_tac[tuple_place_dynarray_store_open]
QED

Finalise tuple_place_assign_value_open

Theorem tuple_place_success_store_open:
  target_post ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type dty) r t /\
  arg_type_fits sty dty /\ ~block_is_terminated sp /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  (let dst = FST r; loc_opt = FST (SND r); dst_ty_opt = SND (SND r);
       loc = case loc_opt of SOME l => l | NONE => LocMemory;
       dt = case dst_ty_opt of SOME (ValPT ty) => ty | _ => sty;
       arr = case dt of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
         | _ => NONE
   in (if is_word_type sty then
         if is_word_type dt then
           compile_store_at_loc cenv.ce_imm_alloca dst src loc_opt
         else emit_void INVALID []
       else compile_assign_value cenv dst loc src (is_word_type dt)
         NONE dt sty arr (type_memory_bytes cenv dt)) sa) = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >> drule tuple_place_success_descriptor_probe >> strip_tac >>
  `~block_is_terminated sa` by metis_tac[tuple_place_target_ptr_open] >>
  (Cases_on `is_word_type sty`
   >- (`is_word_type dty` by metis_tac[arg_type_fits_word_type] >>
       gvs[compile_store_at_loc_def] >>
       drule emit_void_terminated >> simp[is_terminator_def]) >>
   gvs[] >> irule tuple_place_assign_value_open >> metis_tac[])
QED
