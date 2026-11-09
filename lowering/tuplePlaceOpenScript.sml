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
