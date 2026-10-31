(*
 * Layout of struct, tuple and array literals (#636)
 *
 * Under expr_body_pre, StructLit and MakeArray compile to an ALLOCA of the
 * literal's size followed by compile_struct_lit, compile_make_tuple or
 * compile_make_array, and the evaluated types and field sizes add up to
 * that size (expr_sim_inv's struct fields clause gives the sizes).  For
 * empty(T): the buffer size, and when a zeroed buffer holds the default.
 *
 * TOP-LEVEL:
 *   struct_literal_decl_types, struct_literal_layout_types — a well-typed
 *     struct literal matches the declared fields and ce_struct_fields
 *   compile_struct_literal_inv, compile_tuple_literal_inv,
 *   compile_array_literal_inv — the compiled literal's shape
 *   struct_literal_evaluated_layout, make_tuple_evaluated_layout,
 *   make_array_evaluated_layout — evaluated types and buffer size
 *   compile_struct_lit_as_tuple — compile_struct_lit is compile_make_tuple
 *     on the field values
 *   expr_sim_inv_memory_size — type_memory_bytes = type_memory_size under
 *     expr_sim_inv
 *   empty_type_buffer_size, empty_type_default_memory — empty(T)
 *
 * Helpers: struct_layout_*, type_memory_size_aligned, and the per-case
 *   compile_* lemmas behind the _inv ones.
 *)
Theory exprSimAggregateLayout
Ancestors
  structFieldsProps vyperTypeSystem valueEncoding compileEnv
  exprSimHyps exprSimBufferEmpty vyperValue list pair finite_map vfmConstants
  exprCallbackContracts exprLowering exprSimWordBuiltins

Theorem struct_literal_decl_types:
  well_typed_expr env (StructLit ann nsid kes) ==>
  ann = StructT nsid /\
  ?args. FLOOKUP env.type_defs nsid = SOME (StructArgs args) /\
         MAP FST kes = MAP FST args /\
         MAP (expr_type o SND) kes = MAP SND args
Proof
  simp[well_typed_expr_def] >> metis_tac[]
QED

Theorem struct_literal_layout_types:
  well_typed_expr env (StructLit ann nsid kes) /\
  sfields_tenv_consistent cenv.ce_struct_fields env.type_defs ==>
  ann = StructT nsid /\
  ?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string nsid) = SOME fields /\
           MAP FST fields = MAP FST kes /\
           MAP (FST o SND) fields = MAP (expr_type o SND) kes
Proof
  strip_tac >> drule struct_literal_decl_types >> strip_tac >>
  gvs[sfields_tenv_consistent_def] >> metis_tac[]
QED

Theorem struct_layout_size_list:
  !fields tvs.
    OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs /\
    EVERY (\(name, ty, sz). !tv. evaluate_type tenv ty = SOME tv ==>
                                  sz = type_memory_size tv) fields ==>
    SUM (MAP (SND o SND) fields) = type_memory_size_list tvs
Proof
  Induct >> simp[type_memory_size_def] >>
  Cases >> rename1 `(name, info)` >> Cases_on `info` >>
  simp[type_memory_size_def] >> rpt strip_tac >> gvs[type_memory_size_def]
QED

Theorem struct_layout_size_zip:
  !names tvs. LENGTH names = LENGTH tvs ==>
    type_memory_size_fields (ZIP (names, tvs)) = type_memory_size_list tvs
Proof
  Induct >> Cases_on `tvs` >> simp[type_memory_size_def]
QED

Theorem expr_sim_inv_memory_size:
  !cenv ty cx env es tv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv
Proof
  ho_match_mp_tac type_memory_bytes_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          type_memory_bytes_def, type_memory_size_def] >>
      `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
        gvs[expr_sim_inv_def] >>
      `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
        EVERY (\(fname, fty, sz). !tv.
          evaluate_type (get_tenv cx) fty = SOME tv ==>
          sz = type_memory_size tv) fields` by
        (fs[expr_sim_inv_def] >> metis_tac[]) >>
      qpat_x_assum `sfields_tenv_consistent _ _` mp_tac >>
      simp[sfields_tenv_consistent_def] >> strip_tac >>
      qpat_x_assum `!nsid args. _` drule >> strip_tac >>
      gvs[get_struct_fields_def, evaluate_types_OPT_MMAP] >>
      `LENGTH tvs = LENGTH (MAP FST args)` by
        (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
      simp[struct_layout_size_zip] >>
      irule struct_layout_size_list >>
      qexists_tac `get_tenv cx \\ nsid` >> conj_tac >- gvs[] >>
      qpat_x_assum `!name fields. _ ==> EVERY _ _` drule >>
      simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
      drule (cj 1 vyperTypeExprSoundnessTheory.evaluate_type_mono) >>
      metis_tac[])
  >~ [`TupleT tys`]
  >- (rpt strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          type_memory_bytes_def, type_memory_size_def, evaluate_types_OPT_MMAP] >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> irule tuple_memory_bytes_size >>
      qexists_tac `get_tenv cx` >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      type_memory_bytes_def, type_memory_size_def, word_size_def] >>
  metis_tac[]
QED


Theorem type_memory_size_aligned:
  (!tv. type_memory_size tv MOD 32 = 0) /\
  (!tvs. type_memory_size_list tvs MOD 32 = 0) /\
  (!fields. type_memory_size_fields fields MOD 32 = 0)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def] >> rpt strip_tac >>
  once_rewrite_tac[GSYM arithmeticTheory.MOD_PLUS,
                   GSYM arithmeticTheory.MOD_TIMES2] >> simp[]
QED

Theorem struct_layout_lookup:
  !fields kes i tenv tv.
    MAP FST fields = MAP FST kes /\
    MAP (FST o SND) fields = MAP (expr_type o SND) kes /\
    ALL_DISTINCT (MAP FST fields) /\ i < LENGTH kes /\
    EVERY (\(name,ty,sz). !tv. evaluate_type tenv ty = SOME tv ==>
                              sz = type_memory_size tv) fields /\
    evaluate_type tenv (expr_type (SND (EL i kes))) = SOME tv ==>
    ?sz. ALOOKUP fields (FST (EL i kes)) =
           SOME (expr_type (SND (EL i kes)),sz) /\
         sz = type_memory_size tv
Proof
  rpt strip_tac >>
  `LENGTH fields = LENGTH kes` by metis_tac[LENGTH_MAP] >>
  `i < LENGTH fields` by simp[] >>
  `FST (EL i fields) = FST (EL i kes)` by metis_tac[EL_MAP] >>
  `FST (SND (EL i fields)) = expr_type (SND (EL i kes))` by
    (fs[LIST_EQ_REWRITE, EL_MAP] >> metis_tac[]) >>
  drule_all alistTheory.ALOOKUP_ALL_DISTINCT_EL >>
  strip_tac >>
  qexists_tac `SND (SND (EL i fields))` >>
  conj_tac >- metis_tac[PAIR] >>
  fs[EVERY_EL] >>
  qpat_x_assum `!n. n < LENGTH kes ==> _`
    (qspec_then `i` mp_tac) >>
  Cases_on `EL i fields` >> rename1 `(name, info)` >>
  Cases_on `info` >> gvs[] >> metis_tac[]
QED

Theorem compile_struct_lit_as_tuple:
  !fields off.
    EVERY (\(name,e).
      ALOOKUP (get_struct_fields ce.ce_struct_fields
        (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields ==>
    compile_struct_lit cfn ce ty fields buf off =
    compile_make_tuple cfn ce (MAP SND fields) buf off
Proof
  Induct >> simp[exprLoweringTheory.compile_struct_lit_def,
                 exprLoweringTheory.compile_make_tuple_def] >>
  qx_gen_tac `fld` >> PairCases_on `fld` >> rpt strip_tac >>
  gvs[exprLoweringTheory.compile_struct_lit_def,
      exprLoweringTheory.compile_make_tuple_def]
QED

Theorem struct_literal_lookup_types:
  expr_body_pre ce cx env (StructLit ann nsid kes) es ==>
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) kes
Proof
  strip_tac >>
  drule expr_body_pre_var_types_well_formed >> strip_tac >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (StructLit ann nsid kes)` by
    fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_body_pre_def, expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    gvs[expr_sim_inv_def] >>
  drule_all struct_literal_layout_types >> strip_tac >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(name,ty,sz). !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
       sz = type_memory_size tv) fields` by
    (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `EVERY (well_typed_expr env o SND) kes` by
    (`!ks. vyperTypeSystem$well_typed_named_exprs env ks ==>
        EVERY (well_typed_expr env o SND) ks` by
       (Induct >> simp[vyperTypeSystemTheory.well_typed_expr_def,
                      FORALL_PROD]) >>
     fs[vyperTypeSystemTheory.well_typed_expr_def]) >>
  simp[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
  `well_typed_expr env (SND (EL i kes))` by fs[EVERY_EL] >>
  drule_all exprSafeOperandTheory.well_typed_expr_type_well_formed >>
  simp[vyperTypeSystemTheory.well_formed_type_def] >> strip_tac >>
  Cases_on `evaluate_type (get_tenv cx) (expr_type (SND (EL i kes)))` >>
  gvs[] >>
  `ALL_DISTINCT (MAP FST fields)` by metis_tac[] >>
  drule_all struct_layout_lookup >> strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  Cases_on `EL i kes` >> gvs[get_struct_fields_def]
QED

Theorem empty_type_buffer_size:
  !cenv cx env es ty tv.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (if is_bytestring_type ty \/
        (case ty of ArrayT _ (Dynamic _) => T | _ => F)
     then 32 <= type_memory_bytes cenv ty
     else type_memory_bytes cenv ty MOD 32 = 0)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  IF_CASES_TAC
  >- (Cases_on `ty` >>
      gvs[is_bytestring_type_def, AllCaseEqs(),
          vyperValueTheory.evaluate_type_def, type_memory_size_def]
      >~ [`ArrayTV tv' bd`] >- (Cases_on `bd` >> gvs[type_memory_size_def]) >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def, AllCaseEqs(),
          vyperValueTheory.evaluate_type_def, type_memory_size_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def,
          type_memory_size_def]) >>
  simp[type_memory_size_aligned]
QED

Theorem empty_type_default_memory:
  !cenv cx env es ty tv off mem.
    expr_sim_inv cenv cx env es /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    (if is_bytestring_type ty \/
        (case ty of ArrayT _ (Dynamic _) => T | _ => F)
     then mem_word_at off mem = 0w
     else mem_bytes_at off (type_memory_bytes cenv ty) mem =
            REPLICATE (type_memory_bytes cenv ty) 0w) ==>
    val_in_memory tv (default_value tv) off mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  Cases_on `is_bytestring_type ty \/
    (case ty of ArrayT _ (Dynamic _) => T | _ => F)`
  >- (Cases_on `ty` >>
      gvs[is_bytestring_type_def, AllCaseEqs(),
          vyperValueTheory.evaluate_type_def]
      >~ [`ArrayTV tv' bd`]
      >- (Cases_on `bd` >> gvs[default_memory_header]) >>
      simp[default_memory_header] >>
      rename1 `BaseT bt` >> Cases_on `bt` >>
      gvs[is_bytestring_type_def, AllCaseEqs(),
          vyperValueTheory.evaluate_type_def] >>
      simp[default_memory_header] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
      simp[default_memory_header]) >>
  gvs[] >> irule default_memory_zero_bytes >> simp[]
QED

Theorem struct_child_compile:
  !ann nsid fields ce buf sa.
    compile_struct_lit
      (expr_child_callback (expr_size (StructLit ann nsid fields)) compile_expr)
      ce (StructT nsid) fields buf 0 sa =
    compile_struct_lit compile_expr ce (StructT nsid) fields buf 0 sa
Proof
  rpt gen_tac >> AP_THM_TAC >>
  MATCH_ACCEPT_TAC compile_struct_lit_child_calls
QED

Theorem compile_struct_literal:
  !ce ty ann nsid fields sa.
    compile_expr ce ty (StructLit ann nsid fields) sa =
    let (ba,sm) = compile_alloc_buffer
      (SUM (MAP (SND o SND)
        (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa in
    let (u,sb) = compile_struct_lit compile_expr ce (StructT nsid)
                  fields ba.buf_operand 0 sm in
    (LocatedValue (expr_type (StructLit ann nsid fields)) (base_ptr ba),sb)
Proof
  rpt gen_tac >> pure_once_rewrite_tac[compile_expr_def] >>
  simp_tac (srw_ss()) [compile_expr_body_def, struct_child_compile, LET_THM]
QED

Theorem compile_struct_literal_inv:
  !ce ty ann nsid fields sa vv sb.
    compile_expr ce ty (StructLit ann nsid fields) sa = (vv,sb) ==>
    ?ba sm u.
      compile_alloc_buffer
        (SUM (MAP (SND o SND)
          (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa = (ba,sm) /\
      compile_struct_lit compile_expr ce (StructT nsid) fields ba.buf_operand 0 sm = (u,sb) /\
      vv = LocatedValue (expr_type (StructLit ann nsid fields)) (base_ptr ba)
Proof
  rpt gen_tac >>
  Cases_on `compile_alloc_buffer
    (SUM (MAP (SND o SND)
      (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)))) sa` >>
  rename1 `compile_alloc_buffer _ sa = (ba,sm)` >>
  Cases_on `compile_struct_lit compile_expr ce (StructT nsid) fields ba.buf_operand 0 sm` >>
  simp[compile_struct_literal] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem evaluated_struct_layout:
  evaluate_type tenv (StructT nsid) = SOME tv ==>
  ?args tvs. FLOOKUP tenv nsid = SOME (StructArgs args) /\
    OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
    tv = StructTV (ZIP (MAP FST args,tvs))
Proof
  simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule (cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono) >>
  simp[evaluate_types_OPT_MMAP] >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem struct_literal_evaluated_layout:
  expr_body_pre ce cx env (StructLit ann nsid fields) es ==>
  ?tvs.
    OPT_MMAP (evaluate_type (get_tenv cx))
      (MAP expr_type (MAP SND fields)) = SOME tvs /\
    type_memory_size_list tvs =
      SUM (MAP (SND o SND) (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
    evaluate_type (get_tenv cx) (StructT nsid) =
      SOME (StructTV (ZIP (MAP FST fields,tvs)))
Proof
  strip_tac >>
  `well_typed_expr env (StructLit ann nsid fields) /\
   expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule struct_literal_decl_types >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?tv. evaluate_type (get_tenv cx) (StructT nsid) = SOME tv` by
    (gvs[vyperTypeSystemTheory.well_typed_expr_def,
         vyperTypeSystemTheory.well_formed_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) (StructT nsid)` >> gvs[]) >>
  drule evaluated_struct_layout >> strip_tac >>
  gvs[GSYM MAP_COMPOSE] >>
  drule_all expr_sim_inv_memory_size >>
  `LENGTH tvs = LENGTH (MAP FST args)` by
    (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  simp[type_memory_bytes_def, type_memory_size_def, struct_layout_size_zip,
       GSYM MAP_COMPOSE]
QED

Theorem make_tuple_evaluated_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray NONE bnd) args) es ==>
  ?tvs. ann = TupleT (MAP expr_type args) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
    evaluate_type (get_tenv cx) ann = SOME (TupleTV tvs) /\
    SUM (MAP (type_memory_bytes ce o expr_type) args) = type_memory_size_list tvs
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (Builtin ann (MakeArray NONE bnd) args)` by
    gvs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def,
      vyperTypeSystemTheory.well_formed_type_def,
      vyperValueTheory.evaluate_type_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  Cases_on `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args)` >> gvs[] >>
  simp[GSYM MAP_COMPOSE] >>
  irule tuple_memory_bytes_size >> goal_assum (drule_at Any) >>
  metis_tac[expr_sim_inv_memory_size]
QED

Theorem make_array_evaluated_layout:
  expr_body_pre ce cx env (Builtin ann (MakeArray (SOME et) bnd) args) es ==>
  ?tv. ann = ArrayT et bnd /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) ann = SOME (ArrayTV tv bnd) /\
    EVERY (\e. expr_type e = et) args /\
    type_memory_bytes ce et = type_memory_size tv /\
    (if (case bnd of Dynamic _ => T | _ => F) then 32 else 0) +
      LENGTH args * type_memory_size tv <= type_memory_bytes ce ann
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\
   well_typed_expr env (Builtin ann (MakeArray (SOME et) bnd) args)` by
    gvs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[vyperTypeSystemTheory.well_typed_expr_def,
      vyperTypeSystemTheory.well_typed_builtin_app_def,
      vyperTypeSystemTheory.well_formed_type_def, EVERY_MAP] >>
  Cases_on `evaluate_type (get_tenv cx) et` >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  `type_memory_bytes ce et = type_memory_size x` by
    metis_tac[expr_sim_inv_memory_size] >>
  conj_tac >- gvs[EVERY_MEM] >>
  Cases_on `bnd` >>
  gvs[vyperValueTheory.compatible_bound_def, type_memory_bytes_def] >>
  simp[]
QED

Theorem tuple_child_compile:
  compile_make_tuple (expr_child_callback (list_size expr_size args) compile_expr)
    ce args buf off sa = compile_make_tuple compile_expr ce args buf off sa
Proof
  AP_THM_TAC >> MATCH_ACCEPT_TAC compile_make_tuple_list_child_calls
QED

Theorem array_child_compile:
  compile_make_array (expr_child_callback (list_size expr_size args) compile_expr)
    ce args et sz lw buf sa = compile_make_array compile_expr ce args et sz lw buf sa
Proof
  AP_THM_TAC >> MATCH_ACCEPT_TAC compile_make_array_list_child_calls
QED

Theorem make_array_not_names[local]:
  !args topt bnd. ~names_builtin (MakeArray topt bnd) args
Proof
  Cases >> simp[names_builtin_def] >>
  rename1 `h::rest` >> Cases_on `h` >> simp[names_builtin_def] >>
  Cases_on `rest` >> simp[names_builtin_def] >>
  rename1 `Name _ _ :: h :: rest` >> Cases_on `h` >> simp[names_builtin_def] >>
  Cases_on `rest` >> simp[names_builtin_def] >>
  rename1 `Name _ _ :: Name _ _ :: h :: rest` >>
  Cases_on `h` >> simp[names_builtin_def] >>
  Cases_on `rest` >> simp[names_builtin_def]
QED

Theorem compile_tuple_literal:
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa =
  let (ba,sm) = compile_alloc_buffer
    (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa in
  as_ptr_val ann LocMemory (compile_make_tuple compile_expr ce args ba.buf_operand 0 sm)
Proof
  simp_tac (srw_ss() ++ boolSimps.ETA_ss) [make_array_not_names, compile_expr_builtin_dispatch,
    cj 2 compile_expr_raw_def,
    compile_builtin_dispatch_body_def, tuple_child_compile, LET_THM]
QED

Theorem compile_array_literal:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa =
  let (ba,sm) = compile_alloc_buffer (type_memory_bytes ce ann) sa in
  as_ptr_val ann LocMemory (compile_make_array compile_expr ce args et
    (type_memory_bytes ce et) (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm)
Proof
  simp_tac (srw_ss() ++ boolSimps.ETA_ss) [make_array_not_names, compile_expr_builtin_dispatch,
    cj 2 compile_expr_raw_def,
    compile_builtin_dispatch_body_def, array_child_compile, LET_THM]
QED

Theorem compile_tuple_literal_inv:
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) args) sa = (vv,sb) ==>
  ?ba sm u.
    compile_alloc_buffer (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa = (ba,sm) /\
    compile_make_tuple compile_expr ce args ba.buf_operand 0 sm = (u,sb) /\
    vv = LocatedValue ann (mk_ptr u LocMemory)
Proof
  Cases_on `compile_alloc_buffer (SUM (MAP (type_memory_bytes ce o expr_type) args)) sa` >>
  rename1 `compile_alloc_buffer _ sa = (ba,sm)` >>
  Cases_on `compile_make_tuple compile_expr ce args ba.buf_operand 0 sm` >>
  simp[compile_tuple_literal, as_ptr_val_def] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem compile_array_literal_inv:
  compile_expr ce ty (Builtin ann (MakeArray (SOME et) bnd) args) sa = (vv,sb) ==>
  ?ba sm u.
    compile_alloc_buffer (type_memory_bytes ce ann) sa = (ba,sm) /\
    compile_make_array compile_expr ce args et (type_memory_bytes ce et)
      (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm = (u,sb) /\
    vv = LocatedValue ann (mk_ptr u LocMemory)
Proof
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ann) sa` >>
  rename1 `compile_alloc_buffer _ sa = (ba,sm)` >>
  Cases_on `compile_make_array compile_expr ce args et (type_memory_bytes ce et)
    (case bnd of Dynamic _ => T | _ => F) ba.buf_operand sm` >>
  simp[compile_array_literal, as_ptr_val_def] >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED
