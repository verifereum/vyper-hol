Theory bodyPtrIntCallArgumentLayout
Ancestors
  bodyPtrIntCallMargin entryStateRel entryArgPtrs vyperTypeBindArguments
  exprSimHyps compileVyper compileEnv finite_map list words structFieldsProps
  constSubst

Theorem intcall_build_argument_slots:
  ALL_DISTINCT (MAP FST args) /\ MEM (arg,ty) args /\
  FLOOKUP (build_compile_env tops vis mut (name:string) args ret ss locks).ce_vars
    arg = SOME (MemLoc off sz) ==>
  sz = type_memory_bytes (build_compile_env tops vis mut name args ret ss locks) ty
Proof
  strip_tac >>
  ` (build_compile_env tops vis mut (name:string) args ret ss locks).ce_vars =
    FST (allocate_args (get_struct_fields (make_struct_fields_map tops))
      args 0 FEMPTY)` by
    (simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])) >>
  drule allocate_args_lookup >>
  disch_then (qspecl_then
    [`get_struct_fields (make_struct_fields_map tops)`, `0`, `FEMPTY`] mp_tac) >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >>
  simp[GSYM type_mem_bytes_type_memory_bytes, build_compile_env_ce_struct_fields] >>
  strip_tac >> gvs[]
QED

Theorem intcall_internal_argument_size_bound:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  MEM (arg,ty) args ==>
  MAX 32 (type_memory_bytes ce ty) < dimword (:256)
Proof
  strip_tac >> drule_all body_inv_internal_subst_allocs_ok >>
  simp[fn_allocs_ok_def, subst_consts_fn_def, EVERY_MEM] >> strip_tac >>
  `ce.ce_struct_fields =
   (build_compile_env tops Internal mut name args ret
      (subst_consts_stmts (module_consts_env tops []) ss) F).ce_struct_fields` by
    gvs[bodySimTheory.body_inv_def, build_compile_env_ce_struct_fields] >>
  drule type_memory_bytes_frame >> strip_tac >>
  `type_memory_bytes ce ty < 2 ** 64` by
    (qpat_x_assum `!e. MEM e args ==> _` (qspec_then `(arg,ty)` mp_tac) >>
     simp[]) >>
  gvs[dimword_def] >> decide_tac
QED

Theorem intcall_bound_argument_layout:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx tenv es /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ALL_DISTINCT (MAP FST args) /\
  bind_arguments (get_tenv cx) args vs = SOME penv /\
  i < LENGTH args /\
  FLOOKUP penv (FST (EL i args)) = SOME entry /\
  FLOOKUP (build_compile_env tops Internal mut name args ret ss F).ce_vars
    (FST (EL i args)) = SOME (MemLoc off sz) ==>
  evaluate_type (get_tenv cx) (SND (EL i args)) = SOME entry.type /\
  type_memory_size entry.type = sz /\
  sz = type_memory_bytes ce (SND (EL i args)) /\
  sz <= MAX 32 (type_memory_bytes ce (SND (EL i args))) /\
  MAX 32 (type_memory_bytes ce (SND (EL i args))) < dimword (:256)
Proof
  strip_tac >> drule_all bind_arguments_lookup_index >> strip_tac >> gvs[] >>
  `MEM (EL i args) args` by simp[EL_MEM] >>
  `?a ty. EL i args = (a,ty)` by metis_tac[pairTheory.pair_CASES] >> gvs[] >>
  drule_all intcall_build_argument_slots >> strip_tac >>
  `ce.ce_struct_fields =
   (build_compile_env tops Internal mut name args ret ss F).ce_struct_fields` by
    gvs[bodySimTheory.body_inv_def, build_compile_env_ce_struct_fields] >>
  drule type_memory_bytes_frame >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `MAX 32 (type_memory_bytes ce ty) < dimword (:256)` by
    metis_tac[intcall_internal_argument_size_bound] >>
  gvs[] >> simp[]
QED

(* The name-lookup form is the footprint obligation at PARAM capture. *)
Theorem intcall_bound_argument_footprint:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx tenv es /\
  MEM (FunctionDecl Internal mut nr rr name args dflts ret ss) tops /\
  ALL_DISTINCT (MAP FST args) /\
  bind_arguments (get_tenv cx) args vs = SOME penv /\
  FLOOKUP penv arg = SOME entry /\
  FLOOKUP (build_compile_env tops Internal mut name args ret ss F).ce_vars
    arg = SOME (MemLoc off sz) ==>
  val_footprint entry.type entry.value <= sz
Proof
  strip_tac >>
  drule_all bind_arguments_scope_lookup >> strip_tac >> gvs[] >>
  `?i. i < LENGTH args /\ EL i args = (arg,typ)` by metis_tac[MEM_EL] >>
  `type_memory_size entry.type = sz` by
    (mp_tac intcall_bound_argument_layout >> simp[]) >>
  drule bind_arguments_scope_well_typed_from_success >>
  simp[vyperTypeInvariantsTheory.scope_well_typed_def] >> strip_tac >>
  `value_has_type entry.type entry.value` by metis_tac[] >>
  metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf,
            exprSimPropsTheory.val_footprint_le]
QED
