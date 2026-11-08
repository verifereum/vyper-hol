(* Slot provenance for pure expression results, including zero-sized locals. *)
Theory bodyIntCallJointPureSlot
Ancestors
  bodyIntCallJointContract exprLoweringProps compileEnv venomState
  exprSimHypsDefs exprLowering exprSimNameValue context vyperTypeSystem
  typedCopyMetadata placeMemoryTypedBase valueEncodingTyping vyperTypeABI
  structFieldsProps retAbiPlanProps

Theorem joint_local_result_slot:
  intcall_joint_res fp ce env es sa s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  ?w. eval_operand (Var p) s = SOME w /\
      type_memory_size entry.type <= sz /\
      w2n w + sz < dimword (:256) /\
      (fp.jc_lo <= w2n w \/
       ?b z. fp.jc_staged b z /\ b <= w2n w /\ w2n w + sz <= b + z)
Proof
  strip_tac >> fs[intcall_joint_res_def] >>
  `?w. lookup_var p s = SOME w /\ w2n w + sz <= s.vs_alloca_next /\
        type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
  qexists `w` >> simp[eval_operand_def] >>
  metis_tac[]
QED

Theorem joint_name_result_slot:
  intcall_joint_res fp ce env es sa s /\
  well_typed_expr env (Name ann name) /\
  compile_expr ce ty (Name ann name) sa = (vv,sb) /\
  evaluate_type (get_tenv fp.jc_cx) ann = SOME tv ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\
    (fp.jc_lo <= a \/
     ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  strip_tac >>
  `?entry. lookup_scopes name es.scopes = SOME entry /\ entry.type = tv` by
    (fs[intcall_joint_res_def, expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     gvs[vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `?p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz)` by
    gvs[intcall_joint_res_def, expr_sim_inv_def,
        vyperTypeSystemTheory.well_typed_expr_def] >>
  drule_all joint_local_result_slot >> strip_tac >>
  drule exprSimNameValueTheory.compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  qexistsl [`w`, `w2n w`, `sz`] >>
  simp[vv_operand_def, mk_ptr_def] >> metis_tac[]
QED

Theorem joint_allocated_result_slot:
  intcall_joint_res fp ce env es sa s /\
  FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
  a + k < dimword (:256) /\ fp.jc_lo <= a
Proof
  strip_tac >> fs[intcall_joint_res_def, stmt_state_rel_def,
    venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
    intCallFrameTheory.allocas_above_def] >>
  `a + k <= s.vs_alloca_next` by metis_tac[] >>
  conj_tac >- decide_tac >> metis_tac[]
QED

Theorem joint_local_region_slot:
  intcall_joint_res fp ce env es sa s /\ local_region ce es.scopes s name a k ==>
  a + k < dimword (:256) /\
  (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  strip_tac >> fs[local_region_def] >>
  drule_all joint_local_result_slot >>
  simp[eval_operand_def] >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem joint_positive_result_slot:
  intcall_joint_res fp ce env es sc s /\
  vv_at ce fp.jc_cx ty sa sb es r vv s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  ~is_word_type ty /\ 0 < type_memory_size tv /\
  val_footprint tv v = type_memory_size tv /\
  (case vv of StackValue _ _ => T
            | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\
    (fp.jc_lo <= a \/
     ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  Cases_on `vv` >>
  simp[loweringPostsTheory.vv_at_def, loweringPostsTheory.expr_val_at_def,
       vv_operand_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  all_tac
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (a,k)`],
        drule_all joint_allocated_result_slot >> strip_tac >>
        qexistsl [`a`, `k`] >> simp[]) >>
  drule_all joint_local_region_slot >> strip_tac >>
  rename1 `local_region ce es.scopes s name a k` >>
  qexistsl [`a`, `k`] >> simp[] >> metis_tac[]
QED

Theorem evaluated_base_memory_positive:
  evaluate_type tenv (BaseT bt) = SOME tv ==> 0 < type_memory_size tv
Proof
  Cases_on `bt` >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[valueEncodingTheory.type_memory_size_def]
QED

Theorem evaluated_scalar_memory_positive:
  supportedTypes$supported_scalar_type ty /\
  evaluate_type tenv ty = SOME tv ==> 0 < type_memory_size tv
Proof
  Cases_on `ty` >>
  simp[supportedTypesTheory.supported_scalar_type_def,
       supportedTypesTheory.supported_word_type_def,
       supportedTypesTheory.supported_string_type_def] >>
  metis_tac[evaluated_base_memory_positive]
QED

Theorem evaluated_scalar_list_memory_positive:
  !tys tvs. ~NULL tys /\ EVERY supportedTypes$supported_scalar_type tys /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    0 < type_memory_size_list tvs
Proof
  Cases >> simp[] >> Cases >> simp[] >> rpt strip_tac >>
  drule_all evaluated_scalar_memory_positive >>
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem type_env_modules_struct_compare:
  !mods src tops name ta args.
    ALOOKUP mods src = SOME tops /\
    FLOOKUP (type_env_for_module src tops) (src,name) = SOME ta /\
    FLOOKUP (type_env_all_modules mods) (src,name) = SOME (StructArgs args) ==>
    ta = StructArgs args
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[vyperContextTheory.type_env_all_modules_def] >> strip_tac >>
  Cases_on `h0 = src`
  >- gvs[finite_mapTheory.FLOOKUP_FUNION] >>
  gvs[] >>
  Cases_on `FLOOKUP (type_env_for_module h0 h1) (src,name)` >>
  gvs[finite_mapTheory.FLOOKUP_FUNION]
  >- (first_x_assum drule_all >> simp[]) >>
  drule type_env_for_module_struct_mem >> simp[]
QED

Theorem evaluated_supported_struct_memory_positive:
  get_module_code cx NONE = SOME tops /\
  supportedTypes$supported_struct_fields tops id = SOME args /\ args <> [] /\
  EVERY (supportedTypes$supported_word_type o SND) args /\
  evaluate_type (get_tenv cx) (StructT id) = SOME tv ==>
  0 < type_memory_size tv
Proof
  PairCases_on `id` >> strip_tac >>
  `id0 = NONE` by
    (Cases_on `id0` >>
     gvs[supportedTypesTheory.supported_struct_fields_other_module]) >>
  gvs[] >>
  drule supported_struct_fields_type_env >>
  simp[vyperContextTheory.type_env_def] >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `args = args'` by
    (fs[vyperContextTheory.get_module_code_def,
        vyperContextTheory.get_tenv_def, AllCaseEqs()] >> gvs[] >>
     drule_all type_env_modules_struct_compare >> simp[]) >>
  gvs[] >>
  `~NULL (MAP SND args)` by (Cases_on `args` >> gvs[]) >>
  `EVERY supportedTypes$supported_scalar_type (MAP SND args)` by
    (fs[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
     metis_tac[supportedTypesTheory.supported_scalar_type_def]) >>
  drule evaluate_types_LIST_REL >> strip_tac >>
  `0 < type_memory_size_list tvs` by
    (irule evaluated_scalar_list_memory_positive >> metis_tac[]) >>
  `LENGTH tvs = LENGTH args` by
    metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_MAP] >>
  gvs[valueEncodingTheory.type_memory_size_def, type_memory_size_fields_zip]
QED

Theorem evaluated_supported_value_memory_positive:
  get_module_code cx NONE = SOME tops /\
  supportedTypes$supported_value_type tops ty /\
  (!id fs. supportedTypes$supported_struct_fields tops id = SOME fs ==> fs <> []) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==> 0 < type_memory_size tv
Proof
  strip_tac >>
  Cases_on `supportedTypes$supported_scalar_type ty`
  >- metis_tac[evaluated_scalar_memory_positive] >>
  Cases_on `ty` >>
  gvs[supportedTypesTheory.supported_value_type_def]
  >- (drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >>
      gvs[valueEncodingTheory.type_memory_size_def] >>
      irule evaluated_scalar_list_memory_positive >> metis_tac[])
  >- (gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
      rename1 `ArrayTV etv bd` >> Cases_on `bd` >>
      gvs[valueEncodingTheory.type_memory_size_def] >>
      `0 < type_memory_size etv` by
        metis_tac[evaluated_scalar_memory_positive,
                  supportedTypesTheory.supported_scalar_type_def] >>
      simp[]) >>
  rename1 `evaluate_type (get_tenv cx) (StructT id) = SOME tv` >>
  Cases_on `supportedTypes$supported_struct_fields tops id` >> gvs[] >>
  irule evaluated_supported_struct_memory_positive >> metis_tac[]
QED

Theorem joint_supported_result_slot:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sc s /\
  supportedTypes$supported_value_type fp.jc_tops ty /\
  vv_at ce fp.jc_cx ty sa sb es r vv s /\
  read_result fp.jc_cx r es = (INL v,es) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  (case vv of StackValue _ _ => T
            | LocatedValue _ p => p.ptr_location = LocMemory) ==>
  ?w a k. eval_operand (vv_operand vv) s = SOME w /\
    a <= w2n w /\ w2n w + type_memory_size tv <= a + k /\
    a + k < dimword (:256) /\
    (fp.jc_lo <= a \/
     ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)
Proof
  strip_tac >>
  `0 < type_memory_size tv` by
    (irule evaluated_supported_value_memory_positive >>
     qexistsl [`fp.jc_cx`, `fp.jc_tops`, `ty`] >>
     gvs[intcall_frame_ok_def, bodySimTheory.body_inv_def]) >>
  `val_footprint tv v = type_memory_size tv` by
    (irule exprSimAggregateChildrenTheory.evaluated_nonbytes_footprint >>
     metis_tac[]) >>
  drule_all joint_positive_result_slot >> simp[]
QED

Theorem supported_type_builtin_complex_result:
  supportedExprForms$supported_type_builtin_form tops ty tb target args /\
  well_typed_expr env (TypeBuiltin ty tb target args) /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  supportedTypes$supported_value_type tops ty
Proof
  Cases_on `tb` >> strip_tac >>
  gvs[supportedExprFormsTheory.supported_type_builtin_form_def,
      well_typed_expr_def, type_builtin_result_ok_def,
      well_typed_type_builtin_args_def, is_word_type_def, is_bytestring_type_def,
      supportedExprFormsTheory.supported_numeric_type_def,
      supportedTypesTheory.supported_integer_type_def,
      supportedExprFormsTheory.supported_signed_type_def,
      supportedExprFormsTheory.supported_unsigned_type_def, AllCaseEqs()]
  >>~- ([`supported_integer_type target`],
      Cases_on `target` >> gvs[supportedTypesTheory.supported_integer_type_def] >>
       rename1 `BaseT bt` >> Cases_on `bt` >>
       gvs[supportedTypesTheory.supported_integer_type_def, is_word_type_def]) >>
  Cases_on `args` >> gvs[]
  >>~- ([`valid_conversion src target`],
     Cases_on `target` >> gvs[valid_conversion_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[valid_conversion_def, is_word_type_def, is_bytestring_type_def,
         well_formed_type_def]
     >- (rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, is_bytestring_type_def,
             vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
     Cases_on `src` >> gvs[valid_conversion_def])
  >~ [`extract32_result_base_ok bt`] >-
    (rename1 `LENGTH tail = 1` >> Cases_on `tail` >> gvs[]) >>
  rename1 `supported_tuple_type target` >>
  Cases_on `target` >>
  gvs[supportedTypesTheory.supported_tuple_type_def,
      supportedTypesTheory.supported_value_type_def]
QED
