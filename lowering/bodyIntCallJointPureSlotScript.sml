(* Slot provenance for pure expression results, including zero-sized locals. *)
Theory bodyIntCallJointPureSlot
Ancestors
  bodyIntCallJointContract exprLoweringProps compileEnv venomState
  exprSimHypsDefs exprLowering exprSimNameValue context vyperTypeSystem

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
