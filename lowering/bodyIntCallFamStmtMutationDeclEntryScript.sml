(* Pending declarations transport expression resources, not statement resources. *)
Theory bodyIntCallFamStmtMutationDeclEntry
Ancestors
  bodyIntCallJointContract bodySimDeclCases bodyExprPreFacts bodyDeclCopyMemory
  stmtSimDecl stmtSimProps stmtLowering bodySim compileEnv loweringPosts
  finite_map venomState exprLoweringProps

Theorem local_region_declare_local_pending:
  declare_local ce id ty sa = (c,sb) /\ ce.ce_alloca_locals /\
  lookup_scopes id scopes = NONE ==>
  (local_region c scopes s n b k <=> local_region ce scopes s n b k)
Proof
  strip_tac >> drule_all declare_local_ptr >> strip_tac >>
  Cases_on `n = id` >> gvs[local_region_def] >> metis_tac[]
QED

Theorem intcall_expr_res_declare_local_pending:
  intcall_expr_res fp ce env es sa s /\
  declare_local ce id ty sa = (c,sb) /\ ce.ce_alloca_locals /\
  id NOTIN FDOM env.var_types /\ lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?p sz. l = PtrVar p sz) ==>
  intcall_expr_res fp c env es sb s
Proof
  strip_tac >>
  `same_frame ce c` by (irule declare_local_same_frame >> metis_tac[]) >>
  `expr_sim_inv c fp.jc_cx env es` by
    (irule expr_sim_inv_declare_local >> fs[intcall_expr_res_def] >> metis_tac[]) >>
  `stmt_state_rel fp.jc_ctx fp.jc_func c fp.jc_cx es s` by
    (irule stmt_state_rel_declare_local_entry >> fs[intcall_expr_res_def] >> metis_tac[]) >>
  `local_ptrs_reserved c sb` by
    (irule declare_local_reserved >> fs[intcall_expr_res_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (drule_all declare_local_ptr >> strip_tac >> simp[not_fresh_at_def]) >>
  `(!t. type_memory_bytes c t = type_memory_bytes ce t)` by
    (drule_all declare_local_memory_types_mem >> simp[]) >>
  `c.ce_return_pc = ce.ce_return_pc /\ c.ce_return_buf = ce.ce_return_buf /\
   c.ce_module_vars = ce.ce_module_vars /\ c.ce_module = ce.ce_module /\
   c.ce_is_ctor = ce.ce_is_ctor` by
    (fs[same_frame_def, compile_env_component_equality]) >>
  simp[intcall_expr_res_def] >>
  fs[intcall_expr_res_def] >> rpt conj_tac
  >- (fs[locals_alloc_ok_def] >> gvs[])
  >- (rpt strip_tac >> drule_all local_region_declare_local_pending >> metis_tac[])
  >- (fs[ret_pc_ok_def] >> metis_tac[])
  >- (Cases_on `fp.jc_rb` >- fs[return_buf_frame_def] >>
      PairCases_on `x` >> fs[return_buf_frame_def] >> metis_tac[])
  >- metis_tac[same_frame_trans] >>
  metis_tac[]
QED
