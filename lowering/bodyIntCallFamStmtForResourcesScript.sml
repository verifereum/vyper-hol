(* Resource transport at the declaration of an iteration variable. *)
Theory bodyIntCallFamStmtForResources
Ancestors
  bodyIntCallJointContract bodySim compileEnv bodySimDeclCases bodyExprPreFacts
  bodyIntCallDeclarationRegions bodyMemoryDefs stmtSimProps freshWrites
  venomExecSemantics venomState loweringPosts intCallFrame vyperState finite_map

Theorem intcall_for_declared_entry:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  lookup_scopes id es.scopes = NONE /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv v /\ type_memory_bytes ce fty < 2 ** 64 /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_var p t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  allocas_above fp.jc_lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  sa.cs_next_var <= sb0.cs_next_var /\ local_ptrs_reserved bc sb0 /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!a k. fp.jc_prot a k ==>
     mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) /\
  stmt_state_rel fp.jc_ctx fp.jc_func bc fp.jc_cx
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                       value := v; popped := []|>)) :: es.scopes) t ==>
  intcall_joint_res fp bc (extend_local env id fty F)
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                       value := v; popped := []|>)) :: es.scopes) sb0 t
Proof
  strip_tac >>
  `same_frame ce bc` by
    (drule declare_local_same_frame >> simp[] >> disch_then irule >> simp[]) >>
  `bc.ce_return_pc = ce.ce_return_pc /\
   bc.ce_return_buf = ce.ce_return_buf /\
   bc.ce_struct_fields = ce.ce_struct_fields /\
   bc.ce_module_vars = ce.ce_module_vars /\
   bc.ce_module = ce.ce_module /\ bc.ce_is_ctor = ce.ce_is_ctor` by
    fs[same_frame_def, compile_env_component_equality] >>
  fs[intcall_joint_res_def, bodyIntCallJointContractTheory.intcall_expr_res_def] >>
  `expr_sim_inv bc fp.jc_cx (extend_local env id fty F)
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                       value := v; popped := []|>)) :: es.scopes)` by
    (irule expr_sim_inv_for_scope >> metis_tac[]) >>
  `ce_locals_declared bc (extend_local env id fty F)` by
    (irule ce_locals_declared_declare_local >> metis_tac[]) >>
  `locals_alloc_ok bc (extend_local env id fty F)` by
    (irule locals_alloc_ok_extend >> qexists_tac `ce` >> simp[]) >>
  `ret_pc_ok bc sb0 t` by (irule ret_pc_ok_frame >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb bc sb0 t` by
    (irule return_buf_frame_frame >> metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- suspend "reserved"
  >- (metis_tac[not_fresh_at_mono])
  >- suspend "regions"
  >- suspend "rpc"
  >- suspend "frame"
  >- (rpt strip_tac >> fs[] >> metis_tac[])
QED

Resume intcall_for_declared_entry[reserved]:
  rpt strip_tac >>
  `?x z. op = Var x /\ lookup_var x fp.jc_oorig = SOME z` by
    (fs[intcall_frame_ok_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  qpat_x_assum `!op. fp.jc_reserved op ==> _`
    (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]
QED

Resume intcall_for_declared_entry[regions]:
  `!name. name <> id ==> FLOOKUP bc.ce_vars name = FLOOKUP ce.ce_vars name` by
    (drule_all declare_local_ptr >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `FLOOKUP bc.ce_vars id = SOME _` mp_tac >>
  disch_then (mp_then (Pos hd) mp_tac local_region_declaration_cases) >>
  disch_then (drule_at (Pos last)) >>
  disch_then (qspecl_then [`es.scopes`, `s`, `ce`] mp_tac) >>
  impl_tac
  >- (simp[lookup_scopes_def, FLOOKUP_UPDATE] >> conj_tac
      >- (rpt strip_tac >> gvs[]) >> rpt strip_tac >>
      qpat_x_assum `!x. not_fresh_at sa x ==> _` irule >>
      fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  strip_tac
  >- (gvs[] >> disj1_tac >> fs[allocas_above_def] >> metis_tac[]) >>
  qpat_x_assum `!n p k. local_region ce _ _ _ _ _ ==> _` irule >>
  goal_assum (drule_at Any)
QED

Resume intcall_for_declared_entry[rpc]:
  fs[intcall_frame_ok_def] >> metis_tac[eval_operand_def]
QED

Resume intcall_for_declared_entry[frame]:
  metis_tac[same_frame_trans]
QED

Finalise intcall_for_declared_entry
