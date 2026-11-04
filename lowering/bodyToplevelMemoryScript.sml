(* Code-free storage/transient value views; forcing is not certified here. *)
Theory bodyToplevelMemory
Ancestors
  bodyMemoryDefs exprSimLeaves exprSimHyps exprSim exprLowering
  compileEnv fragExecMem venomState loweringSlice valueEncoding
  exprLoweringProps accountsRelProps
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTyping
  vyperValueOperation vyperStorageLayoutSafety vyperLookupStorage
  vyperTypeGlobalLookupSoundness

Theorem compile_toplevel_storage_vv_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_mem_def] >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >>
     gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  drule_all eval_expr_toplevel_storage >> strip_tac >> gvs[] >>
  reverse (Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`)
  >- (simp[frag_exec_mem_def, stmt_state_rel_def, state_rel_def] >>
      metis_tac[]) >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_def, expr_type_def] >>
  Cases_on `tr` >> simp[] >> strip_tac >> gvs[] >>
  irule frag_exec_mem_refl >> rpt strip_tac >> gvs[] >>
  simp[vv_post_def, vv_holds_def, vv_at_def, storage_holds_def,
       contextTheory.mk_ptr_def, eval_operand_def, expr_type_def]
QED

Theorem compile_toplevel_storage_undecodable_sim_mem:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rpt strip_tac >> simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `F` suffices_by simp[] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM] >>
  Cases_on `lookup_var_slot_from_layout cx tr src id_str` >>
  simp[raise_def, return_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> simp[raise_def, return_def]
  >- (strip_tac >> gvs[expr_vv_res_ok_def]) >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_TOPLEVEL_MEMORY_AUDIT OK\n"
     else raise Fail "toplevel memory inherited admission"
  end) [compile_toplevel_storage_vv_sim_mem,
        compile_toplevel_storage_undecodable_sim_mem];
