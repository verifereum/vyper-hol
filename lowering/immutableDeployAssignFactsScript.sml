(* Constructor immutable assignment: layout and state interface probes. *)
Theory immutableDeployAssignFacts
Ancestors
  bodySim exprSimHypsDefs exprLoweringProps loweringPosts
  exprLowering compileEnv vyperTypeSystem exprSimHyps compileVyper vyperContext
  structFieldsProps

Theorem immutable_assign_target_layout:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  ~cx_const_name cx (src,id) ==>
  src = cenv.ce_module /\
  cenv.ce_module_var_type (src,id) = SOME ty /\
  ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
        compile_get_target_ptr cfn cenv (TopLevelNameTarget (src,id)) =
          return (Lit (n2w off), SOME LocCode, SOME (ValPT ty)) /\
        (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
              off + type_memory_size tv < dimword (:256))
Proof
  rpt strip_tac >>
  `src = cenv.ce_module /\
   cenv.ce_module_var_type (src,id) = SOME ty /\
   ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
              off + type_memory_size tv < dimword (:256)` by
    (fs[expr_sim_inv_def, bare_globals_layout_def] >> metis_tac[]) >>
  gvs[compile_get_target_ptr_def]
QED

Theorem immutable_assign_declared_region:
  stmt_state_rel H ctx func cenv cx es s /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  off + type_memory_size tv <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint off (type_memory_size tv) b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint off (type_memory_size tv) b sz)
Proof
  simp[stmt_state_rel_def, immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  metis_tac[]
QED

Theorem immutable_exact_slot_size:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env st ==>
  !ty tv. evaluate_type (type_env tops) ty = SOME tv ==>
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
    type_memory_size tv
Proof
  strip_tac >>
  qpat_assum `body_inv _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [body_inv_def]) >>
  `get_tenv cx = type_env tops` by
    simp[get_tenv_def, type_env_all_modules_def, type_env_def] >>
  rpt strip_tac >>
  qpat_assum `cenv.ce_struct_fields = _` (SUBST1_TAC o SYM) >>
  rewrite_tac[type_mem_bytes_type_memory_bytes] >>
  irule expr_sim_inv_memory_size >> simp[] >> metis_tac[]
QED
