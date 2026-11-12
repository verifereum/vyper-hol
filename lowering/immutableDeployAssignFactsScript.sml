(* Constructor immutable assignment: layout and state interface probes. *)
Theory immutableDeployAssignFacts
Ancestors
  bodySim exprSimHypsDefs exprLoweringProps loweringPosts
  exprLowering compileEnv vyperTypeSystem

Theorem immutable_assign_target_layout:
  expr_sim_inv cenv cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ty ==>
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
  stmt_state_rel ctx func cenv cx es s /\ cenv.ce_is_ctor /\
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
