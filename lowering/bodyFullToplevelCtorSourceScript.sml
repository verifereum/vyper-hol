Theory bodyFullToplevelCtorSource
Ancestors
  bodyFullToplevelCtorSourceLayout bodyFullToplevelCtorSourceFrame
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  bodyFullShadowBodyInv[qualified] bodyPtrDefs[qualified]

Theorem toplevel_ctor_source_contract:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  off + type_memory_size rt <= lo /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v off mem)
Proof
  strip_tac >> gvs[] >>
  `dead_lo_ok_mods H D lo cenv cx` by
    fs[bodyFullShadowBodyInvTheory.dead_lo_ok_mods_def, bodyPtrDefsTheory.dead_lo_ok_def] >>
  `ghost_inv_at_mods D lo d cenv cx es G tn s` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
     PURE_REWRITE_TAC [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,
                       bodyPtrDefsTheory.ghost_inv_at_def] >> simp[]) >>
  drule_all toplevel_ctor_source_layout >> strip_tac >>
  simp[] >>
  match_mp_tac (Q.INST [`src` |-> `cenv.ce_module`] toplevel_ctor_source_frame_mods) >>
  simp[] >>
  goal_assum (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >> simp[]
QED
