Theory bodyFullToplevelCtorSource
Ancestors
  bodyFullToplevelCtorSourceLayout bodyFullToplevelCtorSourceFrame

Theorem toplevel_ctor_source_contract:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
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
  strip_tac >>
  drule_all toplevel_ctor_source_layout >> strip_tac >>
  qpat_x_assum `ty = ann` SUBST_ALL_TAC >>
  conj_tac >- simp[] >>
  metis_tac[toplevel_ctor_source_frame]
QED
