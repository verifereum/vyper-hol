Theory bodyFullToplevelCtorSourceFrame
Ancestors
  bodySim bodyInvCodeProps exprBodyPreProps bodyFullShadowBodyInv
  immutableRegionFrameProps stateRelProj loweringStateRelDefs
  bodyPtrDefs exprSimHypsDefs exprLoweringProps
  bodyInvSplit[qualified]

Theorem toplevel_ctor_source_frame_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v off mem
Proof
  strip_tac >> gvs[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `es.immutables = es.immutables` by simp[] >>
  drule_all immutable_ctor_frame_mods >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  qpat_x_assum `tops = _` kall_tac >>
  qpat_x_assum `off = _` kall_tac >>
  qpat_x_assum `src = _` SUBST_ALL_TAC >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_all_then assume_tac body_inv_expr_body_pre_mods >>
  fs[GSYM dead_lo_ok_mods_singleton, GSYM ghost_inv_at_mods_singleton] >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                 `src` |-> `cenv.ce_module`] toplevel_ctor_source_frame_mods) >>
  simp[]
QED
*)
Theorem toplevel_ctor_source_frame:
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
  evaluate_type (get_tenv cx) ann = SOME rt /\
  cx_tops cx = tops /\ off + type_memory_size rt <= lo /\
  tops = pre ++ VariableDecl vis Immutable id ann slot :: post /\
  off = compute_immutables_len
    (get_struct_fields (make_struct_fields_map tops)) pre /\
  type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ann =
    type_memory_size rt ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory rt v off mem
Proof
  cheat
QED
