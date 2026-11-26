Theory bodyExtSavedCtorReadMods
Ancestors
  bodyFullPostsMods immutableRegionFrameProps loweringPosts compileEnv
  venomState valueEncodingDefs words arithmetic finite_map

(* Read from the module carried by the saved LocCode value, at the same
   endpoint as the linked immutable frame and the ghost taint mask. *)
Theorem ext_saved_ctor_read_linked:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
  cenv.ce_is_ctor /\ p.ptr_location = LocCode /\ dead_lo_ok_mods H D lo cenv cx /\
  ee.immutables = entry.immutables /\ immutable_frame_mods func cenv cx ee u /\
  ghost_inv_at_mods D lo d cenv cx ee G tn u /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
     vv_holds_mods cenv cx ty raw (LocatedValue ty p) ee u) ==>
  !rt w. evaluate_type (get_tenv cx) ty = SOME rt /\
         eval_operand p.ptr_operand u = SOME w ==>
    w2n w + type_memory_size rt <= lo /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
  strip_tac >> Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  rename1 `ALOOKUP entry.immutables cx.txn.target = SOME imms` >>
  `ALOOKUP ee.immutables cx.txn.target = SOME imms` by simp[] >>
  fs[immutable_frame_mods_def] >>
  drule_all_then strip_assume_tac qualified_immutable_ctor_frame_mods >>
  fs[sub_layout_def] >>
  `k + off < dimword (:256)` by decide_tac >>
  `type_memory_size rt + (k + off) <= lo` by decide_tac >>
  simp[LESS_MOD] >> rpt strip_tac >> once_rewrite_tac[ADD_COMM] >>
  qpat_assum `!b mem. val_in_memory _ _ b mem ==> _` irule >> simp[]
QED
