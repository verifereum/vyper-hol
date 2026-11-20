(* Caller-local boundaries used by the joint internal-call return frame. *)
Theory bodyFullIntCallReturnFrame
Ancestors
  bodySim bodyFullIntCallDefs exprLoweringProps ctorDeployDeadSection
  immutableLocationProps vyperTypeContract abiCallerTypeEnv vyperContext finite_map alist
  bodySimLogArgs stateRelProj fnRunFields
  bodyStorageMetadata compileVyper list bodyPtrDefs ptrDiscipline intCallFrame
  bodyPtrMakeArrayMemoryFrame intCallReturn vyperImmutableMetadataFrame
  execMemoryLength

Theorem return_stmt_immutable_sep:
  stmt_state_rel H ctx func cenv cx vs ss ==>
  immutable_alloca_sep func cenv cx vs ss
Proof
  simp_tac bool_ss [stmt_state_rel_def]
QED

Theorem intcall_immutable_decl_metadata:
  body_inv (pre ++ [VariableDecl vis Immutable name ty slot] ++ post)
    ctx cenv cx ==>
  cenv.ce_module = NONE /\
  FLOOKUP cenv.ce_module_vars (NONE,name) =
    SOME (ImmutableLoc (compute_immutables_len
      (get_struct_fields (make_struct_fields_map
        (pre ++ [VariableDecl vis Immutable name ty slot] ++ post))) pre)) /\
  cenv.ce_module_var_type (NONE,name) = SOME ty
Proof
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option))
      (pre ++ [VariableDecl vis Immutable name ty slot] ++ post)))` by
    fs[body_inv_def] >>
  `MEM (VariableDecl vis Immutable name ty slot)
      (pre ++ [VariableDecl vis Immutable name ty slot] ++ post)` by simp[] >>
  drule_all build_maps_variable >> strip_tac >>
  `!vis' name' ty' slot'.
    MEM (VariableDecl vis' Immutable name' ty' slot') post ==> name' <> name` by
    (gvs[ALL_DISTINCT_APPEND, toplevel_vtype_keys_toplevel_def] >>
     rpt strip_tac >> gvs[] >>
     drule vyperTypeContractStaticMapsTheory.module_toplevel_vtype_key_MEM_Variable >>
     disch_then (qspec_then `NONE` mp_tac) >> simp[]) >>
  fs[body_inv_def, cenv_module_pins_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  irule (add_immutable_locations_declaration_lookup |> Q.INST [`off` |-> `0`] |> SRULE []) >>
  simp[]
QED

Theorem intcall_local_immutable_dead_disjoint:
  body_inv tops ctx cenv cx /\ cenv.ce_is_ctor /\
  immutable_decl_sep cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  local_region cenv scopes t name b sz /\ b <= i /\ i < b + sz ==>
  ~imm_section_dead (cx_tops cx) sec i
Proof
  rpt strip_tac >>
  `cx_tops cx = tops` by (fs[body_inv_def] >> simp[gasContextTheory.cx_tops_def]) >>
  gvs[immSectionDeadTheory.imm_section_dead_def] >>
  drule (cj 1 mem_dead_bytes_range) >> strip_tac >>
  drule intcall_immutable_decl_metadata >> strip_tac >>
  `get_module_code cx NONE = SOME (cx_tops cx)` by
    (fs[body_inv_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by
    metis_tac[abi_caller_type_submap, body_main_type_env_submap] >>
  gvs[immutable_decl_sep_alt] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_immutable_decl_evaluates[local]:
  expr_sim_inv cenv cx tenv es /\
  get_module_code cx NONE = SOME tops /\
  MEM (VariableDecl vis Immutable name ty slot) tops ==>
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rpt strip_tac >>
  `env_context_consistent tenv cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def] >>
  `FLOOKUP tenv.toplevel_vtypes (NONE,name) = SOME (Type ty)` by
    (fs[vyperTypeInvariantsTheory.env_context_consistent_def,
        vyperTypeInvariantsTheory.toplevel_vtypes_complete_def] >>
     qpat_x_assum `!src ts vis mut id ty init. _` irule >>
     qexistsl [`slot`, `Immutable`, `tops`, `vis`] >> simp[]) >>
  fs[vyperTypeInvariantsTheory.env_context_consistent_def] >>
  qpat_x_assum `!src id vt. _ ==> well_formed_vtype _ _` drule >>
  simp[vyperTypeSystemTheory.well_formed_vtype_def,
       vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]
QED

Theorem intcall_evaluated_immutable_coverage:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx tenv es /\
  i < imm_len (cx_tops cx) ==>
  ?pre vis name ty slot post tv.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    compute_immutables_len (get_struct_fields cenv.ce_struct_fields) pre <= i /\
    i < compute_immutables_len (get_struct_fields cenv.ce_struct_fields) pre +
        type_memory_size tv
Proof
  rpt strip_tac >>
  `cx_tops cx = tops /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_struct_fields = make_struct_fields_map tops` by
    (fs[body_inv_def, cenv_module_pins_def, gasContextTheory.cx_tops_def] >>
     metis_tac[]) >>
  `i < compute_immutables_len (get_struct_fields cenv.ce_struct_fields) tops` by
    gvs[immSectionDeadTheory.imm_len_def] >>
  drule compute_immutables_len_byte_coverage >> strip_tac >>
  `MEM (VariableDecl vis Immutable name ty slot) tops` by simp[] >>
  drule_all intcall_immutable_decl_evaluates >> strip_tac >>
  drule_all exprSimHypsTheory.expr_sim_inv_memory_size >> strip_tac >>
  qexistsl [`pre`, `vis`, `name`, `ty`, `slot`, `post`, `tv`] >>
  gvs[structFieldsPropsTheory.type_mem_bytes_type_memory_bytes]
QED

Theorem intcall_local_immutable_prefix_disjoint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx tenv es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  local_region cenv scopes t name b sz /\ b <= i /\ i < b + sz ==>
  imm_len (cx_tops cx) <= i
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `i < imm_len (cx_tops cx)` by decide_tac >>
  drule_all intcall_evaluated_immutable_coverage >> strip_tac >>
  qpat_x_assum `tops = _` SUBST_ALL_TAC >>
  drule (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] intcall_immutable_decl_metadata) >> strip_tac >>
  `cenv.ce_struct_fields = make_struct_fields_map
     (pre ++ VariableDecl vis Immutable name' ty slot :: post)` by
    fs[body_inv_def, cenv_module_pins_def] >>
  gvs[immutable_decl_sep_alt] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_alloca_immutable_prefix_disjoint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx tenv es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz ==>
  imm_len (cx_tops cx) <= i
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `i < imm_len (cx_tops cx)` by decide_tac >>
  drule_all intcall_evaluated_immutable_coverage >> strip_tac >>
  qpat_x_assum `tops = _` SUBST_ALL_TAC >>
  drule (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] intcall_immutable_decl_metadata) >> strip_tac >>
  `cenv.ce_struct_fields = make_struct_fields_map
     (pre ++ VariableDecl vis Immutable name ty slot :: post)` by
    fs[body_inv_def, cenv_module_pins_def] >>
  gvs[immutable_decl_sep_alt] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_return_ghost_inv:
  !tops ctx cenv cx H DF lo sa mut nr rtv rc rb sm t tn v ee Gc tc ir cs
   outs out d func tenv name es vv s0 es0 G0 tn0 args ret ss rr prev penv es1 G.
  body_inv tops ctx cenv cx /\
  dead_lo_ok H (DF H) lo cenv cx /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc rb
    sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME out /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) ==>
  ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev)
    (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs))) out
Proof
  rpt strip_tac >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `ghost_inv_at (DF H) lo d cenv cx (es1 with scopes := prev) G tn t` by
    fs[intcall_entry_full_def] >>
  simp[ghost_inv_at_def] >> rpt conj_tac
  >- suspend "locals"
  >- suspend "buffer"
  >- suspend "pc"
  >- suspend "storage"
  >- suspend "fixed"
  >- suspend "base"
  >> gvs[ghost_inv_at_def, allocas_from_def] >> metis_tac[]
QED

Resume intcall_return_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by
    (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `~MEM p outs` by metis_tac[] >>
  `lookup_var p out = lookup_var p t` by metis_tac[] >>
  `ptr_covers G tn p t sz /\
   !w mem. lookup_var p t = SOME w /\
     mem_agree_outside tn.t_mem t.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  conj_tac
  >- gvs[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `local_region cenv prev t name' (w2n w) sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev)` by
    fs[intcall_entry_full_def] >>
  `w2n w + sz <= t.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_wf entry.type entry.value` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     fs[loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     qpat_x_assum `!n e p sz. _ ==> ?w. _` drule_all >>
     strip_tac >> gvs[]) >>
  `immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
    (drule return_stmt_immutable_sep >> simp[immutable_alloca_sep_def]) >>
  `!i. w2n w <= i /\ i < w2n w + sz ==> lo <= i` by
    (rpt strip_tac >> fs[dead_lo_ok_def] >>
     Cases_on `cenv.ce_is_ctor` >> gvs[] >>
     drule_all (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] intcall_local_immutable_prefix_disjoint) >> simp[]) >>
  `mem_bytes_at (w2n w) sz cs.vs_memory = mem_bytes_at (w2n w) sz t.vs_memory` by
    (Cases_on `sz = 0` >- gvs[valueEncodingDefsTheory.mem_bytes_at_def] >>
     `cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= w2n w` by
       (strip_tac >>
        qpat_x_assum `!i. w2n w <= i /\ _ ==> lo <= i`
          (qspec_then `w2n w` mp_tac) >>
        gvs[dead_lo_ok_def]) >>
     fs[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
        exprSimDefsTheory.expr_exit_def] >>
     first_x_assum irule >> simp[] >> rpt strip_tac >>
     fs[intcall_entry_full_def] >>
     metis_tac[]) >>
  `!i. w2n w <= i /\ i < w2n w + sz /\ i IN tc.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >> fs[intcall_callee_exit_full_def] >>
     qpat_x_assum `!i. lo <= i /\ _ ==> _` irule >> simp[] >>
     rpt strip_tac >>
     `regions_disjoint (w2n w) sz off asz` by
       (fs[intcall_entry_full_def] >>
        metis_tac[]) >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  drule exprSimPropsTheory.val_footprint_le >> strip_tac >>
  irule bodyPtrMakeArrayMemoryFrameTheory.robust_val_in_memory_shrinking_frame >>
  conj_tac >- simp[] >>
  qexistsl [`tn.t_mem`, `tc.t_mem`, `t.vs_memory`, `cs.vs_memory`, `sz`] >>
  simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
Resume intcall_return_ghost_inv[buffer]:
  Cases_on `d` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair) _ _ _ _` >> PairCases_on `pair` >>
  fs[ghost_inv_at_def, return_buf_ptr_def] >>
  `not_fresh_at sa x` by metis_tac[] >>
  `~MEM x outs` by metis_tac[] >>
  gvs[ptr_covers_def, op_taint_def, FLOOKUP_DRESTRICT]
QED
Resume intcall_return_ghost_inv[pc]:
  rpt strip_tac >>
  `not_fresh_at sa x` by metis_tac[] >>
  `~MEM x outs` by metis_tac[] >>
  fs[ghost_inv_at_def, op_taint_def, FLOOKUP_DRESTRICT]
QED
Resume intcall_return_ghost_inv[storage]:
  `stor_taint_ok_at (DF H) tc cs` by fs[intcall_callee_exit_full_def] >>
  `t.vs_call_ctx.cc_address = cx.txn.target` by
    (qhdtm_assum `intcall_entry_full`
       (strip_assume_tac o PURE_REWRITE_RULE [intcall_entry_full_def]) >>
     drule stmt_state_rel_state_rel >>
     disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  `cs.vs_call_ctx.cc_address = cx.txn.target` by
    (fs[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
        exprSimDefsTheory.expr_exit_def] >>
     drule state_rel_call_ctx_rel >>
     simp[loweringStateRelDefsTheory.call_ctx_rel_def]) >>
  fs[venomExecSemanticsTheory.bind_outputs_def] >>
  qspec_then `ZIP (outs,ir.iret_values)`
    (qspec_then `adopt_return_fmp ir (merge_callee_state t cs)` strip_assume_tac)
    intCallFrameTheory.foldl_update_var_frame >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[venomExecSemanticsTheory.adopt_return_fmp_def,
      venomExecSemanticsTheory.merge_callee_state_def,
      stor_taint_ok_at_def]
QED
Resume intcall_return_ghost_inv[fixed]:
  gvs[intcall_callee_exit_full_def]
QED
Resume intcall_return_ghost_inv[base]:
  rpt strip_tac >>
  `not_fresh_at sa x` by
    fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
  `~MEM x outs` by metis_tac[] >>
  gvs[ghost_inv_at_def, op_taint_def, FLOOKUP_DRESTRICT]
QED
Finalise intcall_return_ghost_inv

Theorem intcall_return_ghost_kept:
  !tops ctx cenv cx H DF lo sa mut nr rtv rc rb sm t tn v ee Gc tc ir cs
   outs out d func tenv name es vv s0 es0 G0 tn0 args ret ss rr prev penv es1 G.
  body_inv tops ctx cenv cx /\
  dead_lo_ok H (DF H) lo cenv cx /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc rb
    sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME out /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) ==>
  ghost_kept_at lo cenv es0 sa G0 tn0 s0
    (DRESTRICT G (COMPL (set outs)))
    (tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)))
Proof
  rpt strip_tac >>
  `ghost_kept_at lo cenv es0 sa G0 tn0 s0 G tn` by
    fs[intcall_entry_full_def] >>
  simp[ghost_kept_at_def] >> rpt conj_tac
  >- (rpt strip_tac >> `~MEM x outs` by metis_tac[] >>
      gvs[ghost_kept_at_def, op_taint_def, FLOOKUP_DRESTRICT])
  >- suspend "allocas"
  >> suspend "locals"
QED
Resume intcall_return_ghost_kept[allocas]:
  rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev)` by
    fs[intcall_entry_full_def] >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by
    (fs[intcall_entry_full_def] >> metis_tac[]) >>
  `off + sz <= t.vs_alloca_next /\
   immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     drule return_stmt_immutable_sep >>
     simp[immutable_alloca_sep_def] >>
     fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[]) >>
  `lo <= i` by
    (fs[dead_lo_ok_def] >> Cases_on `cenv.ce_is_ctor` >> gvs[] >>
     spose_not_then assume_tac >>
     `i < imm_len (cx_tops cx)` by decide_tac >>
     drule_all intcall_evaluated_immutable_coverage >> strip_tac >>
     qpat_x_assum `tops = _` SUBST_ALL_TAC >>
     drule (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]
       intcall_immutable_decl_metadata) >> strip_tac >>
     `cenv.ce_struct_fields = make_struct_fields_map
       (pre ++ VariableDecl vis Immutable name' ty slot :: post)` by
       fs[body_inv_def, cenv_module_pins_def] >>
     gvs[immutable_decl_sep_alt] >>
     first_x_assum drule_all >> strip_tac >>
     qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = _ ==> _` drule >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `i IN tn.t_mem` by
    (fs[intcall_callee_exit_full_def] >>
     qpat_x_assum `!i. lo <= i /\ _ ==> _` irule >> simp[] >>
     rpt strip_tac >>
     drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.allocas_non_overlapping_def] >>
     `aid <> aid'` by decide_tac >>
     first_x_assum drule_all >> decide_tac) >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED
Resume intcall_return_ghost_kept[locals]:
  rpt strip_tac >>
  `local_region cenv prev t n b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl [`s0`, `sa`, `es0.scopes`] >>
     fs[intcall_entry_full_def,
        loweringPostsTheory.locals_kept_def]) >>
  `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev)` by
    fs[intcall_entry_full_def] >>
  `b + sz <= t.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
     fs[loweringStateRelDefsTheory.local_region_def,
        loweringStateRelDefsTheory.local_ptrs_rel_def] >>
     qpat_x_assum `!n e p sz. _ ==> ?w. _` drule_all >> strip_tac >> gvs[]) >>
  `immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
    (drule return_stmt_immutable_sep >> simp[immutable_alloca_sep_def]) >>
  `lo <= i` by
    (fs[dead_lo_ok_def] >> Cases_on `cenv.ce_is_ctor` >> gvs[] >>
     drule_all intcall_local_immutable_prefix_disjoint >> simp[]) >>
  `i IN tn.t_mem` by
    (fs[intcall_callee_exit_full_def] >>
     qpat_x_assum `!i. lo <= i /\ _ ==> _` irule >> simp[] >>
     rpt strip_tac >>
     `regions_disjoint b sz off asz` by
       (fs[intcall_entry_full_def] >>
        metis_tac[]) >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[ghost_kept_at_def] >> metis_tac[]
QED
Finalise intcall_return_ghost_kept

Theorem intcall_return_stmt_state_rel:
  !tops ctx cenv cx H DF lo sa mut nr rtv rc rb sm t tn v ee Gc tc ir cs
   outs returned out d func tenv name es vv s0 es0 G0 tn0 args ret ss rr prev penv es1 G
   fuel callee argv setup obs inst.
  body_inv tops ctx cenv cx /\
  dead_lo_ok H (DF H) lo cenv cx /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  intcall_entry_full (DF,lo,d) H tops ctx func cenv cx tenv name es sa sm vv
    s0 es0 G0 tn0 (mut,nr,args,ret,ss,rr) prev penv rtv es1 t G tn /\
  intcall_callee_exit_full (DF,lo) H func cenv cx mut nr rtv rc rb
    sa.cs_next_id sm.cs_next_id t tn (INL v) ee (Gc,tc) (IntRet ir cs) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
  intcall_callee_src cx name mut nr ss (es1 with gas_obs := obs) = (INL v,ee) /\
  setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs /\
  step_inst fuel ctx inst t = OK returned /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME returned /\
  (!x. MEM x outs ==> ~not_fresh_at sa x) ==>
  stmt_state_rel H ctx func cenv cx (out with scopes := prev) returned
Proof
  rpt strip_tac >>
  `stmt_state_rel H ctx func cenv cx (es1 with scopes := prev) t /\
   expr_sim_inv cenv cx tenv (es1 with scopes := prev)` by
    fs[intcall_entry_full_def] >>
  `state_rel H func cenv cx (out with scopes := []) cs /\
   ir.iret_adopt_fmp = NONE` by
    (fs[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
        exprSimDefsTheory.expr_exit_def] >> gvs[]) >>
  drule invoke_return_frame >> strip_tac >>
  irule stmt_state_rel_allocas_frame >>
  conj_tac >- suspend "base" >>
  conj_tac >- suspend "immutable" >>
  conj_tac >- suspend "state" >>
  qexistsl [`es1 with scopes := prev`, `t`] >> simp[] >>
  suspend "fmp"
QED
Resume intcall_return_stmt_state_rel[state]:
  `cs.vs_data_section = t.vs_data_section` by
    (drule run_blocks_intret_data_section >>
     gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()]) >>
  `local_ptrs_rel func cenv prev returned` by
    (irule invoke_return_local_ptrs_rel >>
     goal_assum (drule_at Any) >> simp[] >>
     reverse conj_tac
     >- (conj_tac
         >- (simp[EVERY_MEM, loweringStateRelDefsTheory.not_local_ptr_def] >>
             fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
         drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     rpt strip_tac >>
     rename1 `local_region cenv prev t name' b sz` >>
     Cases_on `sz = 0`
     >- gvs[valueEncodingDefsTheory.mem_bytes_at_def] >>
     `b + sz <= t.vs_alloca_next` by
       (drule stmt_state_rel_local_ptrs_alloca >> simp[] >> strip_tac >>
        fs[loweringStateRelDefsTheory.local_ptrs_rel_def,
           loweringStateRelDefsTheory.local_region_def] >>
        first_x_assum drule_all >> strip_tac >> gvs[]) >>
     `cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b` by
       (strip_tac >>
        `immutable_decl_sep cenv cx prev t.vs_vars t.vs_allocas t.vs_alloca_next` by
          (drule return_stmt_immutable_sep >> simp[immutable_alloca_sep_def]) >>
        irule intcall_local_immutable_prefix_disjoint >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     fs[intcall_callee_exit_full_def, bodyIntCallSeamsTheory.intcall_callee_exit_def,
        exprSimDefsTheory.expr_exit_def] >>
     sym_tac >> first_x_assum irule >> simp[] >> rpt strip_tac >>
     fs[intcall_entry_full_def] >> metis_tac[]) >>
  qspecl_then [`ZIP (outs, ir.iret_values)`,
    `adopt_return_fmp ir (merge_callee_state t cs)`]
    strip_assume_tac foldl_update_var_frame >>
  `returned = (adopt_return_fmp ir (merge_callee_state t cs)) with vs_vars := vars` by
    (fs[venomExecSemanticsTheory.bind_outputs_def] >> metis_tac[]) >>
  `cs.vs_call_ctx = t.vs_call_ctx /\ cs.vs_tx_ctx = t.vs_tx_ctx /\
   cs.vs_block_ctx = t.vs_block_ctx /\ cs.vs_code = t.vs_code` by
    (drule run_blocks_intret_fields >>
     gvs[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()]) >>
  irule state_rel_frame >>
  conj_tac >- (simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  qexistsl [`out with scopes := []`, `cs`] >>
  drule state_rel_immutables_rel >>
  simp[loweringStateRelDefsTheory.immutables_rel_def,
       venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def]
QED
Resume intcall_return_stmt_state_rel[immutable]:
  `immutable_metadata_frame (es1 with scopes := prev) (out with scopes := prev)` by
    (qpat_x_assum `intcall_callee_src _ _ _ _ _ _ = _` mp_tac >>
     simp[bodyIntCallSeamsTheory.intcall_callee_src_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
          vyperStateTheory.try_def, AllCaseEqs()] >>
     rpt strip_tac >>
     drule (cj 2 eval_metadata_frame_mutual) >>
     qpat_x_assum `unlock_if_nr _ _ _ _ = _` mp_tac >>
     gvs[vyperInterpreterTheory.unlock_if_nr_def,
         vyperInterpreterTheory.lock_if_nr_def,
         vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, vyperStateTheory.check_not_static_def,
         vyperStateTheory.check_def, vyperStateTheory.assert_def, AllCaseEqs()] >>
     rpt strip_tac >>
     TRY (rename1 `handle_function ex st = _` >> Cases_on `ex` >>
          gvs[vyperInterpreterTheory.handle_function_def,
              vyperStateTheory.return_def, vyperStateTheory.raise_def]) >>
     Cases_on `nr` >>
     Cases_on `cx.nonreentrant_slot` >>
     Cases_on `mut = View \/ mut = Pure` >>
     gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, vyperStateTheory.assert_def, AllCaseEqs()] >>
     imp_res_tac vyperStatePreservationTheory.acquire_nonreentrant_lock_immutables >>
     imp_res_tac vyperStatePreservationTheory.release_nonreentrant_lock_immutables >>
     gvs[immutable_metadata_frame_def] >> metis_tac[]) >>
  `!nm tv iv. FLOOKUP
     (case ALOOKUP out.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
     ?old. FLOOKUP
     (case ALOOKUP es1.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,old)` by
    (gvs[immutable_metadata_frame_def] >> rpt strip_tac >>
     Cases_on `ALOOKUP out.immutables cx.txn.target` >> gvs[] >>
     rename1 `FLOOKUP (get_source_immutables cenv.ce_module out_imms) nm =
                SOME (tv,iv)` >>
     Cases_on `ALOOKUP es1.immutables cx.txn.target` >> gvs[] >>
     qpat_x_assum `!addr. IS_SOME _ <=> _`
       (qspec_then `cx.txn.target` mp_tac) >> simp[] >>
     rename1 `?old. FLOOKUP (get_source_immutables cenv.ce_module entry_imms)
                        nm = SOME (tv,old)` >>
     qpat_x_assum `!addr imms imms' src id. _`
       (qspecl_then [`cx.txn.target`,`entry_imms`,`out_imms`,
                     `cenv.ce_module`,`nm`] mp_tac) >>
     simp[] >>
     Cases_on `FLOOKUP (get_source_immutables cenv.ce_module entry_imms) nm`
     >- simp[] >>
     rename1 `FLOOKUP (get_source_immutables cenv.ce_module entry_imms) nm =
                SOME entry_cell` >>
     PairCases_on `entry_cell` >> simp[]) >>
  `!id b sz. local_region cenv prev returned id b sz ==>
             local_region cenv prev t id b sz` by
    (simp[loweringStateRelDefsTheory.local_region_def] >> rpt strip_tac >>
     `~MEM p outs` by
       (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  drule return_stmt_immutable_sep >> simp[immutable_alloca_sep_def] >>
  strip_tac >>
  conj_tac
  >- (gvs[immutable_decl_sep_alt] >> metis_tac[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  metis_tac[]
QED
Resume intcall_return_stmt_state_rel[fmp]:
  qspecl_then [`ZIP (outs, ir.iret_values)`,
    `adopt_return_fmp ir (merge_callee_state t cs)`]
    strip_assume_tac foldl_update_var_frame >>
  `returned = (adopt_return_fmp ir (merge_callee_state t cs)) with vs_vars := vars` by
    (fs[venomExecSemanticsTheory.bind_outputs_def] >> metis_tac[]) >>
  simp[venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def] >>
  metis_tac[step_inst_memory_length]
QED
Resume intcall_return_stmt_state_rel[base]:
  qspecl_then [`ZIP (outs, ir.iret_values)`,
    `adopt_return_fmp ir (merge_callee_state t cs)`]
    strip_assume_tac foldl_update_var_frame >>
  `returned = (adopt_return_fmp ir (merge_callee_state t cs)) with vs_vars := vars` by
    (fs[venomExecSemanticsTheory.bind_outputs_def] >> metis_tac[]) >>
  irule immutable_base_zero_frame >> qexists `t` >>
  simp[venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def] >>
  reverse conj_tac >-
    (qhdtm_assum `stmt_state_rel`
       (ACCEPT_TAC o cj 6 o PURE_REWRITE_RULE [stmt_state_rel_def])) >>
  rpt strip_tac >>
  `~MEM x outs` by
    (fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_x_assum `!x. ~MEM x outs ==> lookup_var x returned = _` drule >>
  simp[venomExecSemanticsTheory.adopt_return_fmp_def,
       venomExecSemanticsTheory.merge_callee_state_def]
QED
Finalise intcall_return_stmt_state_rel
