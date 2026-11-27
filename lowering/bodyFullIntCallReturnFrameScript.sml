(* Caller-local boundaries used by the joint internal-call return frame. *)
Theory bodyFullIntCallReturnFrame
Ancestors
  bodyInvSplit bodyInvCodeProps immutableRegionTypingProps immutableRegionDeadProps
  exprSimHypsDefs bodySim bodyFullIntCallDefs exprLoweringProps ctorDeployDeadSection
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

Theorem intcall_immutable_decl_metadata_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods src name off bytes ==>
  FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
  ?ty tv. cenv.ce_module_var_type (src,name) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ bytes = type_memory_size tv
Proof
  strip_tac >> drule_all_then strip_assume_tac immutable_region_mods_type >>
  drule_then assume_tac contract_inv_immutable_section_layout >>
  fs[immutable_section_layout_mods_def] >> metis_tac[]
QED

Theorem intcall_evaluated_immutable_coverage_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  i < imm_len_mods mods ==>
  ?src name off ty tv.
    immutable_region_mods mods src name off (type_memory_size tv) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,name) = SOME ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    off <= i /\ i < off + type_memory_size tv
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_immutable_section_layout >>
  `?src name off bytes. immutable_region_mods mods src name off bytes /\
      off <= i /\ i < off + bytes` by fs[immutable_section_layout_mods_def] >>
  drule_all_then strip_assume_tac intcall_immutable_decl_metadata_mods >>
  metis_tac[]
QED

Theorem intcall_immutable_region_disjoint[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ immutable_region_mods mods src id off bytes /\
  immutable_decl_sep_mods cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  (local_region cenv scopes t name b sz \/ FLOOKUP t.vs_allocas aid = SOME (b,sz)) ==>
  regions_disjoint off bytes b sz
Proof
  REWRITE_TAC [GSYM AND_IMP_INTRO] >> rpt disch_tac >>
  drule_all_then strip_assume_tac intcall_immutable_decl_metadata_mods >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `?tops. ALOOKUP mods src = SOME tops` by
    fs[immutable_region_mods_def] >>
  qpat_x_assum `immutable_decl_sep_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [immutable_decl_sep_mods_def]) >>
  disch_then (qspecl_then [`src`, `tops`] mp_tac) >>
  simp[immutable_decl_sep_alt] >> disch_then drule >>
  simp[loweringStateRelDefsTheory.local_region_def] >>
  fs[loweringStateRelDefsTheory.local_region_def] >> metis_tac[]
QED

Theorem intcall_local_immutable_dead_disjoint_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep_mods cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  local_region cenv scopes t name b sz /\ b <= i /\ i < b + sz ==>
  ~imm_section_dead_mods cenv sec i
Proof
  rpt strip_tac >>
  drule_all_then (fn th => fs[th]) imm_section_dead_mods_regions >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (irule intcall_immutable_region_disjoint >> rpt (goal_assum (drule_at Any)) >>
     qexistsl [`ARB`, `name`] >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
  drule (cj 1 mem_dead_bytes_range) >> decide_tac
QED

Theorem intcall_local_immutable_prefix_disjoint_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep_mods cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  local_region cenv scopes t name b sz /\ b <= i /\ i < b + sz ==>
  imm_len_mods mods <= i
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `i < imm_len_mods mods` by decide_tac >>
  drule_all_then strip_assume_tac intcall_evaluated_immutable_coverage_mods >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (irule intcall_immutable_region_disjoint >> rpt (goal_assum (drule_at Any)) >>
     qexistsl [`ARB`, `name`] >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_alloca_immutable_prefix_disjoint_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep_mods cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz ==>
  imm_len_mods mods <= i
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `i < imm_len_mods mods` by decide_tac >>
  drule_all_then strip_assume_tac intcall_evaluated_immutable_coverage_mods >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (irule intcall_immutable_region_disjoint >> rpt (goal_assum (drule_at Any)) >>
     qexistsl [`aid`, `ARB`] >> simp[]) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem intcall_immutable_sep_singleton[local]:
  body_inv tops ctx cenv cx /\
  immutable_decl_sep cenv cx scopes vars allocas next ==>
  immutable_decl_sep_mods cenv cx scopes vars allocas next
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then strip_assume_tac body_inv_module_locations >>
  `cenv with ce_module := NONE = cenv` by
    (simp[compileEnvTheory.compile_env_component_equality] >>
     qpat_assum `cenv.ce_module = NONE` (fn th => simp[th])) >>
  fs[immutable_decl_sep_mods_def, ALOOKUP_def, AllCaseEqs()]
QED

Theorem intcall_local_immutable_prefix_disjoint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx tenv es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  local_region cenv scopes t name b sz /\ b <= i /\ i < b + sz ==>
  imm_len (cx_tops cx) <= i
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_all_then assume_tac intcall_immutable_sep_singleton >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx tenv es` by fs[expr_sim_inv_split_def] >>
  drule_all_then mp_tac intcall_local_immutable_prefix_disjoint_mods >>
  simp[imm_len_mods_singleton]
QED

Theorem intcall_alloca_immutable_prefix_disjoint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx tenv es /\
  cenv.ce_is_ctor /\
  immutable_decl_sep cenv cx scopes t.vs_vars t.vs_allocas t.vs_alloca_next /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz ==>
  imm_len (cx_tops cx) <= i
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then strip_assume_tac body_inv_main_code >>
  drule_all_then assume_tac intcall_immutable_sep_singleton >>
  `expr_sim_inv_mods [(NONE,tops)] cenv cx tenv es` by fs[expr_sim_inv_split_def] >>
  drule_all_then mp_tac intcall_alloca_immutable_prefix_disjoint_mods >>
  simp[imm_len_mods_singleton]
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
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `!sec j. imm_section_dead_mods cenv sec j <=> imm_section_dead tops sec j` by
    (rpt gen_tac >>
     qpat_x_assum `cenv.ce_modules = [(NONE,tops)]`
       (fn th => ACCEPT_TAC (MATCH_MP imm_section_dead_mods_singleton th))) >>
  drule_then strip_assume_tac body_inv_main_code >>
  `imm_len_mods cenv.ce_modules = imm_len (cx_tops cx)` by
    simp[imm_len_mods_singleton] >>
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
    (rpt strip_tac >> fs[dead_lo_ok_def, imm_len_mods_singleton] >>
     Cases_on `cenv.ce_is_ctor` >> gvs[] >>
     drule_all (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] intcall_local_immutable_prefix_disjoint) >> simp[]) >>
  `mem_bytes_at (w2n w) sz cs.vs_memory = mem_bytes_at (w2n w) sz t.vs_memory` by
    (Cases_on `sz = 0` >- gvs[valueEncodingDefsTheory.mem_bytes_at_def] >>
     `cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= w2n w` by
       (strip_tac >>
        qpat_x_assum `!i. w2n w <= i /\ _ ==> lo <= i`
          (qspec_then `w2n w` mp_tac) >>
        gvs[dead_lo_ok_def, imm_len_mods_singleton]) >>
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
  fs[intcall_callee_exit_full_def] >>
  first_x_assum (qspec_then `mem_bytes_at 0 lo cs.vs_memory` assume_tac) >>
  first_x_assum (qspec_then `i` assume_tac) >>
  metis_tac[]
QED

Resume intcall_return_ghost_inv[base]:
  rpt strip_tac >>
  `not_fresh_at sa x` by
    fs[loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
  `~MEM x outs` by metis_tac[] >>
  gvs[ghost_inv_at_def, op_taint_def, FLOOKUP_DRESTRICT]
QED

Finalise intcall_return_ghost_inv

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
*)
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
  cheat
QED
(* SCRATCH MEASUREMENT: original continuation.
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
     drule_all intcall_alloca_immutable_prefix_disjoint >> simp[]) >>
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
*)
(* SCRATCH MEASUREMENT: original continuation.
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
*)
(* SCRATCH MEASUREMENT: original continuation.
Finalise intcall_return_ghost_kept
*)

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
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
*)
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
  cheat
QED
(* SCRATCH MEASUREMENT: original continuation.
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
*)
(* SCRATCH MEASUREMENT: original continuation.
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
*)
(* SCRATCH MEASUREMENT: original continuation.
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
*)
(* SCRATCH MEASUREMENT: original continuation.
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
*)
(* SCRATCH MEASUREMENT: original continuation.
Finalise intcall_return_stmt_state_rel
*)
