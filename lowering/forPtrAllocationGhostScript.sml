(* Allocation can taint a new site, but no live local overlaps that site. *)
Theory forPtrAllocationGhost
Ancestors forPtrAllocation allocationPtr exprSimPtrLiteralBuffer
  robustCopyTransportPtr bodyPtrDefs exprSimProps compileEnv localPtrsProps
  venomState venomInst venomExecSemantics finite_map stmtSimDeclPath
  loweringPosts ptrDiscipline exprLoweringProps

Theorem for_local_value_region:
  stmt_state_rel ctx fn cenv cx es s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  val_footprint entry.type entry.value <= sz /\
  local_region cenv es.scopes s name (w2n w) sz
Proof
  strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  fs[local_ptrs_rel_def] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    metis_tac[] >>
  drule val_footprint_le >> simp[local_region_def] >> metis_tac[]
QED

Theorem for_alloca_local_robust:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_var p s = SOME w /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem) ==>
  !mem. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem
    u.vs_memory mem ==> val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >> drule_all for_local_value_region >> strip_tac >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  `regions_disjoint b n (w2n w) sz` by
    (irule for_alloca_outer_local_disjoint >> simp[] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def] >>
     simp[GSYM mk_inst_def] >> strip_tac >>
     drule exec_alloca_memory >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >> simp[] >>
  qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn).t_mem`,
    `{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac
  >- (fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >> conj_tac
  >- (fs[regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `mem_agree_outside _ _ mem` mp_tac >> simp[]
QED

Theorem for_alloca_ghost_inv:
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  (!q. cenv.ce_return_buf <> SOME (PtrVar (Var out) q)) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  ghost_inv d cenv cx es G tn s ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u
Proof
  strip_tac >> fs[ghost_inv_def] >> rpt conj_tac
  >- suspend "locals"
  >- suspend "buffer"
  >- suspend "pc" >>
  irule alloca_step_stor_taint_ok >> simp[] >> metis_tac[]
QED

Resume for_alloca_ghost_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by (fs[not_local_ptr_def] >> metis_tac[]) >>
  `lookup_var p u = lookup_var p s` by
    (drule_at (Pat `step_inst_base _ _ = _`) alloca_step_operand_preserved >>
     disch_then (qspec_then `Var p` mp_tac) >> simp[eval_operand_def]) >>
  conj_tac
  >- (irule alloca_step_old_ptr_covers >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory entry.type entry.value (w2n w) m` by
    (qpat_x_assum `!name entry p sz. _` drule_all >> simp[]) >>
  drule_all for_alloca_local_robust >> simp[]
QED

Resume for_alloca_ghost_inv[buffer]:
  Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
  fs[return_buf_ptr_def] >>
  rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot_size)` >>
  `rp <> out` by metis_tac[] >> conj_tac
  >- (drule_at (Pat `step_inst_base _ _ = _`) alloca_step_operand_preserved >>
      disch_then (qspec_then `Var rp` mp_tac) >> simp[eval_operand_def]) >>
  irule alloca_step_old_ptr_covers >> simp[] >> metis_tac[]
QED

Resume for_alloca_ghost_inv[pc]:
  rpt gen_tac >> strip_tac >> Cases_on `x = out`
  >- (gvs[] >> drule_all literal_ptr_alloca_ghost >>
      disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
      simp[op_taint_def, FLOOKUP_UPDATE]) >>
  drule_all forPtrAdminTheory.alloca_old_variable_ghost_frame >> simp[]
QED

Finalise for_alloca_ghost_inv
