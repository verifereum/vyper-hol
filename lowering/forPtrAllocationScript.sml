(* Allocation-site separation includes re-execution of an existing site. *)
Theory forPtrAllocation
Ancestors forPtrAdmin allocationPtr localPtrsProps loweringHalt
  exprLoweringProps compileEnv venomInst venomState finite_map

Theorem for_alloca_outer_local_disjoint:
  stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  local_region cenv es.scopes s name lo sz /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  FLOOKUP u.vs_allocas id = SOME (b,n) ==>
  regions_disjoint b n lo sz
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all step_alloca_fresh >> strip_tac >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      `local_ptrs_rel fn cenv es.scopes s` by
        fs[stmt_state_rel_def, state_rel_def] >>
      drule local_ptrs_rel_above_frontier >>
      disch_then drule >>
      disch_then (qspecl_then [`s.vs_alloca_next`, `n`] mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[update_var_def] >>
  irule local_ptrs_rel_alloca_disjoint >>
  qexistsl [`cenv`, `fn`, `mk_inst id ALLOCA [Lit (n2w n)] [out]`,
            `name`, `out`, `es.scopes`, `s`] >>
  simp[mk_inst_def] >> fs[stmt_state_rel_def, state_rel_def]
QED

(* Layout and non-local-output premises remain explicit: neither says that
   this allocation site has not already executed. *)
Theorem for_alloca_slot_path_ptr:
  stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  not_local_ptr cenv es.scopes out /\ n < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst id ALLOCA [Lit (n2w n)] [out]) /\
  local_region cenv es.scopes s name lo sz /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx)) /\
  ptr_covers
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
    out (u with vs_inst_idx := SUC s.vs_inst_idx) n /\
  (?b. FLOOKUP u.vs_allocas id = SOME (b,n) /\
       b + n < dimword (:256) /\
       eval_operand (Var out) u = SOME (n2w b) /\
       regions_disjoint b n lo sz) /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u) p =
      FLOOKUP G p /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
      (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all alloca_zero_path_ptr_covered >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  simp[] >>
  conj_tac
  >- (drule_all alloca_step_site >> strip_tac >>
      qexists `b` >> simp[] >>
      irule for_alloca_outer_local_disjoint >> simp[] >> metis_tac[]) >>
  gen_tac >> disch_tac >> drule_all alloca_old_variable_ghost_frame >>
  simp[]
QED
