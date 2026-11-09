(* Fresh allocation and the ghost boundary for pointer-safe encoders. *)
Theory allocationPtr
Ancestors
  loweringHalt bodyPtrDefs loweringPosts exprSimDefs exprSimProps exprLoweringProps ptrDiscipline
  venomMemDefs venomExecSemantics venomInst finite_map compileEnv loweringStateRelDefs venomState localPtrsProps

(* A zero-footprint value need not be allocated at all.  Every byte of a
   positive footprint, however, lies strictly below the allocation frontier. *)
Theorem expr_val_at_below_frontier:
  !ctx func cenv cx t sa sb es v op s tv w i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w /\
    w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    i < s.vs_alloca_next
Proof
  rw[expr_val_at_def] >> first_x_assum (qspec_then `tv` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >- (fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
     local_region_def] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >> decide_tac
QED

Theorem fresh_alloca_new_site_bytes:
  !id n out s s1.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    new_site_bytes s s1 =
      {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n}
Proof
  rpt strip_tac >> drule_all step_alloca_fresh >> strip_tac >> gvs[] >>
  rw[new_site_bytes_def, update_var_def, FLOOKUP_UPDATE,
     pred_setTheory.EXTENSION] >>
  gvs[AllCaseEqs(), FLOOKUP_DEF] >>
  eq_tac
  >- (strip_tac >> gvs[] >> decide_tac) >>
  strip_tac >> qexistsl [`id`, `s.vs_alloca_next`, `n`] >> simp[]
QED

Theorem fresh_alloca_ghost:
  !id n out s s1 PG G tn.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1 =
      G |+ (out, (s.vs_alloca_next,n)) /\
    step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn =
      tn with <| t_mem := tn.t_mem UNION
                     {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n};
                 t_var := tn.t_var |+ (out,{}) |>
Proof
  rpt strip_tac >>
  drule_all fresh_alloca_new_site_bytes >> strip_tac >>
  drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       update_var_def, FLOOKUP_UPDATE, step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, imm_taint_def, adopt_reset_def,
       new_site_bytes_def, pred_setTheory.EXTENSION] >>
  simp[taint_component_equality]
QED

Theorem fresh_alloca_ptr_covers:
  !id n out s s1 PG G tn p sz.
    FLOOKUP s.vs_allocas id = NONE /\
    s.vs_alloca_next + n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
      out s1 n /\
    (p <> out /\ ptr_covers G tn p s sz ==>
      ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn)
        p s1 sz)
Proof
  rpt gen_tac >> strip_tac >>
  `n < dimword (:256)` by decide_tac >>
  `s.vs_alloca_next < dimword (:256)` by decide_tac >>
  drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> gvs[ptr_covers_def, op_taint_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem fresh_alloca_taint_below_frontier:
  !id n out s s1 tn i.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    i < s.vs_alloca_next ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
     <=> i IN tn.t_mem)
Proof
  rpt strip_tac >> drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  simp[]
QED

Theorem fresh_alloca_stor_taint_ok:
  !id n out s s1 tn cx.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    stor_taint_ok cx tn s ==>
    stor_taint_ok cx
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  rpt strip_tac >> drule_all fresh_alloca_ghost >>
  disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
  simp[] >> disch_then (qspec_then `out` assume_tac) >>
  gvs[stor_taint_ok_def, update_var_def]
QED

Theorem fresh_alloca_old_region_disjoint:
  !id n out s s1 aid b sz i.
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    alloca_inv s /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    b <= i /\ i < b + sz ==>
    i NOTIN new_site_bytes s s1
Proof
  rpt strip_tac >> drule_all fresh_alloca_new_site_bytes >> strip_tac >>
  simp[] >> fs[alloca_inv_def, alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem fresh_alloca_expr_read_clean:
  !ctx func cenv cx t sa sb es v op s tv w id n out s1 tn i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w /\
    FLOOKUP s.vs_allocas id = NONE /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    w2n w <= i /\ i < w2n w + val_footprint tv v /\ i NOTIN tn.t_mem ==>
    i NOTIN
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
Proof
  rpt strip_tac >>
  `i < s.vs_alloca_next` by (drule_all expr_val_at_below_frontier >> simp[]) >>
  drule_all fresh_alloca_taint_below_frontier >>
  disch_then (qspec_then `tn` mp_tac) >> simp[]
QED

Theorem reused_alloca_step:
  !id n out s b.
    FLOOKUP s.vs_allocas id = SOME (b,n) ==>
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s =
      OK (update_var out (n2w b) s)
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def]
QED

Theorem reused_alloca_ghost:
  !id n out s b PG G tn.
    FLOOKUP s.vs_allocas id = SOME (b,n) ==>
    new_site_bytes s (update_var out (n2w b) s) = {} /\
    step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (update_var out (n2w b) s) = G |+ (out,(b,n)) /\
    step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn = tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt strip_tac >>
  `new_site_bytes s (update_var out (n2w b) s) = {}` by
    (rw[new_site_bytes_def, update_var_def, pred_setTheory.EXTENSION] >>
     gvs[FLOOKUP_DEF]) >>
  simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def,
       update_var_def, step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       range_bytes_def, written_taint_def, set_var_taint_def, out_taint_def,
       eval_operand_def, store_taint_def, imm_taint_def, adopt_reset_def,
       taint_component_equality]
QED

Theorem reused_alloca_ptr_covers:
  !id n out s b PG G tn p sz.
    FLOOKUP s.vs_allocas id = SOME (b,n) /\ b + n < dimword (:256) ==>
    ptr_covers
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
        (update_var out (n2w b) s))
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
        (update_var out (n2w b) s) tn) out (update_var out (n2w b) s) n /\
    (p <> out /\ ptr_covers G tn p s sz ==>
      ptr_covers
        (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out])
          (update_var out (n2w b) s))
        (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
          (update_var out (n2w b) s) tn) p (update_var out (n2w b) s) sz)
Proof
  rpt gen_tac >> strip_tac >> `b < dimword (:256)` by decide_tac >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[ptr_covers_def, op_taint_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> gvs[ptr_covers_def, op_taint_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem reused_alloca_stor_taint_ok:
  !id n out s b tn cx.
    FLOOKUP s.vs_allocas id = SOME (b,n) /\ stor_taint_ok cx tn s ==>
    stor_taint_ok cx
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
        (update_var out (n2w b) s) tn) (update_var out (n2w b) s)
Proof
  rpt strip_tac >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  gvs[stor_taint_ok_def, update_var_def]
QED

Theorem reused_alloca_memory_taint:
  !id n out s b tn.
    FLOOKUP s.vs_allocas id = SOME (b,n) ==>
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s
      (update_var out (n2w b) s) tn).t_mem = tn.t_mem
Proof
  rpt strip_tac >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
  simp[]
QED

Theorem expr_val_at_alloca_disjoint:
  !ctx func cenv cx t sa sb es v op s tv w inst out b n i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [out] /\
    not_local_ptr cenv es.scopes out /\
    (inst.inst_id < sa.cs_next_id \/ sb.cs_next_id <= inst.inst_id) /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
    w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    ~(b <= i /\ i < b+n)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (`aid <> inst.inst_id` by decide_tac >>
      fs[stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def] >>
      first_x_assum drule_all >> decide_tac)
  >- (fs[stmt_state_rel_def, state_rel_def] >>
      drule_all local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def] >> decide_tac)
  >- (`aid <> inst.inst_id` by decide_tac >>
      fs[stmt_state_rel_def, alloca_inv_def, allocas_non_overlapping_def] >>
      first_x_assum drule_all >> decide_tac) >>
  fs[stmt_state_rel_def, state_rel_def] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem stmt_state_rel_alloca_site_bound:
  !ctx func cenv cx es s id n out b sz.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    sz = n /\ b + n < dimword (:256)
Proof
  rpt strip_tac >>
  `sz = n` by
    (fs[stmt_state_rel_def] >> first_x_assum drule >>
     simp[mk_inst_def] >> disch_then drule >> simp[wordsTheory.w2n_n2w]) >>
  gvs[] >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
  qpat_x_assum `!aid base sz. FLOOKUP _ _ = SOME _ ==> _`
    drule >> decide_tac
QED

Theorem stmt_state_rel_alloca_fresh_bound:
  !ctx func cenv cx es s id n out.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ FLOOKUP s.vs_allocas id = NONE ==>
    s.vs_alloca_next + n < dimword (:256)
Proof
  rpt strip_tac >>
  `id NOTIN FDOM s.vs_allocas` by fs[FLOOKUP_DEF] >>
  fs[stmt_state_rel_def] >> drule alloca_room_fresh >>
  disch_then (qspecl_then
    [`mk_inst id ALLOCA [Lit (n2w n)] [out]`, `n2w n`] mp_tac) >>
  simp[mk_inst_def, wordsTheory.w2n_n2w]
QED

Theorem alloca_step_site:
  !ctx func cenv cx es s id n out s1.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    ?b. FLOOKUP s1.vs_allocas id = SOME (b,n) /\
        b + n < dimword (:256) /\
        eval_operand (Var out) s1 = SOME (n2w b)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
      simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem alloca_step_ptr_covers:
  !ctx func cenv cx es s id n out s1 PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) out s1 n
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all fresh_alloca_ptr_covers >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> irule (cj 1 reused_alloca_ptr_covers) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem alloca_step_old_ptr_covers:
  !ctx func cenv cx es s id n out s1 PG G tn p sz.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    p <> out /\ ptr_covers G tn p s sz ==>
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) p s1 sz
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all stmt_state_rel_alloca_fresh_bound >> strip_tac >>
      drule_all fresh_alloca_ptr_covers >>
      disch_then (qspecl_then [`PG`, `G`, `tn`, `p`, `sz`] mp_tac) >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> irule (cj 2 reused_alloca_ptr_covers) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem alloca_step_stor_taint_ok:
  !ctx func cenv cx es s id n out s1 tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    stor_taint_ok cx tn s ==>
    stor_taint_ok cx
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (irule fresh_alloca_stor_taint_ok >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> irule reused_alloca_stor_taint_ok >> simp[]
QED

Theorem alloca_step_expr_read_clean:
  !ctx func cenv cx t sa sb es v op s tv w id n out s1 tn i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    w2n w <= i /\ i < w2n w + val_footprint tv v /\ i NOTIN tn.t_mem ==>
    i NOTIN
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_expr_read_clean >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[]
QED

Theorem alloca_step_expr_disjoint:
  !ctx func cenv cx t sa sb es v op s tv w id n out s1 b i.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    eval_operand op s = SOME w /\ fn_inst_ids_distinct func /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    not_local_ptr cenv es.scopes out /\
    (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    FLOOKUP s1.vs_allocas id = SOME (b,n) /\
    w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    ~(b <= i /\ i < b+n)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >>
      drule_all expr_val_at_below_frontier >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >>
  disch_then (map_every assume_tac o CONJUNCTS) >> gnvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gnvs[update_var_def] >>
  drule_at (Pat `MEM _ (fn_insts _)`) expr_val_at_alloca_disjoint >>
  disch_then (drule_all o SRULE [mk_inst_def]) >> simp[]
QED

Theorem alloca_step_operand_preserved:
  !s id n out s1 op.
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    (!p. op = Var p ==> p <> out) ==>
    eval_operand op s1 = eval_operand op s
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[] >> Cases_on `op` >>
      gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[] >> Cases_on `op` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED
