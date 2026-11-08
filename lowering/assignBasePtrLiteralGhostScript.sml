(* Ghost transport for the actual allocating literal producer. *)
Theory assignBasePtrLiteralGhost
Ancestors wordLoadStorePtr assignBasePtrLiteralPost typedCopyPtr robustCopyTransportPtr
  allocationPtr loweringHalt exprLoweringProps localPtrsProps bodyPtrDefs ptrDiscipline venomInst venomExecSemantics
  venomState valueEncodingProps exprSimProps compileEnv finite_map pred_set
  fragGasSeqPtr ghostPcTransportPtr instIdxIndep representationCleanPtr
  emitHelperProps words exprSimMemoryTransport venomMemProofs list valueEncodingProofs

Theorem assign_base_ptr_mstore_imm_taint[local]:
  !tn s id dst value a w.
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_imm = tn.t_imm
Proof
  rpt gen_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def]
QED

(* A live local cannot observe changes confined to a disjoint write set.
   The existing exterior-frame theorem constructs the comparison-memory
   witness; no global containment of the new taint is assumed. *)
Theorem assign_base_ptr_local_robust_frame:
  !func cenv cx es d G tn s tn' t writes name entry p sz w mem.
    local_ptrs_rel func cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
    (!name b sz i. local_region cenv es.scopes s name b sz /\
      b <= i /\ i < b + sz ==> i NOTIN writes) /\
    (!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ mem_agree_outside tn'.t_mem t.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> first_x_assum drule_all >> simp[]) >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
  simp[] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b sz i. _`
        (qspecl_then [`name`, `w2n w`, `sz`, `i`] mp_tac) >> simp[] >> decide_tac) >>
  fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]
QED

Theorem assign_base_ptr_clean_mstore_inv:
  !func d cenv cx es PG G tn s id dst value a w.
    local_ptrs_rel func cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n a) 32 b sz) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
      (mstore (w2n a) w s)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `ghost_inv d cenv cx es G tn' t` >>
  `tn'.t_imm = tn.t_imm` by simp[Abbr `tn'`, Abbr `t`, assign_base_ptr_mstore_imm_taint] >>
  `!x. op_taint tn' (Var x) = op_taint tn (Var x)` by
    simp[Abbr `tn'`, op_taint_def] >>
  `!x. lookup_var x t = lookup_var x s` by simp[Abbr `t`, mstore_def, lookup_var_def] >>
  `!p sz. ptr_covers G tn p s sz ==> ptr_covers G tn' p t sz` by
    simp[ptr_covers_def] >>
  rewrite_tac[ghost_inv_def] >> conj_tac
  >- suspend "locals" >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_def] >> strip_tac >> conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >>
      PairCases_on `x` >> fs[return_buf_ptr_def] >> metis_tac[]) >>
  gvs[stor_taint_ok_def, Abbr `t`, mstore_def]
QED

Resume assign_base_ptr_clean_mstore_inv[locals]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (fs[ghost_inv_def] >> first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `writes = {i | w2n a <= i /\ i < w2n a + 32}` >>
  `!name b sz i. local_region cenv es.scopes s name b sz /\
     b <= i /\ i < b + sz ==> i NOTIN writes` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!name b sz. _`
       (qspecl_then [`name'`, `b`, `sz'`] mp_tac) >>
     simp[Abbr `writes`, regions_disjoint_def] >> decide_tac) >>
  `!i. i NOTIN writes ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[Abbr `t`] >> irule mstore_mem_bytes_at_disjoint >>
     fs[Abbr `writes`] >> decide_tac) >>
  `!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    simp[Abbr `tn'`, Abbr `writes`] >>
  `lookup_var p s = SOME w'` by metis_tac[] >>
  drule_all assign_base_ptr_local_robust_frame >> simp[]
QED

Finalise assign_base_ptr_clean_mstore_inv

(* Allocation changes only its output variable and the taint of newly
   allocated bytes. Re-executing a site introduces no new memory taint. *)
Theorem assign_base_ptr_alloca_ghost_frame:
  !ctx func cenv cx es s id n out t PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    t.vs_memory = s.vs_memory /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t) x = FLOOKUP G x /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) (Var x) = op_taint tn (Var x)) /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem =
      tn.t_mem UNION new_site_bytes s t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule_all fresh_alloca_new_site_bytes >> strip_tac >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
      simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `PG`, `G`, `tn`] strip_assume_tac) >>
  simp[update_var_def, lookup_var_def, op_taint_def, FLOOKUP_UPDATE]
QED

Theorem assign_base_ptr_alloca_local_taint_frame:
  !ctx func cenv cx es s id n out t name b sz i.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    local_region cenv es.scopes s name b sz /\ b <= i /\ i < b + sz ==>
    i NOTIN new_site_bytes s t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_new_site_bytes >> strip_tac >>
      `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
      `regions_disjoint b sz s.vs_alloca_next n` by
        (irule local_ptrs_rel_above_frontier >>
         qexistsl_tac [`cenv`, `func`, `name`, `es.scopes`, `s`] >> simp[]) >>
      fs[regions_disjoint_def] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `ARB`] strip_assume_tac) >> simp[]
QED

Theorem assign_base_ptr_alloca_inv:
  !ctx func d cenv cx es s id n out t PG G tn.
    stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ not_local_ptr cenv es.scopes out /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) t
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_alloca_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ghost_inv d cenv cx es G' tn' t` >>
  `!p sz. p <> out /\ ptr_covers G tn p s sz ==> ptr_covers G' tn' p t sz` by
    (rpt strip_tac >> simp[Abbr `G'`, Abbr `tn'`] >>
     irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  rewrite_tac[ghost_inv_def] >> conj_tac >- suspend "locals" >>
  qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_inv_def] >> strip_tac >> conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  simp[Abbr `tn'`] >> irule alloca_step_stor_taint_ok >> metis_tac[]
QED

Resume assign_base_ptr_alloca_inv[locals]:
  rpt gen_tac >> strip_tac >>
  `p <> out` by (fs[not_local_ptr_def] >> metis_tac[]) >>
  conj_tac >- (fs[ghost_inv_def] >> first_x_assum drule_all >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `!name b sz i. local_region cenv es.scopes s name b sz /\
    b <= i /\ i < b + sz ==> i NOTIN new_site_bytes s t` by
    (rpt gen_tac >> strip_tac >> drule_all assign_base_ptr_alloca_local_taint_frame >> simp[]) >>
  `!i. i NOTIN new_site_bytes s t ==> (i IN tn'.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!i. i NOTIN new_site_bytes s t ==>
    mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory` by simp[] >>
  drule_all assign_base_ptr_local_robust_frame >> simp[]
QED

Finalise assign_base_ptr_alloca_inv

Theorem assign_base_ptr_alloca_old_taint_frame:
  !ctx func cenv cx es s id n out t aid b sz i.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ b <= i /\ i < b + sz ==>
    i NOTIN new_site_bytes s t
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (`alloca_inv s` by fs[stmt_state_rel_def] >>
      drule_all fresh_alloca_old_region_disjoint >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`, `[]`, `FEMPTY`, `ARB`] strip_assume_tac) >> simp[]
QED

Theorem assign_base_ptr_alloca_kept:
  !ctx func cenv cx es s sa id n out t PG G tn.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    n < dimword (:256) /\ (!x. not_fresh_at sa x ==> x <> out) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_ptr_alloca_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  simp[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >>
      `i NOTIN new_site_bytes s t` by
        (drule_all assign_base_ptr_alloca_old_taint_frame >> simp[]) >> fs[]) >>
  rpt strip_tac >>
  `i NOTIN new_site_bytes s t` by
    (drule_all assign_base_ptr_alloca_local_taint_frame >> simp[]) >> fs[]
QED

Theorem assign_base_ptr_clean_mstore_kept:
  !cenv es sa G0 tn0 s0 PG G tn s id dst value a w.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id MSTORE [Var dst; value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >> drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  fs[ghost_kept_def, op_taint_def] >> metis_tac[]
QED

Theorem assign_base_ptr_binop_imm_taint[local]:
  !tn s id opc left right out w.
    opc <> ISTORE ==>
    (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn).t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, store_taint_def,
       adopt_reset_def, step_writes_def, written_taint_def, imm_taint_def,
       mem_taint_def, update_var_def, new_site_bytes_def, FLOOKUP_DEF,
       EXTENSION, SF CONJ_ss]
QED

Theorem assign_base_ptr_binop_inv:
  !d cenv cx es PG G tn s id opc left right out w.
    ghost_inv d cenv cx es G tn s /\ (opc = ADD \/ opc = AND) /\
    not_local_ptr cenv es.scopes out /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> out) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> out) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out w s))
      (step_taint (mk_inst id opc [left;right] [out]) s (update_var out w s) tn)
      (update_var out w s)
Proof
  rpt gen_tac >> strip_tac >> (
  `opc <> ISTORE` by gvs[] >>
  qmatch_goalsub_abbrev_tac `ghost_inv d cenv cx es G' tn' t` >>
  `op_taint tn' (Var out) = {} /\ tn'.t_mem = tn.t_mem /\
   tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
   (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `G'`, Abbr `tn'`, Abbr `t`] >>
     irule copy_len_binop_ghost_frame >> simp[]) >>
  `!p. p <> out ==> lookup_var p t = lookup_var p s` by
    simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `!p sz. p <> out /\ ptr_covers G tn p s sz ==> ptr_covers G' tn' p t sz` by
    (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  rewrite_tac[ghost_inv_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> out` by (fs[not_local_ptr_def] >> metis_tac[]) >>
      fs[ghost_inv_def] >>
      qpat_x_assum `!name entry p sz. _` drule_all >> strip_tac >>
      conj_tac >- metis_tac[] >>
      simp[Abbr `t`, update_var_def] >> metis_tac[]) >>
  fs[ghost_inv_def] >> conj_tac
  >- (Cases_on `d` >> simp[return_buf_ptr_def] >> PairCases_on `x` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  `tn'.t_imm = tn.t_imm` by
    simp[Abbr `tn'`, Abbr `t`, assign_base_ptr_binop_imm_taint] >>
  fs[stor_taint_ok_def, Abbr `t`, update_var_def] >> metis_tac[])
QED

Theorem assign_base_ptr_binop_kept:
  !cenv es sa G0 tn0 s0 PG G tn s id opc left right out w.
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ (opc = ADD \/ opc = AND) /\
    (!x. not_fresh_at sa x ==> x <> out) ==>
    ghost_kept cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id opc [left;right] [out]) (update_var out w s))
      (step_taint (mk_inst id opc [left;right] [out]) s (update_var out w s) tn)
Proof
  rpt gen_tac >> strip_tac >> (
  qmatch_goalsub_abbrev_tac `ghost_kept cenv es sa G0 tn0 s0 G' tn'` >>
  `op_taint tn' (Var out) = {} /\ tn'.t_mem = tn.t_mem /\
   tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
   (!p. p <> out ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `G'`, Abbr `tn'`] >>
     irule copy_len_binop_ghost_frame >> simp[]) >>
  fs[ghost_kept_def] >> metis_tac[])
QED

Theorem assign_base_ptr_one_byte_init_clean:
  !D lo ctx func PG G tn s G' tn' p q a i j k.
    p <> q /\ lookup_var p s = SOME a /\ w2n a + 64 < dimword (:256) /\
    inst_seq_ptr D lo ctx func PG G tn
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s G' tn' ==>
    !b. w2n a <= b /\ b < w2n a + 64 ==> b NOTIN tn'.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = mstore (w2n a) 1w s` >>
  qabbrev_tac `v = update_var q (a + 32w) u` >>
  qabbrev_tac `t = mstore (w2n (a + 32w)) (n2w (2 ** 248)) v` >>
  `lookup_var p u = SOME a /\ lookup_var q v = SOME (a + 32w)` by
    (simp[Abbr `u`, Abbr `v`, lookup_var_def, mstore_def,
      update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `step_inst_base (mk_inst i MSTORE [Var p; Lit 1w] []) s = OK u` by
    (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j ADD [Var p; Lit 32w] [q]) u = OK v` by
    (simp[Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []) v = OK t` by
    (simp[Abbr `t`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  qabbrev_tac `tn1 = step_taint (mk_inst i MSTORE [Var p; Lit 1w] []) s u tn` >>
  qabbrev_tac `tn2 = step_taint (mk_inst j ADD [Var p; Lit 32w] [q]) u v tn1` >>
  `tn1.t_mem = tn.t_mem DIFF {b | w2n a <= b /\ b < w2n a + 32}` by
    (simp[Abbr `tn1`, Abbr `u`] >> irule (cj 5 mstore_ghost_frame) >>
     simp[eval_operand_def, op_taint_def]) >>
  `tn2.t_mem = tn1.t_mem` by
    (simp[NoAsms, Abbr `tn2`, Abbr `v`] >> irule (cj 2 copy_len_binop_ghost_frame) >> simp[]) >>
  `(step_taint (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []) v t tn2).t_mem =
     tn2.t_mem DIFF {b | w2n (a + 32w) <= b /\ b < w2n (a + 32w) + 32}` by
    (simp[NoAsms, Abbr `t`] >> irule (cj 5 mstore_ghost_frame) >>
     simp[eval_operand_def, op_taint_def]) >>
  `w2n (a + 32w) = w2n a + 32` by
    (irule EQ_TRANS >> qexists_tac `w2n a + w2n (32w:bytes32)` >>
     conj_tac >- (irule w2n_add_2 >> fs[dimword_def] >> decide_tac) >> simp[]) >>
  `~is_terminator (mk_inst j ADD [Var p; Lit 32w] [q]).inst_opcode /\
   ~is_terminator (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  fs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def,
     Abbr `tn1`, Abbr `tn2`] >>
  rpt strip_tac >> fs[] >> decide_tac
QED

(* Only the represented footprint must be clean, not the annotated buffer. *)
Theorem assign_base_ptr_clean_footprint_robust:
  !tv v p mem tn n.
    val_in_memory tv v p mem /\ val_wf tv v /\ val_footprint tv v <= n /\
    (!b. p <= b /\ b < p+n ==> b NOTIN tn) ==>
    !m. mem_agree_outside tn mem m ==> val_in_memory tv v p m
Proof
  rpt strip_tac >> irule val_in_memory_relocate_footprint >>
  conj_tac >- simp[] >> qexistsl_tac [`mem`, `p`] >> simp[] >>
  irule LIST_EQ >> simp[EL_mem_bytes_at] >> rpt strip_tac >>
  rename1 `i < val_footprint tv v` >>
  `p+i NOTIN tn` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (p+i) 1 mem = mem_bytes_at (p+i) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem assign_base_ptr_one_byte_init_robust:
  !D lo ctx func PG G tn s G' tn' t p q a i j k.
    p <> q /\ lookup_var p s = SOME a /\ w2n a + 64 < dimword (:256) /\
    run_inst_seq
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s = OK t /\
    inst_seq_ptr D lo ctx func PG G tn
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s G' tn' ==>
    !m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      val_in_memory (BaseTV (BytesT (Dynamic 64))) (BytesV [1w]) (w2n a) m
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `inst_seq_ptr`) assign_base_ptr_one_byte_init_clean >>
  simp[] >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_endpoint >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_memory >> strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic 64))) (BytesV [1w])
     (w2n a) t.vs_memory` by
    (irule assign_base_ptr_one_byte_value >> simp[]) >>
  rpt strip_tac >> irule assign_base_ptr_clean_footprint_robust >>
  conj_tac >- simp[valueEncodingTheory.val_wf_def, valueEncodingTheory.type_memory_size_def,
    vyperValueTheory.type_slot_size_def, vfmConstantsTheory.word_size_def] >>
  qexistsl_tac [`t.vs_memory`, `64`, `tn'.t_mem`] >>
  simp[valueEncodingTheory.val_wf_def, loweringPostsTheory.val_footprint_def]
QED

Theorem assign_base_ptr_one_byte_init_kept:
  !D lo ctx func PG G tn s G' tn' p q a i j k cenv es sa G0 tn0 s0.
    p <> q /\ lookup_var p s = SOME a /\
    (!x. not_fresh_at sa x ==> x <> q) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    inst_seq_ptr D lo ctx func PG G tn
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s G' tn' ==>
    ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = mstore (w2n a) 1w s` >>
  qabbrev_tac `v = update_var q (a + 32w) u` >>
  qabbrev_tac `t = mstore (w2n (a + 32w)) (n2w (2 ** 248)) v` >>
  `lookup_var p u = SOME a /\ lookup_var q v = SOME (a + 32w)` by
    (simp[Abbr `u`, Abbr `v`, lookup_var_def, mstore_def,
      update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `step_inst_base (mk_inst i MSTORE [Var p; Lit 1w] []) s = OK u` by
    (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j ADD [Var p; Lit 32w] [q]) u = OK v` by
    (simp[Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []) v = OK t` by
    (simp[Abbr `t`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `~is_terminator (mk_inst j ADD [Var p; Lit 32w] [q]).inst_opcode /\
   ~is_terminator (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  fs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Abbr `t`] >> irule assign_base_ptr_clean_mstore_kept >>
  simp[eval_operand_def, op_taint_def] >>
  simp[Abbr `v`] >> irule assign_base_ptr_binop_kept >> simp[] >>
  simp[Abbr `u`] >> irule assign_base_ptr_clean_mstore_kept >>
  simp[eval_operand_def, op_taint_def] >> qexists_tac `a` >> simp[]
QED

Theorem assign_base_ptr_one_byte_init_inv:
  !D lo ctx func PG G tn s G' tn' p q a i j k d cenv cx es.
    p <> q /\ lookup_var p s = SOME a /\ w2n a + 64 < dimword (:256) /\
    local_ptrs_rel func cenv es.scopes s /\ ghost_inv d cenv cx es G tn s /\
    not_local_ptr cenv es.scopes q /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> q) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> q) /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n a) 64 b sz) /\
    inst_seq_ptr D lo ctx func PG G tn
      [mk_inst i MSTORE [Var p; Lit 1w] [];
       mk_inst j ADD [Var p; Lit 32w] [q];
       mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []] s G' tn' ==>
    ghost_inv d cenv cx es G' tn'
      (mstore (w2n (a + 32w)) (n2w (2 ** 248))
        (update_var q (a + 32w) (mstore (w2n a) 1w s)))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = mstore (w2n a) 1w s` >>
  qabbrev_tac `v = update_var q (a + 32w) u` >>
  qabbrev_tac `t = mstore (w2n (a + 32w)) (n2w (2 ** 248)) v` >>
  `lookup_var p u = SOME a /\ lookup_var q v = SOME (a + 32w)` by
    (simp[Abbr `u`, Abbr `v`, lookup_var_def, mstore_def,
      update_var_def, FLOOKUP_UPDATE] >> fs[lookup_var_def]) >>
  `step_inst_base (mk_inst i MSTORE [Var p; Lit 1w] []) s = OK u` by
    (simp[Abbr `u`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst j ADD [Var p; Lit 32w] [q]) u = OK v` by
    (simp[Abbr `v`] >> irule step_ADD >> simp[eval_operand_def]) >>
  `step_inst_base (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []) v = OK t` by
    (simp[Abbr `t`] >> irule step_MSTORE >> simp[eval_operand_def]) >>
  `local_ptrs_rel func cenv es.scopes v /\
   (!name b sz. local_region cenv es.scopes v name b sz ==>
      regions_disjoint (w2n (a + 32w)) 32 b sz) /\
   (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n a) 32 b sz)` by suspend "frames" >>
  `~is_terminator (mk_inst j ADD [Var p; Lit 32w] [q]).inst_opcode /\
   ~is_terminator (mk_inst k MSTORE [Var q; Lit (n2w (2 ** 248))] []).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  fs[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  simp[Abbr `t`] >> irule assign_base_ptr_clean_mstore_inv >>
  simp[eval_operand_def, op_taint_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qexists_tac `func` >> simp[]) >>
  simp[Abbr `v`] >> irule assign_base_ptr_binop_inv >> simp[] >>
  simp[Abbr `u`] >> irule assign_base_ptr_clean_mstore_inv >>
  simp[eval_operand_def, op_taint_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `func` >> simp[]
QED

Resume assign_base_ptr_one_byte_init_inv[frames]:
  `w2n (a + 32w) = w2n a + 32` by
    (irule EQ_TRANS >> qexists_tac `w2n a + w2n (32w:bytes32)` >>
     conj_tac >- (irule w2n_add_2 >> fs[dimword_def] >> decide_tac) >> simp[]) >>
  `!name b sz. local_region cenv es.scopes v name b sz <=>
     local_region cenv es.scopes s name b sz` by
    (simp[local_region_def, Abbr `v`, Abbr `u`, lookup_var_def,
       update_var_def, mstore_def, FLOOKUP_UPDATE] >>
     fs[not_local_ptr_def] >> metis_tac[]) >>
  `!name b sz. local_region cenv es.scopes s name b sz ==>
     w2n a + 32 <= b \/ b + sz <= w2n a` by
    (rpt strip_tac >> first_x_assum drule >> simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (simp[Abbr `v`] >> irule local_ptrs_rel_update_var >>
      simp[not_local_ptr_scope] >> simp[Abbr `u`] >>
      irule local_ptrs_rel_mstore >> simp[] >> first_assum ACCEPT_TAC) >>
  simp[regions_disjoint_def] >> rpt strip_tac >>
  qpat_x_assum `!name b sz. _ ==> regions_disjoint _ _ _ _` drule >>
  simp[regions_disjoint_def] >> decide_tac
QED

Finalise assign_base_ptr_one_byte_init_inv

Theorem assign_base_ptr_one_byte_ptr_value:
  !cx cenv p a G tn t.
    lookup_var p t = SOME a /\ ptr_covers G tn p t 64 /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
      val_in_memory (BaseTV (BytesT (Dynamic 64))) (BytesV [1w]) (w2n a) m) ==>
    ptr_val_ok cx (BaseT (BytesT (Dynamic 64))) (BytesV [1w]) (Var p) G tn t /\
    ptr_buf_ok cenv (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [1w]))
      (Var p) G t
Proof
  rpt gen_tac >> strip_tac >> fs[ptr_covers_def] >> conj_tac
  >- (simp[ptr_val_ok_def, ptr_mem_ok_def, is_word_type_def,
        vyperValueTheory.evaluate_type_def, eval_operand_def] >>
      simp[loweringPostsTheory.val_footprint_def, exprSimPropsTheory.val_store_size_def,
        vfmConstantsTheory.word_size_def] >> gvs[]) >>
  simp[ptr_buf_ok_def, assignBasePtrLiteralSourceTheory.assign_base_ptr_one_byte_buffer_size, eval_operand_def] >>
  metis_tac[]
QED

(* Compose the actual ALLOCA endpoint and its supplied initialization run.
   The caller supplies code-layout/fresh-output facts, not a second execution. *)
Theorem assign_base_ptr_alloca_init_ghost:
  !D lo ctx func PG G tn s u t G' tn' p q i j k l d cenv cx es sa.
    p <> q /\ stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ ghost_inv d cenv cx es G tn s /\
    MEM (mk_inst i ALLOCA [Lit 64w] [p]) (fn_insts func) /\
    not_local_ptr cenv es.scopes p /\ not_local_ptr cenv es.scopes q /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> x <> p /\ x <> q) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> x <> p /\ x <> q) /\
    (!x. not_fresh_at sa x ==> x <> p /\ x <> q) /\
    step_inst_base (mk_inst i ALLOCA [Lit 64w] [p]) s = OK u /\
    run_inst_seq
      [mk_inst j MSTORE [Var p; Lit 1w] [];
       mk_inst k ADD [Var p; Lit 32w] [q];
       mk_inst l MSTORE [Var q; Lit (n2w (2 ** 248))] []] u = OK t /\
    inst_seq_ptr D lo ctx func PG
      (step_prov PG G (mk_inst i ALLOCA [Lit 64w] [p]) u)
      (step_taint (mk_inst i ALLOCA [Lit 64w] [p]) s u tn)
      [mk_inst j MSTORE [Var p; Lit 1w] [];
       mk_inst k ADD [Var p; Lit 32w] [q];
       mk_inst l MSTORE [Var q; Lit (n2w (2 ** 248))] []] u G' tn' ==>
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es sa G tn s G' tn' /\
    ?a. lookup_var p t = SOME a /\ w2n a + 64 < dimword (:256) /\
      (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
        val_in_memory (BaseTV (BytesT (Dynamic 64))) (BytesV [1w]) (w2n a) m)
Proof
  rpt gen_tac >> strip_tac >>
  `64 < dimword (:256)` by simp[dimword_def] >>
  `exec_alloca (mk_inst i ALLOCA [Lit 64w] [p]) s (64w:bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  ` (mk_inst i ALLOCA [Lit 64w] [p]).inst_opcode = ALLOCA /\
    (mk_inst i ALLOCA [Lit 64w] [p]).inst_operands = [Lit 64w] /\
    (mk_inst i ALLOCA [Lit 64w] [p]).inst_outputs = [p]` by simp[mk_inst_def] >>
  drule_all assign_base_ptr_alloca_endpoint >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes u` by fs[stmt_state_rel_def, state_rel_def] >>
  `w2n w + 64 < dimword (:256)` by fs[dimword_def] >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- suspend "kept" >>
  qexists_tac `w` >> conj_tac >- suspend "lookup" >>
  simp[] >> drule_at (Pat `inst_seq_ptr`) assign_base_ptr_one_byte_init_robust >>
  simp[] >> disch_then drule >> simp[]
QED

Resume assign_base_ptr_alloca_init_ghost[invariant]:
  `ghost_inv d cenv cx es
     (step_prov PG G (mk_inst i ALLOCA [Lit 64w] [p]) u)
     (step_taint (mk_inst i ALLOCA [Lit 64w] [p]) s u tn) u` by
    (irule assign_base_ptr_alloca_inv >>
     simp[] >> metis_tac[]) >>
  drule_at (Pat `inst_seq_ptr`) assign_base_ptr_one_byte_init_inv >>
  simp[] >> disch_then (qspecl_then [`d`, `cenv`, `cx`, `es`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[dimword_def] >> metis_tac[])) >> strip_tac >>
  drule_all assign_base_ptr_one_byte_init_endpoint >>
  disch_then SUBST1_TAC >> simp[]
QED

Resume assign_base_ptr_alloca_init_ghost[kept]:
  `ghost_kept cenv es sa G tn s
     (step_prov PG G (mk_inst i ALLOCA [Lit 64w] [p]) u)
     (step_taint (mk_inst i ALLOCA [Lit 64w] [p]) s u tn)` by
    (irule assign_base_ptr_alloca_kept >>
     simp[] >> metis_tac[]) >>
  drule_at (Pat `inst_seq_ptr`) assign_base_ptr_one_byte_init_kept >>
  simp[] >> metis_tac[]
QED

Resume assign_base_ptr_alloca_init_ghost[lookup]:
  drule_all assign_base_ptr_one_byte_init_endpoint >> strip_tac >>
  drule assign_base_ptr_one_byte_init_frame >> strip_tac >> metis_tac[]
QED

Finalise assign_base_ptr_alloca_init_ghost
