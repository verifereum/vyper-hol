Theory bodyFullHashCleanFrame
Ancestors
  bodyFullGhostFrame bodyPtrHashBuiltinsGhostFrame bodyPtrHashBuiltinsKeccak
  wordLoadStorePtr decoderGhostFramePtr valueEncodingProps wordArgsPtr
  bodyPtrDefs loweringStateRelDefs exprLoweringProps
  ptrDiscipline venomState venomInst finite_map pred_set

Theorem hash_ghost_kept_wb_trans:
  stmt_state_rel H ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es0 es' sa s0 s1 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sb G1 tn1 s1 G2 tn2 ==>
  ghost_kept_at lo cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >>
  `ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
   ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2` by
    (fs[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  drule_all wordArgsPtrTheory.ghost_kept_wb_trans >>
  fs[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]
QED

Theorem hash_sha3_fresh_frame_at:
  !D lo d cenv cx es G tn s sa out v PG id src len G0 tn0 s0.
    ghost_inv_at D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    ~not_fresh_at sa out /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst id SHA3 [src;len] [out]) (update_var out v s))
      (step_taint (mk_inst id SHA3 [src;len] [out]) s (update_var out v s) tn)
      (update_var out v s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id SHA3 [src;len] [out]) (update_var out v s))
      (step_taint (mk_inst id SHA3 [src;len] [out]) s (update_var out v s) tn) /\
    op_taint (step_taint (mk_inst id SHA3 [src;len] [out]) s
      (update_var out v s) tn) (Var out) = {} /\
    op_prov (step_prov PG G (mk_inst id SHA3 [src;len] [out])
      (update_var out v s)) (Var out) = NONE
Proof
  rpt gen_tac >> strip_tac >> simp[hash_sha3_ghost] >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           FLOOKUP_DRESTRICT, op_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[ghost_kept_at_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
          op_taint_def] >> metis_tac[]) >>
  simp[op_taint_def, op_prov_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem hash_clean_mstore_frame_at:
  !H D lo PG G tn s id p value a w d cenv cx es ctx fn sa G0 tn0 s0.
    lookup_var p s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ghost_inv_at D lo d cenv cx es G tn s /\
    stmt_state_rel H ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!n b k i. local_region cenv es.scopes s n b k /\ b <= i /\ i < b+k ==>
      ~(w2n a <= i /\ i < w2n a + 32)) /\ lo <= w2n a /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
    ghost_inv_at D lo d cenv cx es
      (step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
      (mstore (w2n a) w s) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0
      (step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `id`] strip_assume_tac) >>
  conj_tac >- suspend "invariant" >>
  gvs[ghost_kept_at_def, op_taint_def] >> metis_tac[]
QED

Resume hash_clean_mstore_frame_at[invariant]:
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_def] >> strip_tac >>
  rewrite_tac[ghost_inv_at_def] >> conj_tac >- suspend "locals" >>
  conj_tac >- (Cases_on `d` >>
    gvs[return_buf_ptr_def, ptr_covers_def, mstore_def,
        lookup_var_def, op_taint_def] >>
    PairCases_on `x` >>
    gvs[return_buf_ptr_def, ptr_covers_def, mstore_def,
        lookup_var_def, op_taint_def]) >>
  conj_tac >- gvs[op_taint_def] >>
  conj_tac >- gvs[stor_taint_ok_at_def, mstore_def, step_taint_def,
                  imm_taint_def, adopt_reset_def, mk_inst_def] >>
  conj_tac >- suspend "prefix" >>
  gvs[op_taint_def, allocas_from_def, mstore_def] >> gvs[]
QED

Resume hash_clean_mstore_frame_at[locals]:
  rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> conj_tac
  >- gvs[ptr_covers_def, mstore_def, lookup_var_def, op_taint_def] >>
  rpt gen_tac >> strip_tac >>
  irule hash_local_robust_exterior_frame >>
  qpat_assum `stmt_state_rel H ctx fn cenv cx es s` (irule_at Any) >>
  qpat_assum `FLOOKUP cenv.ce_vars name = _` (irule_at Any) >>
  qexistsl_tac [`{i | w2n a <= i /\ i < w2n a + 32}`,
    `step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn`,
    `tn`, `mstore (w2n a) w s`] >>
  simp[] >>
  `lookup_var p' s = SOME w'` by
    (qpat_x_assum `lookup_var p' (mstore _ _ _) = _` mp_tac >>
     simp[lookup_var_def, mstore_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >> simp[] >>
  rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac
QED

Resume hash_clean_mstore_frame_at[prefix]:
  `mem_bytes_at 0 lo (mstore (w2n a) w s).vs_memory =
   mem_bytes_at 0 lo s.vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Finalise hash_clean_mstore_frame_at
