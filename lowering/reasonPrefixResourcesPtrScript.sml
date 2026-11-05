(* Resource transport across the reason encoder's allocation prefix. *)
Theory reasonPrefixResourcesPtr
Ancestors
  reasonBufferPtr normalizationAllocPtr robustCopyTransportPtr typedCopyPtr
  bodyPtrDefs ptrDiscipline venomState venomInst pred_set arithmetic
  loweringPosts compileEnv exprLoweringProps exprSimProps

Theorem reason_encoder_store_robust_preserved:
  !tn s id dst value a w tv v p.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ val_wf tv v /\
    (!i. p <= i /\ i < p + val_footprint tv v ==>
      ~(w2n a <= i /\ i < w2n a + 32)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id MSTORE [Var dst; value] []) s
        (mstore (w2n a) w s) tn).t_mem
      (mstore (w2n a) w s).vs_memory m ==>
      val_in_memory tv v p m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (cj 5 mstore_ghost_frame) >> pure_rewrite_tac[FORALL_SIMP] >>
  disch_then (qspec_then `id` assume_tac) >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `(mstore (w2n a) w s).vs_memory`,
    `tn.t_mem`, `tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}`,
    `{i | w2n a <= i /\ i < w2n a + 32}`] >> simp[] >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`s`, `w2n (a:bytes32)`, `w`] mstore_memory_frame) >>
  gvs[mem_agree_outside_def] >> metis_tac[]
QED

(* Stores change the representation, but not its allocation/local location. *)
Theorem reason_encoder_store_value_location:
  !cenv cx ty sa sb es v op s a w.
    expr_val_at cenv cx ty sa sb es v op (mstore a w s) <=>
    expr_val_at cenv cx ty sa sb es v op s
Proof
  simp[expr_val_at_def, local_region_def, eval_operand_def,
       lookup_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem reason_encoder_original_local_region:
  !ctx func cenv cx e es sa sb s0 es' v op s n b sz.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    local_region cenv es.scopes s0 n b sz ==>
    local_region cenv es'.scopes s n b sz
Proof
  rpt gen_tac >> strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s0`, `sa`, `es.scopes`] >>
  gvs[expr_post_def] >> metis_tac[]
QED
