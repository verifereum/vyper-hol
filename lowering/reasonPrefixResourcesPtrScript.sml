(* Resource transport across the reason encoder's allocation prefix. *)
Theory reasonPrefixResourcesPtr
Ancestors
  reasonBufferPtr normalizationAllocPtr robustCopyTransportPtr typedCopyPtr
  bodyPtrDefs ptrDiscipline venomState venomInst pred_set arithmetic
  loweringPosts compileEnv exprLoweringProps exprSimProps exprSimAlloc emitHelperProps exprSimHash

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

(* A read-only allocation preserves placement without moving the expression's
   ownership interval.  Local-region equivalence is supplied by fresh outputs. *)
Theorem reason_encoder_value_location_frame:
  !cenv cx ty sa sb es v op s t.
    expr_val_at cenv cx ty sa sb es v op s /\
    eval_operand op t = eval_operand op s /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!n b sz. local_region cenv es.scopes t n b sz <=>
      local_region cenv es.scopes s n b sz) ==>
    expr_val_at cenv cx ty sa sb es v op t
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_val_at_def] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[] >> metis_tac[]
QED

Theorem reason_encoder_readonly_post:
  !ctx func cenv cx e es sa sb s0 es' v op s t cc.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    stmt_state_rel ctx func cenv cx es' t /\
    sa.cs_next_var <= cc.cs_next_var /\
    eval_operand op t = eval_operand op s /\
    t.vs_memory = s.vs_memory /\
    (!x w. not_fresh_at cc x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!n b sz. local_region cenv es'.scopes t n b sz <=>
      local_region cenv es'.scopes s n b sz) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op t
Proof
  rpt gen_tac >> strip_tac >>
  `expr_val_at cenv cx (expr_type e) sa sb es' v op t` by
    (irule reason_encoder_value_location_frame >>
     qexists_tac `s` >> gvs[expr_post_def]) >>
  gvs[expr_post_def, expr_val_rel_def, locals_kept_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at cc x` by
        (gvs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!x w. not_fresh_at cc x /\ _ ==> _` irule >>
      simp[] >>
      qpat_x_assum `!x w. not_fresh_at sa x /\ _ ==> _` irule >> simp[]) >>
  metis_tac[]
QED

Theorem reason_encoder_alloc_buffer_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc cd buf n.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    compile_alloc_buffer n cc = (buf,cd) /\ fn_has_code cc cd func /\
    fresh_vars_wrt cc s /\ local_ptrs_reserved cenv cc /\
    fn_inst_ids_distinct func /\ n < dimword (:256) /\
    sa.cs_next_var <= cc.cs_next_var ==>
    ?t w. run_inst_seq (emitted_insts cc cd) s = OK t /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas cc.cs_next_id = SOME (w2n w,n) /\
      w2n w + n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!aid b len. aid < cc.cs_next_id /\
        FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) n b len) /\
      (!name b len. local_region cenv es'.scopes t name b len ==>
        regions_disjoint (w2n w) n b len)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' s` by gvs[expr_post_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `eval_operand op t = eval_operand op s` by suspend "operand" >>
  `!name b len. local_region cenv es'.scopes t name b len <=>
     local_region cenv es'.scopes s name b len` by suspend "locals" >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v op t` by
    (irule reason_encoder_readonly_post >>
     simp[] >> qexistsl_tac [`cc`, `s`] >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> asm_rewrite_tac[]
QED

Resume reason_encoder_alloc_buffer_post[operand]:
  `?ow. eval_operand op s = SOME ow` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[eval_operand_def] >>
  rename1 `lookup_var x s = SOME ow` >>
  `not_fresh_at cc x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     gvs[fresh_vars_wrt_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF] >>
     metis_tac[]) >>
  metis_tac[]
QED

Resume reason_encoder_alloc_buffer_post[locals]:
  rpt gen_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >> conj_tac
      >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
      qexistsl_tac [`cc`, `es'.scopes`, `t`] >> simp[]) >>
  strip_tac >> irule local_region_frame_fwd >>
  qexistsl_tac [`s`, `cc`, `es'.scopes`] >> simp[]
QED

Finalise reason_encoder_alloc_buffer_post

(* The store is confined to an allocated buffer, separated from the old
   allocations and current locals by the allocation-run boundary. *)
Theorem reason_encoder_allocated_store_post:
  !ctx func cenv cx e es sa sb s0 es' v op s cc inst b sz a w.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\
    sa.cs_next_id <= cc.cs_next_id /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= a /\ a + 32 <= b + sz /\
    (!aid off len. aid < cc.cs_next_id /\
      FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
      regions_disjoint b sz off len) /\
    (!name off len. local_region cenv es'.scopes s name off len ==>
      regions_disjoint b sz off len) /\
    expr_val_rel cx (expr_type e) v op (mstore a w s) ==>
    expr_post ctx func cenv cx e es sa sb s0 es' v op (mstore a w s)
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' (mstore a w s)` by
    (irule literal_mstore_state_rel >> reverse conj_tac
     >- gvs[expr_post_def] >>
     qexistsl_tac [`b`, `inst`, `sz`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `!name off len. _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `locals_kept cenv es s0 (mstore a w s)` by suspend "locals" >>
  gvs[expr_post_def, reason_encoder_store_value_location] >>
  rpt strip_tac >>
  `regions_disjoint b sz off sz'` by
    (qpat_x_assum `!aid off len. aid < cc.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[] >> metis_tac[LESS_LESS_EQ_TRANS]) >>
  `mem_bytes_at off sz' (mstore a w s).vs_memory =
   mem_bytes_at off sz' s.vs_memory` by
    (irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >> simp[]) >>
  simp[] >> qpat_x_assum `!aid off sz. _` irule >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  qexists_tac `aid` >> simp[]
QED

Resume reason_encoder_allocated_store_post[locals]:
  `!name off len. local_region cenv es.scopes s0 name off len ==>
     regions_disjoint b sz off len` by
    (rpt strip_tac >>
     `local_region cenv es'.scopes s name off len` by
       (drule_all reason_encoder_original_local_region >> simp[]) >> metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >>
  gvs[expr_post_def] >> rpt strip_tac >>
  irule mstore_region_frame >> qexistsl_tac [`b`, `sz`] >> simp[] >>
  metis_tac[]
QED

Finalise reason_encoder_allocated_store_post
