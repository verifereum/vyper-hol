(* Word-load/store boundaries for typed normalization. *)
Theory typedCopyPtr
Ancestors
  typedCopyCompatibilityPtr normalizationPrefixPtr fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInstProofs venomInst venomState
  contextCodegenRelProps finite_map memLocDefs codegenRel contextCodegenRel fragExec
  typedCopyAgreement emitHelper compileEnv valueEncodingProps representationCleanPtr
  ptrCoverage allocationPtr exprLoweringProps typedCopyLayoutPtr exprSimBufferStore loweringPosts exprSimProps
Theorem ptr_inst_ok_mload:
  !D ctx fn G tn s id src tmp fuel.
    ptr_covers G tn src s 32 /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MLOAD [Var src] [tmp]) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def,
       eval_operand_def] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> simp[mem_read_ops_def] >> metis_tac[]) >>
  simp[step_inst_non_invoke, venomExecSemanticsTheory.step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, eval_operand_def, AllCaseEqs(), mload_def,
       update_var_def] >> rpt strip_tac >> gvs[]
QED

Theorem mload_ghost_clean:
  !PG G tn s id src tmp a.
    eval_operand src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    op_taint (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MLOAD [src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn).t_trans = tn.t_trans
Proof
  rpt strip_tac >>
  gvs[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
      mk_inst_def, mem_word_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, source_memory_write_ranges_def,
      range_bytes_def, update_var_def, store_taint_def, adopt_reset_def,
      FLOOKUP_UPDATE, FLOOKUP_DEF, pred_setTheory.EXTENSION]
  >- (gen_tac >> Cases_on `x < 32` >> simp[] >>
      first_x_assum irule >> decide_tac) >>
  metis_tac[]
QED

Theorem mload_preserves_ptr_covers:
  !PG G tn s id src tmp dst a n.
    tmp <> dst /\ ptr_covers G tn dst s n ==>
    ptr_covers
      (step_prov PG G (mk_inst id MLOAD [src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      dst (update_var tmp (mload (w2n a) s) s) n
Proof
  rpt strip_tac >>
  gvs[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
      step_taint_def, set_var_taint_def, op_taint_def, mk_inst_def,
      update_var_def, lookup_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem mload_then_mstore_ok:
  !D ctx fn PG G tn s id src dst tmp a fuel.
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ tmp <> dst /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id MLOAD [Var src] [tmp]) s /\
    ptr_inst_ok D 0 fuel ctx fn
      (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
        (update_var tmp (mload (w2n a) s) s))
      (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
        (update_var tmp (mload (w2n a) s) s) tn)
      (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
      (update_var tmp (mload (w2n a) s) s)
Proof
  rpt strip_tac
  >- (irule ptr_inst_ok_mload >> simp[]) >>
  irule ptr_inst_ok_mstore >> simp[] >> conj_tac
  >- (irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]) >>
  irule mload_preserves_ptr_covers >> simp[]
QED

Theorem ptr_fragment_step:
  !cx ctx PG sa sb inst P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
    inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
    (!G tn s. P G tn s ==>
       ?t. step_inst_base inst s = OK t /\
           t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
           (!fuel fn. ~ctx_has_dalloca ctx ==>
             ptr_inst_ok (cx_dead cx) 0 fuel ctx fn G tn inst s) /\
           Q (step_prov PG G inst t) (step_taint inst s t tn)
             (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> strip_tac >> simp[frag_exec_ptr_def] >> rpt strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum drule >> strip_tac >>
  disj1_tac >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`,
               `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[] >> rpt strip_tac >> qexists_tac `fuel` >> gvs[] >>
  conj_tac >- (simp[run_from_def, Once exec_block_def, step_inst_non_invoke]) >>
  simp[ghost_run_def, Once ghost_block_def, ghost_step_def,
       step_inst_non_invoke] >>
  strip_tac >> fs[ptr_safe_run_def] >>
  simp[Once ptr_safe_block_def, ptr_safe_step_def, step_inst_non_invoke,
       ghost_step_def] >> gvs[]
QED

Theorem mload_frag_ptr:
  !cx ctx PG sa sb id src tmp P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MLOAD [Var src] [tmp]] /\
    (!G tn s. P G tn s ==>
       ptr_covers G tn src s 32 /\
       !a. lookup_var src s = SOME a ==>
         Q (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
              (update_var tmp (mload (w2n a) s) s))
           (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
              (update_var tmp (mload (w2n a) s) s) tn)
           ((update_var tmp (mload (w2n a) s) s) with
              vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[] >>
  simp[mk_inst_def, is_terminator_def] >> rpt strip_tac >>
  `?a. lookup_var src s = SOME a` by
    (first_x_assum drule >> simp[ptr_covers_def] >> metis_tac[]) >>
  qexists_tac `update_var tmp (mload (w2n a) s) s` >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  simp[update_var_def] >> conj_tac
  >- (rpt strip_tac >> irule (SRULE [mk_inst_def] ptr_inst_ok_mload) >> metis_tac[]) >>
  first_x_assum drule >> simp[mk_inst_def, update_var_def]
QED

Theorem mstore_frag_ptr:
  !cx ctx PG sa sb id dst value P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MSTORE [Var dst; value] []] /\
    (!G tn s. P G tn s ==>
       ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
       ?a w. lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
         Q (step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
              (mstore (w2n a) w s))
           (step_taint (mk_inst id MSTORE [Var dst; value] []) s
              (mstore (w2n a) w s) tn)
           ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `mstore (w2n a) w s` >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  simp[mstore_def] >> rpt strip_tac >>
  irule ptr_inst_ok_mstore >> simp[]
QED

Theorem mstore_ghost_frame:
  !PG G tn s id dst value a w.
    lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} ==>
    step_prov PG G (mk_inst id MSTORE [Var dst; value] [])
      (mstore (w2n a) w s) = G /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_var = tn.t_var /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id MSTORE [Var dst; value] []) s
      (mstore (w2n a) w s) tn).t_mem =
      tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       eval_operand_def, written_taint_def, range_bytes_def, new_site_bytes_def,
       mstore_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem compile_store_word_code:
  !cenv dst dst_ty src src_ty sa sb.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv dst dst_ty src src_ty sa = ((),sb) ==>
    ?sm tmp id.
      sm.cs_current_bb = sa.cs_current_bb /\
      sm.cs_current_insts = sa.cs_current_insts ++
        [mk_inst id MLOAD [src] [tmp]] /\
      sb.cs_current_bb = sm.cs_current_bb /\
      sb.cs_current_insts = sm.cs_current_insts ++
        [mk_inst (id+1) MSTORE [dst; Var tmp] []] /\
      cs_extends sa sm /\ cs_extends sm sb /\
      (!x. not_fresh_at sa x ==> tmp <> x)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_store_memory_typed_word >>
  disch_then (qspecl_then [`src_ty`, `src`, `dst`, `cenv`] assume_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ = _` kall_tac >>
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >> strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >>
  qexistsl_tac [
    `sa with <| cs_next_id := sa.cs_next_id + 1;
                cs_next_var := sa.cs_next_var + 1;
                cs_current_insts := sa.cs_current_insts ++
                  [mk_inst sa.cs_next_id MLOAD [src]
                    ["%" ++ toString sa.cs_next_var]] |>`,
    `"%" ++ toString sa.cs_next_var`, `sa.cs_next_id`] >>
  simp[cs_extends_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem mstore_memory_frame:
  !s off w.
    mem_agree_outside {i | off <= i /\ i < off + 32}
      (mstore off w s).vs_memory s.vs_memory
Proof
  rpt gen_tac >> simp[mem_agree_outside_def] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED


Theorem compile_store_word_framed_frag_ptr:
  !cx ctx PG R cenv dst dst_ty src src_ty sa sb G tn s a b.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
      ((),sb) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
        sf.vs_memory s.vs_memory /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_store_word_code >> strip_tac >>
  `tmp <> dst` by metis_tac[] >>
  qabbrev_tac `s1 = update_var tmp (mload (w2n a) s) s` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst id MLOAD [Var src] [tmp]) s1` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var src] [tmp]) s s1 tn` >>
  qabbrev_tac `v1 = s1 with vs_inst_idx := SUC s.vs_inst_idx` >>
  `ptr_covers G1 tn1 dst s1 32` by
    (simp[Abbr `G1`, Abbr `tn1`, Abbr `s1`] >>
     irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn1 (Var tmp) = {} /\ tn1.t_mem = tn.t_mem /\
   tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (simp[Abbr `tn1`, Abbr `s1`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `lookup_var dst v1 = SOME b /\
   eval_operand (Var tmp) v1 = SOME (mload (w2n a) s)` by
    (simp[Abbr `v1`, Abbr `s1`, update_var_def, lookup_var_def,
          eval_operand_def, FLOOKUP_UPDATE] >> gvs[lookup_var_def]) >>
  qabbrev_tac `s2 = mstore (w2n b) (mload (w2n a) s) v1` >>
  qabbrev_tac `G2 = step_prov PG G1
    (mk_inst (id+1) MSTORE [Var dst; Var tmp] []) s2` >>
  qabbrev_tac `tn2 = step_taint (mk_inst (id+1) MSTORE [Var dst; Var tmp] [])
    v1 s2 tn1` >>
  qexistsl_tac [`G2`, `tn2`, `s2 with vs_inst_idx := SUC v1.vs_inst_idx`] >>
  conj_tac >-
    (irule frag_exec_ptr_seq >>
     qexistsl_tac [`\g t v. g = G1 /\ t = tn1 /\ v = v1`, `sm`] >>
     simp[] >> conj_tac >-
       (irule mload_frag_ptr >> simp[] >>
        qexistsl_tac [`id`, `src`, `tmp`] >>
        simp[Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`]) >>
     irule mstore_frag_ptr >> simp[] >>
     qexistsl_tac [`dst`, `id+1`, `Var tmp`] >>
     simp[Abbr `G2`, Abbr `tn2`, Abbr `s2`] >>
     gvs[Abbr `v1`, ptr_covers_def, lookup_var_def]) >>
  `s2.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory` by
    simp[Abbr `s2`, Abbr `v1`, Abbr `s1`, mstore_def, update_var_def] >>
  simp[mstore_memory_frame, Abbr `tn2`, Abbr `s2`, mstore_ghost_frame] >>
  rpt strip_tac >>
  `tmp <> p` by metis_tac[] >>
  simp[Abbr `G2`, Abbr `G1`, Abbr `tn1`, Abbr `v1`, Abbr `s1`,
       step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
       lookup_var_def, mstore_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem compile_store_word_frag_ptr:
  !cx ctx PG R cenv dst dst_ty src src_ty sa sb G tn s a b.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
      ((),sb) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
      mem_agree_outside {i | w2n b <= i /\ i < w2n b + 32}
        sf.vs_memory s.vs_memory /\
      tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + 32} /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  rpt strip_tac >> drule_all compile_store_word_framed_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED

(* These are the dynamic premises needed even for an empty Return copy.
   In particular no positive-footprint provenance assumption is needed. *)
Theorem expr_post_ptr_return_inputs:
  !ctx fn cenv cx e es sa sb s0 es' v op s d G tn.
    expr_post ctx fn cenv cx e es sa sb s0 es' v op s /\
    ghost_inv d cenv cx es' G tn s /\
    ptr_val_ok cx (expr_type e) v op G tn s ==>
    stmt_state_rel ctx fn cenv cx es' s /\
    (?w. eval_operand op s = SOME w) /\ op_taint tn op = {} /\
    stor_taint_ok cx tn s
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
       ghost_inv_def, ptr_val_ok_def] >> metis_tac[]
QED

(* A recursive field is addressed in memory even when its value type is
   primitive. Robustness of that field, not ptr_val_ok at a word type,
   supplies the clean MLOAD bytes. *)
Theorem compile_store_word_field_ptr:
  !cx ctx PG R cenv dst dst_ty src src_ty sa sb G tn s a b tv v.
    is_word_type dst_ty /\
    compile_store_memory_typed cenv (Var dst) dst_ty (Var src) src_ty sa =
      ((),sb) /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ((?x. v = BoolV x) \/ (?x. v = IntV x) \/
     (?x. v = FlagV x) \/ (?x. v = DecimalV x)) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory tv v (w2n a) mem) ==>
    frag_exec_ptr cx ctx PG sa sb
      (\g t st. g = G /\ t = tn /\ st = s)
      (\g t st. !i. w2n b <= i /\ i < w2n b + 32 ==> i NOTIN t.t_mem) R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    metis_tac[robust_val_in_memory_prim_clean] >>
  qpat_x_assum `_ \/ _` kall_tac >>
  drule_all compile_store_word_frag_ptr >>
  disch_then (qspecl_then [`cx`, `ctx`, `PG`, `R`] strip_assume_tac) >>
  gvs[frag_exec_ptr_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >>
  strip_tac >- (disj1_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> metis_tac[]
QED

Theorem type_stmt_return_some_iff:
  !env ty e.
    IS_SOME (type_stmt env ty (Return (SOME e))) <=>
    well_typed_expr env e /\
    type_widens_to env.type_defs (expr_type e) ty /\ ty <> NoneT
Proof
  simp[vyperTypeSystemTheory.type_stmt_def] >> metis_tac[]
QED

Theorem typed_return_normalization_inputs:
  !cenv cx env es ty e.
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ty (Return (SOME e))) /\ expr_type e <> ty ==>
    well_typed_expr env e /\
    arg_type_fits (expr_type e) ty /\
    well_formed_type (get_tenv cx) ty /\ ty <> NoneT
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  gvs[type_stmt_return_some_iff, vyperTypeSystemTheory.type_widens_to_def]
QED

Theorem typed_return_normalization_layout:
  !cenv cx env es ty e tv v.
    expr_sim_inv cenv cx env es /\
    IS_SOME (type_stmt env ty (Return (SOME e))) /\ expr_type e <> ty /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v ==>
    ?tu. evaluate_type (get_tenv cx) ty = SOME tu /\
      arg_type_fits (expr_type e) ty /\ ty <> NoneT /\
      value_has_type tu v /\ default_value tv = default_value tu /\
      val_footprint tv v <= type_memory_size tv /\
      val_footprint tu v <= type_memory_size tu
Proof
  rpt strip_tac >> drule_all typed_return_normalization_inputs >> strip_tac >>
  gvs[vyperTypeSystemTheory.well_formed_type_def,
      optionTheory.IS_SOME_EXISTS] >>
  drule_all (cj 1 vyperTypeArgFitsTheory.arg_type_fits_value_has_type) >>
  strip_tac >>
  drule_all (cj 1 vyperTypeArgFitsTheory.arg_type_fits_default_value) >>
  strip_tac >>
  metis_tac[exprSimPropsTheory.val_footprint_le,
            valueTypingMemoryPropsTheory.value_has_type_memory_wf]
QED

Theorem type_widens_to_fixed_array_length:
  !tenv t u n m.
    type_widens_to tenv (ArrayT t (Fixed n)) (ArrayT u (Fixed m)) ==>
    n = m
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.arg_type_fits_def] >> metis_tac[]
QED

Theorem type_widens_to_dynamic_array_capacity:
  !tenv t u n m.
    type_widens_to tenv (ArrayT t (Dynamic n)) (ArrayT u (Dynamic m)) ==>
    n <= m
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.arg_type_fits_def] >> rpt strip_tac >> gvs[]
QED

(* Checked edge cases for the normalization-contract audit. These are
   compatibility/representation probes, not counterexamples to a frame. *)
Theorem audit_return_copy_bounds[local]:
  ~arg_type_fits (ArrayT (BaseT BoolT) (Fixed 0))
                (ArrayT (BaseT BoolT) (Fixed 1)) /\
  arg_type_fits (ArrayT (BaseT BoolT) (Dynamic 0))
                (ArrayT (BaseT BoolT) (Dynamic 1)) /\
  arg_type_fits (TupleT []) (TupleT []) /\
  ~arg_type_fits (TupleT []) (TupleT [BaseT BoolT])
Proof
  EVAL_TAC
QED

Theorem audit_string_padding_unconstrained[local]:
  val_in_memory (BaseTV (StringT 1)) (StringV "a") 0
    (REPLICATE 31 0w ++ [1w; 97w; 0w]) /\
  val_in_memory (BaseTV (StringT 1)) (StringV "a") 0
    (REPLICATE 31 0w ++ [1w; 97w; 255w]) /\
  mem_bytes_at 33 1 (REPLICATE 31 0w ++ [1w; 97w; 0w]) <>
  mem_bytes_at 33 1 (REPLICATE 31 0w ++ [1w; 97w; 255w])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def,
                    fcpLib.INDEX_CONV ``dimindex(:8)``]
QED

(* Positive reads derive nonwrap from the semantic frontier, not from the
   possibly oversized incoming provenance site. *)
Theorem expr_val_at_ptr_offset_read_covers:
  !ctx func cenv cx t sa sb es v p s tv w G tn off n G' tn' q s'.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v (Var p) s /\
    ptr_val_ok cx t v (Var p) G tn s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    lookup_var p s = SOME w /\ 0 < n /\
    off + n <= val_footprint tv v /\
    lookup_var q s' = SOME (w + n2w off) /\
    FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  `w2n w <= w2n w + off /\
   w2n w + off < w2n w + val_footprint tv v` by decide_tac >>
  `w2n w + off < s.vs_alloca_next` by
    (drule_all expr_val_at_below_frontier >> simp[]) >>
  `s.vs_alloca_next < dimword(:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `off < dimword(:256)` by decide_tac >>
  `w2n w + off < dimword(:256)` by decide_tac >>
  `val_footprint tv v <> 0` by decide_tac >>
  `val_footprint tv v <= val_footprint tv v` by simp[] >>
  `ptr_covers G tn p s (val_footprint tv v)` by
    (drule_all ptr_val_ok_read_covers >> simp[]) >>
  gvs[ptr_covers_def] >>
  simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem alloca_step_offset_ptr_covers:
  !ctx func cenv cx es s id capacity out s1 PG G G1 w off n q s' G' tn'.
    stmt_state_rel ctx func cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w capacity)] [out]) (fn_insts func) /\
    capacity < dimword(:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w capacity)] [out]) s = OK s1 /\
    G1 = step_prov PG G (mk_inst id ALLOCA [Lit (n2w capacity)] [out]) s1 /\
    lookup_var out s1 = SOME w /\ off + n <= capacity /\
    lookup_var q s' = SOME (w + n2w off) /\
    FLOOKUP G' q = FLOOKUP G1 out /\ op_taint tn' (Var q) = {} ==>
    ptr_covers G' tn' q s' n
Proof
  rpt strip_tac >> drule_all alloca_step_site >> strip_tac >>
  gvs[eval_operand_def] >>
  `FLOOKUP G' q = SOME (b,capacity)` by
    gvs[step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
        FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  `b + off < dimword(:256)` by decide_tac >>
  `b < dimword(:256)` by decide_tac >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptr_covers_def, wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED



Theorem mcopy_operand_ghost_frame:
  !PG G tn s id dst src count_op a b n.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n ==>
    step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s) = G /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_var = tn.t_var /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}
Proof
  rpt strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, finite_mapTheory.DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, mcopy_def, write_memory_with_expansion_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem mcopy_operand_frag_ptr:
  !cx ctx PG sa sb id dst src count_op P Q R.
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id MCOPY [Var dst; Var src; count_op] []] /\
    (!G tn s. P G tn s ==>
       ?a b n. lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
         eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
         ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
         Q (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
              (mcopy (w2n b) (w2n a) (w2n n) s))
           (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
              (mcopy (w2n b) (w2n a) (w2n n) s) tn)
           ((mcopy (w2n b) (w2n a) (w2n n) s) with
              vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt strip_tac >> irule ptr_fragment_step >> simp[is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `mcopy (w2n b) (w2n a) (w2n n) s` >>
  conj_tac >-
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  simp[mcopy_def, write_memory_with_expansion_def] >> rpt strip_tac >>
  irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]
QED

(* Clean arithmetic in the copy-length prefix neither accesses memory nor
   imposes a provenance constraint on its integer operands. *)
Theorem ptr_inst_ok_copy_len_binop:
  !D ctx fn G tn s id opc left right tmp fuel.
    (opc = ADD \/ opc = AND) /\
    op_taint tn left = {} /\ op_taint tn right = {} /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id opc [left;right] [tmp]) s
Proof
  rpt strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem copy_len_binop_frag_ptr:
  !cx ctx PG sa sb id opc left right tmp f P Q R.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++
      [mk_inst id opc [left;right] [tmp]] /\
    (!G tn s. P G tn s ==>
       op_taint tn left = {} /\ op_taint tn right = {} /\
       ?a b. eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
         Q (step_prov PG G (mk_inst id opc [left;right] [tmp])
              (update_var tmp (f a b) s))
           (step_taint (mk_inst id opc [left;right] [tmp]) s
              (update_var tmp (f a b) s) tn)
           ((update_var tmp (f a b) s) with
              vs_inst_idx := SUC s.vs_inst_idx)) ==>
    frag_exec_ptr cx ctx PG sa sb P Q R
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ptr_fragment_step >> simp[] >>
  reverse conj_tac >- (gvs[is_terminator_def]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `update_var tmp (f a b) s` >> conj_tac >-
    (gvs[] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors,
                      instruction_accfupds, combinTheory.K_THM, opcode_case_def] >>
     simp[exec_pure2_def]) >>
  asm_rewrite_tac[] >> simp[update_var_def] >> rpt strip_tac >>
  irule ptr_inst_ok_copy_len_binop >> simp[] >> metis_tac[]
QED

Theorem copy_len_binop_ghost_frame:
  !PG G tn s id opc left right tmp w.
    (opc = ADD \/ opc = AND) ==>
    op_taint (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id opc [left;right] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans /\
    (!p. p <> tmp ==>
      FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [tmp])
        (update_var tmp w s)) p = FLOOKUP G p /\
      op_taint (step_taint (mk_inst id opc [left;right] [tmp]) s
        (update_var tmp w s) tn) (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `new_site_bytes s (update_var tmp w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >> Cases_on `eval_operand left s` >>
  Cases_on `first_prov G [left;right]` >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_copy_len_binop_frag_ptr:
  !opc f G cx ctx PG R sa sb left right out tn s a b.
    (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
    emit_op opc [left;right] sa = (Var out,sb) /\
    eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
    op_taint tn left = {} /\ op_taint tn right = {} ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.emit_binop (copy_len_binop_frag_ptr, copy_len_binop_ghost_frame)
QED

Theorem emit_mload_clean_frag_ptr:
  !cx ctx PG R sa sb src out G tn s a.
    emit_op MLOAD [Var src] sa = (Var out,sb) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      lookup_var out sf = SOME (mload (w2n a) s) /\
      op_taint tnf (Var out) = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.emit_mload (mload_frag_ptr, mload_ghost_clean)
QED


Theorem compile_bytestring_copy_len_frag_ptr:
  !cx ctx PG R sa sb src count_op G tn s a.
    compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
    ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      eval_operand count_op sf =
        SOME ((mload (w2n a) s + 31w && i2w (-32)) + 32w) /\
      op_taint tnf count_op = {} /\
      sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.copy_len
    (emit_mload_clean_frag_ptr, emit_copy_len_binop_frag_ptr, cs_extends_trans)
QED

Theorem compile_store_bytestring_frag_ptr:
  !cx ctx PG R sa sb src dst G tn s a b len n.
    compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    n = 32 + 32 * ((len + 31) DIV 32) /\
    len + 31 < dimword (:256) /\ n < dimword (:256) /\
    mload (w2n a) s = n2w len /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
    ?Gf tnf sf.
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
      (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
         mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\
        FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  typedCopyAmbientLib.store_bytestring
    (compile_bytestring_copy_len_frag_ptr, mcopy_operand_frag_ptr,
     mcopy_operand_ghost_frame, buffer_round_size, buffer_mcopy_exterior)
QED
