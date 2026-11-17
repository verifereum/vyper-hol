(* The fixed SHA input allocation and store preserve the complete ghost. *)
Theory bodyFullHashShaStore
Ancestors
  bodyFullHashShaAlloc bodyFullHashCleanFrame bodyFullUnwrapRun
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsKeccakFixed
  bodyPtrHashBuiltinsGhostFrame wordLoadStorePtr exprSimAlloc allocationPtr
  bodyPtrDefs loweringHalt emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  ptrDiscipline venomState venomInst venomExecSemantics finite_map pred_set words

Theorem sha_literal_alloc_store_frame_at:
  !H:(bool # bytes32 # type_value) list # num list.
  !D lo fn cenv cx es sa sm buf s ctx d PG G tn sid value v.
    compile_alloc_buffer 32 sa = (buf,sm) /\ fn_has_code sa sm fn /\
    stmt_state_rel H ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ghost_inv_at D lo d cenv cx es G tn s /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. value = Var x ==> not_fresh_at sa x) /\
    eval_operand value s = SOME v /\ op_taint tn value = {} ==>
    ?t a p G1 tn1 G2 tn2.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      buf.buf_operand = Var p /\ lookup_var p t = SOME a /\
      p = STRING #"%" (toString sa.cs_next_var) /\
      step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t /\
      eval_operand value t = SOME v /\ op_taint tn1 value = {} /\
      G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) t /\
      tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s t tn /\
      G2 = step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n a) v t) /\
      tn2 = step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n a) v t) tn1 /\
      stmt_state_rel H ctx fn cenv cx es (mstore (w2n a) v t) /\
      ghost_inv_at D lo d cenv cx es G2 tn2 (mstore (w2n a) v t) /\
      ghost_kept_at lo cenv es sa G tn s G2 tn2 /\
      ptr_covers G2 tn2 p (mstore (w2n a) v t) 32 /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn2.t_mem) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,32) /\
      w2n a+32 < dimword (:256) /\ not_fresh_at sm p /\
      ptr_covers G1 tn1 p t 32 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by
    simp[wordsTheory.dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
      fcpTheory.index_one, fcpTheory.finite_one] >>
  drule_all sha_literal_alloc_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `lookup_var p t = SOME w` by gvs[eval_operand_def] >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >> strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `eval_operand value t = SOME v /\ op_taint tn1 value = {}` by
    (`!x. value = Var x ==> x <> p` by (rpt strip_tac >> gvs[]) >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) (fn_insts fn)` by
       (qpat_x_assum `MEM _ (fn_insts fn)` mp_tac >>
        qpat_x_assum `buf.buf_operand = Var p` mp_tac >>
        qpat_x_assum `buf.buf_operand = Var (STRING _ _)` mp_tac >> simp[]) >>
     `value <> Var p` by
       (strip_tac >> qpat_x_assum `!x. value = Var x ==> x <> p`
         (qspec_then `p` mp_tac) >> simp[]) >>
     qpat_assum `stmt_state_rel H ctx fn cenv cx es s`
       (mp_then Any mp_tac (GEN_ALL (SIMP_RULE std_ss []
         (Q.INST [`n` |-> `32`] (SPEC_ALL hash_alloca_old_operand))))) >>
     disch_then (qspecl_then [`v`, `value`, `tn`, `t`, `p`,
       `sa.cs_next_id`, `w2n w`] mp_tac) >> simp[]) >>
  qexistsl_tac [`t`, `w`, `p`, `G1`, `tn1`,
    `step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n w) v t)`,
    `step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n w) v t) tn1`] >>
  simp[] >> suspend "post"
QED

Resume sha_literal_alloc_store_frame_at[post]:
  `STRING #"%" (toString sa.cs_next_var) = p` by gvs[] >>
  qpat_x_assum `G1 = _` (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  qpat_x_assum `tn1 = _` (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  simp[] >>
  `!name b k i. local_region cenv es.scopes t name b k /\ b <= i /\ i < b+k ==>
    ~(w2n w <= i /\ i < w2n w+32)` by
    (rpt strip_tac >>
     qpat_x_assum `!name b k. local_region cenv es.scopes t name b k ==> _`
       (drule_then mp_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- suspend "state" >>
  conj_tac >- (drule_all hash_clean_mstore_frame_at >>
    disch_then (qspecl_then [`PG`, `sid`] mp_tac) >> simp[]) >>
  conj_tac >- suspend "kept" >>
  irule hash_store_covered_clean >> gvs[]
QED

Resume sha_literal_alloc_store_frame_at[kept]:
  qpat_x_assum `G1 = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `tn1 = _` (fn th => rewrite_tac[GSYM th]) >>
  drule_all mstore_ghost_frame >> strip_tac >>
  irule ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G1`, `tn1`] >> simp[op_taint_def]
QED

Resume sha_literal_alloc_store_frame_at[state]:
  irule literal_mstore_state_rel >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`w2n w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]`, `32`] >>
  conj_tac >- (rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
  gvs[mk_inst_def]
QED

Finalise sha_literal_alloc_store_frame_at
