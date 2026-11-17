(* Allocation framing for non-slot For element preparation. *)
Theory bodyFullForArray
Ancestors
  whitelistForIterImmCopy whitelistForIterImmLoop stmtSimForArrayLoop
  bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeRuntimeRun fragGasOriginPtr
  ptrDiscipline allocationPtr context arithmetic pred_set
  stmtSimDeclCompose exprSimCopy exprLoweringProps
  stmtLowering loweringPosts loweringStateRelDefs venomMemDefs venomState
  compileEnv vyperState valueEncoding finite_map words

(* This boundary preserves the original entry frame through the actual
   immutable element copy and source binding. It makes no joint-path claim. *)
Theorem for_immutable_element_copy_alloca_frame:
  compile_iter_elem_copy c src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es1 s /\
  immutable_holds c cx ty (Value v) a es1 s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + bytes < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_frame c es0 sa0 s0 c es1 s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ bytes <= capacity /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  es1.scopes = sc :: rest /\ ee.scopes = (sc |+ (id,entry)) :: rest /\
  local_ptrs_reserved c sa ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      alloca_frame c es0 sa0 s0 c ee z
Proof
  strip_tac >>
  `copy_old_operand sa (Var p)` by simp[copy_old_operand_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule alloca_frame_declare_store >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`aid0`, `s`, `sa0`, `w`] >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  conj_tac >- gvs[copy_runtime_frame_def] >>
  rpt gen_tac >> strip_tac >>
  `aid <> aid0` by decide_tac >>
  `off + z' <= w2n w \/ w2n w + capacity <= off` by
    (qpat_x_assum `allocas_non_overlapping s`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  first_x_assum irule >> decide_tac
QED

(* The emitted copy uses the outer environment, while the fresh loop pointer
   belongs to bc.  Only the initial frame environment is transported. *)
Theorem for_immutable_element_copy_outer_frame:
  compile_iter_elem_copy c src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es s /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  immutable_holds c cx ty (Value v) a es s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + bytes < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_frame c es0 sa0 s0 bc (es with scopes := FEMPTY :: es.scopes) s /\
  (!name. IS_SOME (lookup_scopes name es0.scopes) ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ bytes <= capacity /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  local_ptrs_reserved bc sa ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      alloca_frame c es0 sa0 s0 bc ee z
Proof
  strip_tac >>
  `compile_iter_elem_copy bc src (Var p) bytes LocCode F ty ty sa = ((),sb)` by
    (drule immutable_iter_copy_top_ext >>
     disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func bc cx
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule array_empty_scope_rel_transport >> goal_assum (drule_at Any) >> simp[]) >>
  `immutable_holds bc cx ty (Value v) a
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule immutable_value_holds_transport >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `bc.ce_is_ctor = c.ce_is_ctor /\ bc.ce_imm_alloca = c.ce_imm_alloca` by
    (fs[cenv_top_ext_def] >>
     qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloca_frame bc es0 sa0 s0 bc
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule alloca_frame_cenv_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `!region. bc.ce_is_ctor /\ bc.ce_imm_alloca = SOME region ==>
      eval_operand region s = SOME 0w /\ copy_old_operand sa region` by simp[] >>
  `(bc.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes)` by simp[] >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes` by simp[] >>
  drule_all for_immutable_element_copy_alloca_frame >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule alloca_frame_cenv_pre >> goal_assum (drule_at Any) >> simp[]
QED

(* The semantic frame and the joint path share a deterministic raw endpoint.
   Only the latter advances the instruction cursor. *)
Theorem for_immutable_large_element_joint_frame:
  compile_iter_elem_copy c src (Var p) (32*n) LocCode F ty ty sa = ((),sb) /\
  32 < 32*n /\ 32*n = type_memory_size tv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es s /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  immutable_holds c cx ty (Value v) a es s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + capacity < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) (32*n) (w2n w) (32*n)) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  alloca_frame c es0 sa0 s0 bc (es with scopes := FEMPTY :: es.scopes) s /\
  (!name. IS_SOME (lookup_scopes name es0.scopes) ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ 32*n <= capacity /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  local_ptrs_reserved bc sa /\
  op_taint tn src = {} /\ ptr_covers G tn p s capacity /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n w + 32*n <= s.vs_alloca_next /\
  (c.ce_is_ctor ==>
    op_prov G src = NONE /\ w2n a + 32*n <= lo /\ lo <= w2n w /\
    w2n a + 32*n <= s.vs_alloca_next) /\
  (~c.ce_is_ctor ==>
    w2n a + 32*n <= LENGTH s.vs_data_section /\
    w2n a + 32*n < dimword (:256)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf z.
    copy_runtime_frame sa s sb z /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= 32*n /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + 32*n <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    alloca_frame c es0 sa0 s0 bc ee z /\
    (!x. x IN tnf.t_mem <=>
      if w2n w <= x /\ x < w2n w + 32*n
      then c.ce_is_ctor /\ w2n a + (x - w2n w) IN tn.t_mem
      else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!q sz. not_fresh_at sa q /\ ptr_covers G tn q s sz ==>
      ptr_covers Gf tnf q z sz)
Proof
  strip_tac >>
  `0 < 32*n /\ w2n w + 32*n < dimword (:256)` by decide_tac >>
  `!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region` by metis_tac[] >>
  drule_all for_immutable_element_copy_outer_frame >> strip_tac >>
  `(32*n+31) DIV 32 = n` by simp[Once MULT_COMM, ADD_DIV_ADD_DIV] >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca src (Var p) n 0 sa = ((),sb)` by
    (drule immutable_iter_large_copy >> simp[] >>
     disch_then (fn th => fs[th])) >>
  Cases_on `c.ce_is_ctor`
  >- (fs[] >>
      `!region. c.ce_imm_alloca = SOME region ==>
         eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
         op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
      drule (code_copy_ctor_range_origin_ptr |> Q.INST [`off` |-> `0`] |> SRULE []) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
      disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
      simp[ADD_COMM] >> strip_tac >>
      `t = z` by fs[copy_runtime_frame_def] >>
      qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[] >>
      qpat_x_assum `32*n = type_memory_size tv` (fn th => fs[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  fs[] >>
  drule (runtime_code_copy_range_origin |> Q.INST [`off` |-> `0`] |> SRULE []) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
  simp[ADD_COMM] >> strip_tac >>
  `t = z` by fs[copy_runtime_frame_def] >>
  qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[IN_DIFF] >>
  qpat_x_assum `32*n = type_memory_size tv` (fn th => fs[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[CONJ_COMM]
QED
