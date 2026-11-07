Theory bodyPtrBytestringBuiltinsUintAlloc
Ancestors
  bodyPtrBytestringBuiltinsAllocation exprSimPtrLiteralBuffer
  bodyPtrDefs ptrDiscipline venomState venomInst finite_map
  codegenRel contextCodegenRel pred_set compileEnv

Theorem alloca_union_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa q /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len) /\
  dirty SUBSET {i | b <= i /\ i < b+n} /\
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es (G |+ (q,(b,n)))
    (tn with <|t_var := tn.t_var |+ (q,{}); t_mem := tn.t_mem UNION dirty|>) u
Proof
  strip_tac >> irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >>
  simp[FLOOKUP_UPDATE, op_taint_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) literal_ptr_local_footprint_exterior >>
    disch_then (qspecl_then [`n`, `b`] mp_tac) >> simp[] >>
    disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >> simp[] >>
    disch_then irule >> first_assum ACCEPT_TAC) >>
  rpt strip_tac >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem alloca_union_ghost_kept:
  ~not_fresh_at sa q /\ dirty SUBSET {i | b <= i /\ i < b+n} /\
  (!aid off len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    off+len <= b \/ b+n <= off) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    off+len <= b \/ b+n <= off) ==>
  ghost_kept cenv es sa G tn s (G |+ (q,(b,n)))
    (tn with <|t_var := tn.t_var |+ (q,{}); t_mem := tn.t_mem UNION dirty|>)
Proof
  strip_tac >> simp[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >> `x <> q` by metis_tac[] >>
      simp[FLOOKUP_UPDATE, op_taint_def]) >>
  gvs[SUBSET_DEF] >> conj_tac >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> decide_tac
QED

Theorem alloca_step_old_operand_ghost:
  (!x. op = Var x ==> x <> q) ==>
  op_prov (step_prov PG G (mk_inst id ALLOCA [sz] [q]) u) op = op_prov G op /\
  op_taint (step_taint (mk_inst id ALLOCA [sz] [q]) s u tn) op = op_taint tn op
Proof
  strip_tac >> Cases_on `op` >> gvs[op_prov_def, op_taint_def] >>
  irule (SRULE [op_taint_def] alloca_old_register_ghost_frame) >> simp[]
QED

Theorem alloca_step_ghost_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) (fn_insts fn) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s = OK u /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~not_fresh_at sa q /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,n) /\
  (!aid off len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
    off+len <= b \/ b+n <= off) /\
  (!name off len. local_region cenv es.scopes s name off len ==>
    off+len <= b \/ b+n <= off) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s u tn) u /\
  ghost_kept cenv es sa G tn s
    (step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) u)
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [q]) s u tn)
Proof
  strip_tac >> drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >> gvs[] >>
  conj_tac
  >- (irule (SRULE [] alloca_union_ghost_inv) >> simp[] >>
      qexistsl_tac [`ctx`, `fn`, `s`, `sa`] >> simp[regions_disjoint_def] >>
      rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  irule (SRULE [] alloca_union_ghost_kept) >> simp[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem alloca_step_state_fields:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [q]) s = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_halted = s.vs_halted
Proof
  simp[venomExecSemanticsTheory.step_inst_base_def, mk_inst_def,
    venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[update_var_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[update_var_def]
QED

Theorem old_local_region_transport:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  !name b n. local_region cenv scopes u name b n <=>
             local_region cenv scopes s name b n
Proof
  simp[local_region_def] >> rpt strip_tac >> eq_tac >> strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  metis_tac[]
QED
