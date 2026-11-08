(* Allocation may add taint in its new region.  Global taint shrinking is
   therefore not a suitable frame premise: only old regions need protection. *)
Theory bodyPtrMakeArrayAllocationFrame
Ancestors
  bodyPtrDefs allocationPtr compileEnv pred_set arithmetic
  exprSimPtrLiteralBuffer bodyPtrMakeArrayAllocBuffer ptrDiscipline finite_map

Theorem ghost_kept_disjoint_taint_frame:
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem UNION {i | b <= i /\ i < b+n} /\
  (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len) ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def, SUBSET_DEF, regions_disjoint_def] >>
  rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `!x. x IN tn'.t_mem ==> _` drule >>
  strip_tac >> gvs[] >> decide_tac
QED

(* The allocation's dirty bytes are harmless to every pre-existing frame.
   This also covers allocation sites which are reused and add no dirty bytes. *)
Theorem literal_allocation_ghost_post:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  u.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem UNION dirty /\
  dirty SUBSET {i | b <= i /\ i < b+n} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' u /\ ghost_kept cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[] >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len` by
    (drule_all literal_ptr_local_region_frame >> metis_tac[]) >>
  reverse conj_tac
  >- (irule ghost_kept_disjoint_taint_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`b`, `n`] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      fs[SUBSET_DEF] >> metis_tac[]) >>
  irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p u = SOME w` by metis_tac[] >>
      drule_all literal_ptr_local_footprint_exterior >> simp[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem literal_alloca_ghost_endpoint:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK u /\
  stmt_state_rel ctx func cenv cx es s /\
  stmt_state_rel ctx func cenv cx es u /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\ FLOOKUP u.vs_allocas id = SOME (b,n) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ~not_fresh_at sa out /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn) u /\
  ghost_kept cenv es sa G tn s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) u)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn)
Proof
  strip_tac >>
  drule_all literal_ptr_alloca_ghost >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >> gvs[] >>
  drule literal_alloca_static_frame >> strip_tac >>
  irule literal_allocation_ghost_post >>
  simp[op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (qexistsl_tac [`b`, `dirty`, `n`] >> simp[] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`ctx`, `func`] >> simp[]
QED
