(* Copy-window transport: allocation and copying may change all bytes inside
   the fresh buffer.  Only the exterior is part of the old ghost frame. *)
Theory bodyPtrMakeArrayMaterialiseFrame
Ancestors
  bodyPtrMakeArrayAllocationFrame exprSimPtrLiteralBuffer
  bodyPtrDefs allocationPtr compileEnv pred_set arithmetic finite_map

Theorem literal_copy_window_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es H tm u
Proof
  strip_tac >> irule literal_ghost_inv_frame >>
  qexistsl_tac [`G`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      `lookup_var p u = SOME w` by metis_tac[] >>
      drule_all literal_ptr_local_footprint_exterior >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!i. _ \/ _ ==> _` (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED

Theorem literal_copy_window_ghost_kept:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  (!i. i < b \/ b+n <= i ==> (i IN tm.t_mem <=> i IN tn.t_mem)) ==>
  ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[] >>
  `!name a len. local_region cenv es.scopes s name a len ==>
    regions_disjoint b n a len` by
    (drule_all literal_ptr_local_region_frame >> metis_tac[]) >>
  irule ghost_kept_disjoint_taint_frame >>
  conj_tac >- metis_tac[] >> qexistsl_tac [`b`, `n`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[SUBSET_DEF] >> rpt strip_tac >>
  Cases_on `b <= x /\ x < b+n` >> simp[] >>
  qpat_x_assum `!i. _ \/ _ ==> _` (qspec_then `x` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED

(* The allocated-copy endpoints state local separation at the intermediate
   allocation state u, but exterior preservation and old operands at z. *)
Theorem literal_allocated_copy_ghost_post:
  ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx func cenv cx es z /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!aid a len. FLOOKUP s.vs_allocas aid = SOME (a,len) /\
    aid < sa.cs_next_id ==> regions_disjoint b n a len) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b n a len) /\
  (!i. i < b \/ b+n <= i ==>
    mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tm.t_mem <=> i IN tn.t_mem)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  z.vs_call_ctx = s.vs_call_ctx /\ z.vs_accounts = s.vs_accounts /\
  z.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es H tm z /\ ghost_kept cenv es sa G tn s H tm
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u` by
    metis_tac[] >>
  `!name a len. local_region cenv es.scopes z name a len ==>
    regions_disjoint b n a len` by
    (drule_all literal_ptr_local_region_frame >> metis_tac[]) >>
  conj_tac
  >- (irule literal_copy_window_ghost_inv >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`G`, `b`, `n`, `s`, `sa`, `tn`] >>
      simp[] >> metis_tac[]) >>
  irule literal_copy_window_ghost_kept >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`b`, `n`, `z`] >> simp[] >> metis_tac[]
QED
