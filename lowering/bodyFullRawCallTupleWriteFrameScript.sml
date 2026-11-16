(* Exterior writes preserve the original and current pointer ghosts jointly. *)
Theory bodyFullRawCallTupleWriteFrame
Ancestors
  ghostObservationPtr bodyPtrDefs exprSimProps loweringStateRelDefs
  exprLoweringProps ptrDiscipline abiDecodeStaticProps finite_map

Theorem raw_call_tuple_write_frame:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  local_ptrs_reserved cenv sf /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x. not_fresh_at sf x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tnf (Var x) = op_taint tn (Var x)) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  (!i. i NOTIN R ==> mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN R /\ i IN tnf.t_mem ==> i IN tn.t_mem) /\
  (!i. i < lo ==> i NOTIN R) /\
  (!name a m i. local_region cenv es.scopes s name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
  (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
      aid < sf.cs_next_id /\ a <= i /\ i < a+m ==> i NOTIN R) /\
  (!name a m i. local_region cenv es0.scopes s0 name a m /\
      a <= i /\ i < a+m ==> i NOTIN R) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf /\
  (!D. ghost_inv_at D lo dep cenv cx es G tn s ==>
       ghost_inv_at D lo dep cenv cx es Gf tnf t)
Proof
  strip_tac >> conj_tac
  >- (gvs[ghost_kept_at_def] >> rpt strip_tac >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `!p sz. (!name. FLOOKUP cenv.ce_vars name <> SOME (PtrVar (Var p) sz)) \/
           not_fresh_at sf p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!p sz. not_fresh_at sf p ==>
      (ptr_covers Gf tnf p t sz <=> ptr_covers G tn p s sz)` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (irule mem_bytes_at_bytewise >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at D _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_inv_at_def] >> strip_tac >> conj_tac
  >- suspend "locals" >>
  conj_tac >- suspend "return" >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[stor_taint_ok_at_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Resume raw_call_tuple_write_frame[locals]:
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sf p` by metis_tac[] >>
  `ptr_covers Gf tnf p t sz` by metis_tac[] >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `lookup_var p s = SOME w` by metis_tac[] >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (gvs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    (drule val_footprint_le >> decide_tac) >>
  irule robust_val_in_memory_exterior_no_new_taint >>
  conj_tac >- simp[] >>
  qexistsl_tac [`R`, `s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `i < w2n w + sz` by decide_tac >> metis_tac[]
QED

Resume raw_call_tuple_write_frame[return]:
  Cases_on `dep` >- simp[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME pair)` >> PairCases_on `pair` >>
  gvs[return_buf_ptr_def] >> metis_tac[]
QED

Finalise raw_call_tuple_write_frame
