(* Held observations survive writes to a disjoint, possibly reused buffer. *)
Theory bodyIntCallReuseHeldFrame
Ancestors
  bodyIntCallHeldByteFrame bodyIntCallHeldCopyValue bodyIntCallHeldCopyFrame
  bodyIntCallHeldArgs bodyIntCallHeldFrame loweringPosts context venomState
  exprLoweringProps compileEnv valueEncodingProps freshWrites

Theorem held_footprint_outside_write:
  vv_at ce cx ty sa sm es raw vv s /\
  ((?sty op. vv = StackValue sty op /\ ~is_word_type ty) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!off len. off+len <= b \/ b+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  mem_bytes_at (w2n w) (val_footprint tv v) z.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  disch_tac >> Cases_on `val_footprint tv v = 0`
  >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  pop_assum mp_tac >> pop_assum strip_assume_tac >> disch_tac >>
  `w2n w + val_footprint tv v <= b \/ b+nb <= w2n w` by
    (Cases_on `vv` >>
     gvs[vv_at_def, expr_val_at_def, vv_operand_def] >>
     res_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem outside_write_wb_frame:
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!off len. off+len <= b \/ b+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  wb_frame ce es sm s z
Proof
  strip_tac >> simp[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!off len. _ ==> _` irule >>
      metis_tac[]) >>
  simp[locals_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!off len. _ ==> _` irule >>
  res_tac >> decide_tac
QED

Theorem intcall_held_write_member:
  intcall_held_args ce cx sa sm es s H /\ MEM (ty,raw,vv) H /\
  eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!off len. off+len <= b \/ b+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  vv_holds ce cx ty raw vv es z
Proof
  strip_tac >> drule_all intcall_held_args_member >> strip_tac >>
  Cases_on `vv`
  >- (Cases_on `is_word_type ty`
      >- gvs[vv_holds_def, expr_val_rel_def, vv_operand_def] >>
      irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> irule held_footprint_outside_write >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexistsl_tac [`b`, `nb`] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  rename1 `LocatedValue sty p` >> Cases_on `p.ptr_location = LocMemory`
  >- (irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> irule held_footprint_outside_write >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexistsl_tac [`b`, `nb`] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule held_nonmemory_observation_frame >> gvs[vv_operand_def] >> metis_tac[]
QED

Theorem intcall_held_outside_write_frame:
  intcall_held_args ce cx sa sm es s H /\
  local_ptrs_rel func ce es.scopes s /\ local_ptrs_reserved ce sm /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
  z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= b \/ b+nb <= lb) /\
  (!off len. off+len <= b \/ b+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var ==>
  wb_frame ce es sm s z /\ intcall_held_args ce cx sa sn es z H
Proof
  strip_tac >>
  `wb_frame ce es sm s z` by
    (irule outside_write_wb_frame >> simp[] >> qexistsl_tac [`b`, `nb`] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  simp[] >> irule intcall_held_args_holds_frame >>
  reverse conj_tac >- (qexistsl_tac [`func`, `s`, `sm`] >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  drule_all intcall_held_args_member >> strip_tac >>
  `eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s` by
    (drule intcall_held_operand_defined >> strip_tac >>
     Cases_on `vv_operand vv` >> gvs[eval_operand_def] >> metis_tac[]) >>
  irule intcall_held_write_member >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`b`, `nb`] >> metis_tac[arithmeticTheory.ADD_COMM]
QED
