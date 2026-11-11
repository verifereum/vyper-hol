(* Location-independent observations below a fresh allocation frontier. *)
Theory bodyIntCallHeldByteFrame
Ancestors
  bodyIntCallHeldCopyValue bodyIntCallHeldCopyFrame bodyIntCallHeldArgs
  loweringPosts context venomState exprLoweringProps abiCallerLocalScratch
  valueEncodingProps compileEnv finite_map

Theorem held_footprint_below_frontier:
  vv_at ce cx ty sa sm es raw vv s /\
  ((?sty op. vv = StackValue sty op /\ ~is_word_type ty) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==> lb+sz <= b) /\
  (!off len. off+len <= b ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  mem_bytes_at (w2n w) (val_footprint tv v) z.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  disch_tac >> Cases_on `val_footprint tv v = 0`
  >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  pop_assum mp_tac >> pop_assum strip_assume_tac >> disch_tac >>
  `w2n w + val_footprint tv v <= b` by
    (Cases_on `vv` >>
     gvs[vv_at_def, expr_val_at_def, vv_operand_def] >>
     res_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem intcall_held_bytes_member:
  intcall_held_args ce cx sa sm es s H /\ MEM (ty,raw,vv) H /\
  eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
     lb+sz <= b) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==> lb+sz <= b) /\
  (!off len. off+len <= b ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  vv_holds ce cx ty raw vv es z
Proof
  strip_tac >> drule_all intcall_held_args_member >> strip_tac >>
  Cases_on `vv`
  >- (Cases_on `is_word_type ty`
      >- gvs[vv_holds_def, expr_val_rel_def, vv_operand_def] >>
      irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> irule held_footprint_below_frontier >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexists_tac `b` >> simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  rename1 `LocatedValue sty p` >> Cases_on `p.ptr_location = LocMemory`
  >- (irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >> irule held_footprint_below_frontier >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[] >> qexists_tac `b` >> simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  irule held_nonmemory_observation_frame >> gvs[vv_operand_def] >> metis_tac[]
QED

Theorem intcall_held_frontier_bytes_holds:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\
  wb_frame ce es sm s z /\ z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!off len. off+len <= s.vs_alloca_next ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  !ty raw vv. MEM (ty,raw,vv) H ==> vv_holds ce cx ty raw vv es z
Proof
  strip_tac >> rpt gen_tac >> disch_tac >>
  drule_all intcall_held_args_member >> strip_tac >>
  `eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s` by
    (drule intcall_held_operand_defined >> strip_tac >>
     Cases_on `vv_operand vv` >> gvs[eval_operand_def, wb_frame_def] >>
     metis_tac[]) >>
  `!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) ==>
     lb+sz <= s.vs_alloca_next` by
    gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >>
  `!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= s.vs_alloca_next` by
    (rpt strip_tac >> irule abi_caller_local_end >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  irule intcall_held_bytes_member >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
  qexists_tac `s.vs_alloca_next` >> simp[] >> metis_tac[]
QED

Theorem fresh_allocation_bytes_wb_frame:
  stmt_state_rel ctx func ce cx es s /\
  aid NOTIN FDOM s.vs_allocas /\
  z.vs_allocas = s.vs_allocas |+ (aid,(s.vs_alloca_next,nb)) /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
  (!off len. off+len <= s.vs_alloca_next ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  wb_frame ce es sm s z
Proof
  strip_tac >>
  `!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= s.vs_alloca_next` by
    (rpt strip_tac >> irule abi_caller_local_end >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >> simp[FLOOKUP_UPDATE] >>
      gvs[FLOOKUP_DEF] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  simp[locals_kept_def] >> rpt strip_tac >> first_x_assum irule >>
  res_tac >> decide_tac
QED

Theorem intcall_held_frontier_bytes_frame:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  wb_frame ce es sm s z /\ z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
  (!off len. off+len <= s.vs_alloca_next ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  intcall_held_args ce cx sa sn es z H
Proof
  strip_tac >> irule intcall_held_args_holds_frame >> conj_tac
  >- metis_tac[intcall_held_frontier_bytes_holds] >>
  qexistsl_tac [`func`, `s`, `sm`] >>
  gvs[stmt_state_rel_def, state_rel_def]
QED

Theorem intcall_held_allocation_bytes_frame:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  aid NOTIN FDOM s.vs_allocas /\
  u.vs_allocas = s.vs_allocas |+ (aid,(s.vs_alloca_next,nb)) /\
  u.vs_memory = s.vs_memory /\ z.vs_allocas = u.vs_allocas /\
  z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  sm.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x z = lookup_var x u) /\
  (!off len. off+len <= s.vs_alloca_next \/ s.vs_alloca_next+nb <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var ==>
  wb_frame ce es sm s z /\ intcall_held_args ce cx sa sn es z H
Proof
  strip_tac >>
  `!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!off len. off+len <= s.vs_alloca_next ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    metis_tac[] >>
  `wb_frame ce es sm s z` by
    (irule fresh_allocation_bytes_wb_frame >> metis_tac[]) >>
  simp[] >> irule intcall_held_frontier_bytes_frame >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >> metis_tac[]
QED
