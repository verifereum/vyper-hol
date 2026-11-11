(* Semantic observations of held arguments across fresh copies. *)
Theory bodyIntCallHeldCopyValue
Ancestors
  bodyIntCallHeldArgs bodyIntCallHeldCopyFrame bodyIntCallProducerInterface
  exprSimProps loweringPosts valueEncodingProps context venomState
  exprLoweringProps abiCallerLocalScratch exprSimStorageCopy compileEnv
  bodyIntCallStorageTyped

Theorem held_memory_footprint_frame:
  vv_holds ce cx ty raw vv es s /\
  ((?sty op. vv = StackValue sty op) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  (!v tv w. read_result cx raw es = (INL v,es) /\
            evaluate_type (get_tenv cx) ty = SOME tv /\
            eval_operand (vv_operand vv) s = SOME w ==>
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory) ==>
  vv_holds ce cx ty raw vv es t
Proof
  strip_tac >> Cases_on `vv` >>
  gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]
  >- (rpt strip_tac >> Cases_on `is_word_type ty` >> gvs[] >>
      irule val_in_memory_footprint_agree >>
      metis_tac[]) >>
  rpt strip_tac >>
  `val_in_memory tvt v (w2n w) t.vs_memory` by
    (irule val_in_memory_footprint_agree >> metis_tac[]) >>
  metis_tac[exprSimPropsTheory.val_in_memory_word_type]
QED

Theorem held_footprint_outside_copy:
  vv_at ce cx ty sa sm es raw vv s /\
  ((?sty op. vv = StackValue sty op /\ ~is_word_type ty) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand (vv_operand vv) s = SOME w /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
      lb+sz <= b \/ b+32*n <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
      lb+sz <= b \/ b+32*n <= lb) /\
  u.vs_memory = s.vs_memory /\ copy_prefix loc src b n u k z ==>
  mem_bytes_at (w2n w) (val_footprint tv v) z.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  disch_tac >> Cases_on `val_footprint tv v = 0`
  >- simp[valueEncodingTheory.mem_bytes_at_def] >>
  pop_assum mp_tac >> pop_assum strip_assume_tac >> disch_tac >>
  `w2n w + val_footprint tv v <= b \/ b+32*n <= w2n w` by
    (Cases_on `vv` >>
     gvs[vv_at_def, expr_val_at_def, vv_operand_def] >>
     res_tac >> decide_tac) >>
  metis_tac[exprSimStorageCopyTheory.copy_prefix_bytes]
QED

Theorem held_nonmemory_observation_frame:
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  p.ptr_location <> LocMemory /\
  intcall_vv_provenance ce cx ty sa sm es raw (LocatedValue sty p) s /\
  eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
  contract_storage t = contract_storage s /\
  contract_transient t = contract_transient s ==>
  vv_holds ce cx ty raw (LocatedValue sty p) es t
Proof
  strip_tac >> Cases_on `p.ptr_location` >>
  gvs[vv_holds_def, storage_holds_def] >>
  gvs[intcall_vv_provenance_def, immutable_holds_def] >>
  metis_tac[]
QED

Theorem intcall_held_copy_member:
  intcall_held_args ce cx sa sm es s H /\ MEM (ty,raw,vv) H /\
  eval_operand (vv_operand vv) z = eval_operand (vv_operand vv) s /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
      lb+sz <= b \/ b+32*n <= lb) /\
  (!name lb sz. local_region ce es.scopes s name lb sz ==>
      lb+sz <= b \/ b+32*n <= lb) /\
  u.vs_memory = s.vs_memory /\ copy_prefix loc src b n u k z ==>
  vv_holds ce cx ty raw vv es z
Proof
  strip_tac >> drule_all intcall_held_args_member >> strip_tac >>
  Cases_on `vv`
  >- (Cases_on `is_word_type ty`
      >- gvs[vv_holds_def, expr_val_rel_def, vv_operand_def] >>
      irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >>
      drule held_footprint_outside_copy >>
      disch_then (drule_at (Pat `copy_prefix _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  rename1 `LocatedValue sty p` >> Cases_on `p.ptr_location = LocMemory`
  >- (irule held_memory_footprint_frame >> simp[] >> qexists_tac `s` >> simp[] >>
      rpt strip_tac >>
      drule held_footprint_outside_copy >>
      disch_then (drule_at (Pat `copy_prefix _ _ _ _ _ _ _`)) >>
      simp[] >> metis_tac[]) >>
  irule held_nonmemory_observation_frame >> gvs[vv_operand_def] >> metis_tac[]
QED

(* The actual allocation starts at the old frontier; no additional
   separation premise is needed by the semantic copy boundary. *)
Theorem intcall_held_fresh_copy_holds:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\
  wb_frame ce es sm s z /\ z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  u.vs_memory = s.vs_memory /\
  copy_prefix loc src s.vs_alloca_next n u k z ==>
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
    (rpt strip_tac >> irule abiCallerLocalScratchTheory.abi_caller_local_end >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  irule intcall_held_copy_member >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem intcall_held_fresh_copy_frame:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  wb_frame ce es sm s z /\ z.vs_labels = s.vs_labels /\
  contract_storage z = contract_storage s /\
  contract_transient z = contract_transient s /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
  u.vs_memory = s.vs_memory /\
  copy_prefix loc src s.vs_alloca_next n u k z ==>
  intcall_held_args ce cx sa sn es z H
Proof
  strip_tac >> irule intcall_held_args_holds_frame >> conj_tac
  >- metis_tac[intcall_held_fresh_copy_holds] >>
  qexistsl_tac [`func`, `s`, `sm`] >>
  gvs[stmt_state_rel_def, state_rel_def]
QED

(* All hypotheses below are physical observations exported by the
   allocation and copy paths, at those paths' actual witnesses u and z. *)
Theorem fresh_allocation_copy_wb_frame:
  stmt_state_rel ctx func ce cx es s /\
  aid NOTIN FDOM s.vs_allocas /\
  u.vs_allocas = s.vs_allocas |+ (aid,(s.vs_alloca_next,nb)) /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  sm.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x z = lookup_var x u) /\
  copy_prefix loc src s.vs_alloca_next n u k z ==>
  wb_frame ce es sm s z
Proof
  strip_tac >>
  `z.vs_allocas = u.vs_allocas` by
    metis_tac[copy_prefix_def, copy_static_fields] >>
  `!off len. off+len <= s.vs_alloca_next ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     drule copy_prefix_bytes >> simp[] >> metis_tac[]) >>
  `!name lb sz. local_region ce es.scopes s name lb sz ==>
     lb+sz <= s.vs_alloca_next` by
    (rpt strip_tac >> irule abi_caller_local_end >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at si x` by
        (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[]) 
  >- (rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
      gvs[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  simp[locals_kept_def] >> rpt strip_tac >> first_x_assum irule >>
  res_tac >> decide_tac
QED

Theorem intcall_held_allocation_copy_frame:
  intcall_held_args ce cx sa sm es s H /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  aid NOTIN FDOM s.vs_allocas /\
  u.vs_allocas = s.vs_allocas |+ (aid,(s.vs_alloca_next,nb)) /\
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  sm.cs_next_var <= si.cs_next_var /\
  (!x. not_fresh_at si x ==> lookup_var x z = lookup_var x u) /\
  copy_prefix loc src s.vs_alloca_next n u k z /\
  sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var ==>
  intcall_held_args ce cx sa sn es z H
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (gvs[venom_state_component_equality,
         contract_storage_def, contract_transient_def]) >>
  `z.vs_labels = s.vs_labels /\
   contract_storage z = contract_storage s /\
   contract_transient z = contract_transient s` by
    (`copy_static z = copy_static u` by metis_tac[copy_prefix_def] >>
     drule copy_static_fields >> strip_tac >>
     gvs[contract_storage_def, contract_transient_def]) >>
  `wb_frame ce es sm s z` by
    (irule fresh_allocation_copy_wb_frame >> metis_tac[]) >>
  irule intcall_held_fresh_copy_frame >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

(* Consumer at storage_typed_allocation_path's counted witness. The
   subsequent copy endpoint is supplied, not executed a second time. *)
Theorem storage_allocation_held_copy_tail:
  compile_alloc_buffer nb sm = (buf,si) /\ fn_has_code sm si func /\
  nb < dimword(:256) /\ sm.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ 32 * type_slot_size tv <= nb /\
  (!x. src = Var x ==> not_fresh_at sm x) /\ eval_operand src s = SOME a /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ storage_holds cx tr ty raw a es s /\
  intcall_held_args ce cx sa sm es s H ==>
  ?u b. gas_marked_path F ctx func s 0 (OK u) /\ b = s.vs_alloca_next /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,nb) /\
    (!sn loc from n k z.
      sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var /\
      (!x. not_fresh_at si x ==> lookup_var x z = lookup_var x u) /\
      copy_prefix loc from b n u k z ==>
      intcall_held_args ce cx sa sn es z H)
Proof
  strip_tac >> drule_all storage_typed_allocation_path >> strip_tac >>
  `sm.cs_next_var <= si.cs_next_var` by
    (drule storage_copy_alloc_layout >> simp[]) >>
  qexistsl_tac [`u`, `s.vs_alloca_next`] >> simp[] >>
  rpt gen_tac >> strip_tac >> irule intcall_held_allocation_copy_frame >>
  goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
  metis_tac[]
QED
