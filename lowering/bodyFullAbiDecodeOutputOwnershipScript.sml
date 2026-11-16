Theory bodyFullAbiDecodeOutputOwnership
Ancestors
  bodyPtrIfExpAllocSeparation exprSimOperands loweringHalt
  revertReasonPrefixPtr ptrDiscipline bufferAllocationExecution
  bodyPtrIfExpAllocSource exprSimProps loweringStateRelDefs loweringPosts exprLoweringProps
  venomExecSemantics venomState venomInst compileEnv finite_map words arithmetic

(* Allocation sites may be revisited.  The base is the site's existing base
   in that case, and the old frontier only for a first visit. *)
Theorem abi_decode_output_ownership_alloc_entry:
  stmt_state_rel H ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sb /\
  compile_alloc_buffer cap sb = (buf,sc) /\ fn_has_code sb sc fn /\
  buf.buf_operand = Var out /\ cap < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w cap)] [out]) s = OK u /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w cap)] [out]) (fn_insts fn) /\
  (mk_inst sb.cs_next_id ALLOCA [Lit (n2w cap)] [out]).inst_opcode = ALLOCA /\
  (mk_inst sb.cs_next_id ALLOCA [Lit (n2w cap)] [out]).inst_outputs = [out] /\
  (mk_inst sb.cs_next_id ALLOCA [Lit (n2w cap)] [out]).inst_id = sb.cs_next_id /\
  not_local_ptr ce es.scopes out /\
  FLOOKUP u.vs_allocas sb.cs_next_id =
    SOME (buffer_allocation_base s sb.cs_next_id,cap) /\
  lookup_var out u = SOME (n2w (buffer_allocation_base s sb.cs_next_id)) /\
  lo <= buffer_allocation_base s sb.cs_next_id /\
  sb.cs_next_id < sc.cs_next_id /\ not_fresh_at sc out /\
  (!name b k. local_region ce es.scopes u name b k ==>
    buffer_allocation_base s sb.cs_next_id + cap <= b \/
    b+k <= buffer_allocation_base s sb.cs_next_id)
Proof
  strip_tac >> drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `out = STRING #"%" (toString sb.cs_next_var)` by gvs[] >>
  `not_local_ptr ce es.scopes out` by
    (irule fresh_not_local_ptr >> qexists_tac `sb` >> simp[]) >>
  drule_all ifexp_alloca_step_site >> strip_tac >>
  drule_all ifexp_alloca_step_base >> strip_tac >>
  `lo <= buffer_allocation_base s sb.cs_next_id` by
    (Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id` >>
     gvs[buffer_allocation_base_def, allocas_from_def] >>
     PairCases_on `x` >> gvs[] >> metis_tac[]) >>
  simp[mk_inst_def] >> rpt strip_tac >>
  `local_region ce es.scopes s name b k` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `fn` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sb`, `es.scopes`, `u`] >> simp[] >>
     metis_tac[]) >>
  drule_all ifexp_alloca_local_separate >>
  simp[buffer_allocation_base_def] >> decide_tac
QED

Theorem abi_decode_output_ownership_transport:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_id = aid /\
  not_local_ptr ce scopes out /\
  FLOOKUP s.vs_allocas aid = SOME (ob,cap) /\
  lookup_var out s = SOME (n2w ob) /\ lo <= ob /\
  (!name b k. local_region ce scopes s name b k ==>
     ob+cap <= b \/ b+k <= ob) /\
  FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid /\
  lookup_var out t = lookup_var out s /\
  (!name b k. local_region ce scopes t name b k ==>
     local_region ce scopes s name b k) ==>
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_id = aid /\
  not_local_ptr ce scopes out /\
  FLOOKUP t.vs_allocas aid = SOME (ob,cap) /\
  lookup_var out t = SOME (n2w ob) /\ lo <= ob /\
  (!name b k. local_region ce scopes t name b k ==>
     ob+cap <= b \/ b+k <= ob)
Proof
  metis_tac[]
QED

Theorem abi_decode_output_ownership_write_bounds:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_id = aid /\
  not_local_ptr ce scopes out /\
  FLOOKUP s.vs_allocas aid = SOME (ob,cap) /\
  lookup_var out s = SOME (n2w ob) /\ lo <= ob /\
  (!name b k. local_region ce scopes s name b k ==>
     ob+cap <= b \/ b+k <= ob) /\
  ob <= a /\ a+n <= ob+cap ==>
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [out] /\ inst.inst_id = aid /\
  not_local_ptr ce scopes out /\
  FLOOKUP s.vs_allocas aid = SOME (ob,cap) /\
  lo <= a /\ ob <= a /\ a+n <= ob+cap /\
  (!name b k. local_region ce scopes s name b k ==>
     a+n <= b \/ b+k <= a)
Proof
  strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> decide_tac
QED

(* Concrete instances of the three premises consumed by transport. *)
Theorem abi_decode_output_ownership_update_frame:
  not_local_ptr ce scopes tmp /\ tmp <> out ==>
  FLOOKUP (update_var tmp w s).vs_allocas aid = FLOOKUP s.vs_allocas aid /\
  lookup_var out (update_var tmp w s) = lookup_var out s /\
  (!name b k. local_region ce scopes (update_var tmp w s) name b k ==>
     local_region ce scopes s name b k)
Proof
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       GSYM update_var_def, local_region_update_nonlocal]
QED

Theorem abi_decode_output_ownership_mstore_frame:
  FLOOKUP (mstore a w s).vs_allocas aid = FLOOKUP s.vs_allocas aid /\
  lookup_var out (mstore a w s) = lookup_var out s /\
  (!name b k. local_region ce scopes (mstore a w s) name b k ==>
     local_region ce scopes s name b k)
Proof
  simp[local_region_def, lookup_var_def, mstore_def]
QED

Theorem abi_decode_output_ownership_mcopy_frame:
  FLOOKUP (mcopy dst src n s).vs_allocas aid = FLOOKUP s.vs_allocas aid /\
  lookup_var out (mcopy dst src n s) = lookup_var out s /\
  (!name b k. local_region ce scopes (mcopy dst src n s) name b k ==>
     local_region ce scopes s name b k)
Proof
  simp[local_region_def, lookup_var_def, mcopy_def, write_memory_with_expansion_def]
QED

Theorem abi_decode_output_ownership_scratch_frame:
  step_inst_base (mk_inst id ALLOCA [Lit sz] [tmp]) s = OK t /\
  id <> aid /\ tmp <> out /\ not_local_ptr ce scopes tmp ==>
  FLOOKUP t.vs_allocas aid = FLOOKUP s.vs_allocas aid /\
  lookup_var out t = lookup_var out s /\
  (!name b k. local_region ce scopes t name b k ==>
     local_region ce scopes s name b k)
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           local_region_def] >> gvs[not_local_ptr_def] >> metis_tac[]) >>
  PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       GSYM update_var_def, local_region_update_nonlocal]
QED
