(* Resource-backed allocation/prelude/decoder composition. *)
Theory entryReachBodyRegistrationSingleton
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyRegistrationAllocation entryReachBodyRegistrationWindows
  entryReachBodySourceInstalledDecoder entryReachBodyScratchCapacity
  calldataRegistrationExec abiEncoderRegisteredEffect abiAllocationHistory
  ctorAbiActualMemory abiCallerAllocation venomMemDefs
  entryReachBodyOwnedRegion entryReachBodyExactArrayLoop abiDecoderContract
  entryReachBodyCanonicalArrayChild entryReachBodyOperationalPath abiDecoderLoop
  compileEnv vyperCompiler venomWf finite_map pred_set words list arithmetic

Theorem registration_scratch_from_history[local]:
  FINITE ambient /\ alloca_frontier_inv ctx fn site s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\
  (!id. id IN ambient ==> ?inst. MEM inst (fn_insts fn) /\
    inst.inst_id = id /\ inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_id IN ambient ==>
    alloca_size inst = 32) ==>
  entry_scratch_ready ambient 0 (unit_alloca_budget ctx) s
Proof
  strip_tac >> irule entry_scratch_ready_global >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`fn`, `site`] >> simp[]) >>
  rpt strip_tac >>
  PairCases_on `r` >> gvs[abi_alloca_history_def] >>
  qpat_x_assum `!id off sz. _` drule >> strip_tac >>
  qpat_x_assum `!inst. MEM inst _ /\ _ ==> _` drule >>
  simp[alloca_size_def]
QED

Theorem registration_resource_decoder_run:
  compile_register_positional_args ce
    [(name,prim,dyn,sz,type_to_abi_dec_info ce.ce_struct_fields ce ty)] off st = (out_ce,last) /\
  FLOOKUP ce.ce_vars name = SOME loc /\ var_location_memory_size loc = SOME n /\
  compile_alloc_buffer n st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (head,after_head) /\
  (if dyn /\ ~prim then ?offset after_load.
     emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
     emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) /\
  compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) first = ((),last) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  entry_source_metadata ce env ce.ce_struct_fields ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty) av value /\
  n = type_memory_size tv /\
  EVERY (entry_abi_support env) tys /\
  LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys values /\
  vyper_to_abi_list env tys values = SOME (pvs ++ av::rest) /\
  MAP (vyper_to_abi_type env) tys = pre ++ vyper_to_abi_type env ty::post /\
  LENGTH pre = LENGTH pvs /\
  E = enc (Tuple (pre ++ vyper_to_abi_type env ty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at 4 (LENGTH E) (abi_decode_source CALLDATALOAD initial) = E /\
  4 + LENGTH E < dimword (:256) /\ off = 4 + SUM (MAP abi_member_head_size pre) /\
  (dyn /\ ~prim <=> is_dynamic (vyper_to_abi_type env ty)) /\
  fn_has_code st allocated fn /\ fn_has_code allocated first fn /\
  fn_has_code first last fn /\ abi_decoder_code first last /\
  fn_inst_ids_distinct fn /\ ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  n < dimword (:256) /\ unit_alloca_budget ctx < dimword (:256) /\
  (!entry. FLOOKUP initial.vs_allocas st.cs_next_id = SOME entry ==>
    ?p. entry = (p,n) /\ p+n < dimword (:256)) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  abi_alloca_history (fn_insts fn) initial /\ fresh_vars_wrt limit_st initial /\
  first.cs_next_var <= limit_st.cs_next_var /\ last.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  st.cs_next_id NOTIN abi_decoder_ids first.cs_next_id last.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id) SUBSET ambient /\
  st.cs_next_id NOTIN ambient /\ FINITE ambient /\
  (!id. id IN ambient ==> ?inst. MEM inst (fn_insts fn) /\
    inst.inst_id = id /\ inst.inst_opcode = ALLOCA /\ alloca_size inst = 32) /\
  (!inst. MEM inst (fn_insts fn) /\ inst.inst_id IN ambient ==> alloca_size inst = 32) /\
  compile_register_positional_args body_ce args next_off last = (cef,registered) /\
  compile_guarded_body cef F key ut iv fbody rt registered = ((),z) /\
  fn_has_code last z fn ==>
  ?ready p t.
    FLOOKUP out_ce.ce_vars name = SOME (PtrVar buf.buf_operand n) /\
    array_child_result ctx fn st.cs_next_id p n ambient
      (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
      0 (unit_alloca_budget ctx) site limit_st first last p tv value ready t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\
    entry_loop_fields initial t /\
    initial.vs_alloca_next <= ready.vs_alloca_next /\ ready.vs_memory = initial.vs_memory /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op initial) /\
    (!id entry. FLOOKUP initial.vs_allocas id = SOME entry ==>
      FLOOKUP ready.vs_allocas id = SOME entry) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP ready.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn initial = r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP out_ce.ce_vars name = SOME (PtrVar buf.buf_operand n)` by
    (drule_all calldataRegistrationTheory.register_singleton_allocated_boundary >>
     strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  drule_all registration_literal_source_window >> strip_tac >>
  drule_all registration_allocation_address_run >> strip_tac >>
  `entry_scratch_ready ambient 0 (unit_alloca_budget ctx) v` by
    (irule registration_scratch_from_history >> simp[] >> qexistsl_tac [`fn`, `site`] >> simp[]) >>
  `entry_owned_region st.cs_next_id p n p (type_memory_size tv) v` by
    simp[entry_owned_region_def] >>
  `p+type_memory_size tv < dimword (:256)` by metis_tac[] >>
  `eval_operand src v = SOME (n2w sb)` by metis_tac[] >>
  `mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
    (abi_decode_source CALLDATALOAD v) = enc (vyper_to_abi_type env ty) av` by
    fs[entry_loop_fields_def, abi_decode_source_def] >>
  `?t. array_child_result ctx fn st.cs_next_id p n ambient
    (window_alloca_sites fn (abi_decoder_ids first.cs_next_id last.cs_next_id))
    0 (unit_alloca_budget ctx) site limit_st first last p tv value v t` by
    (irule entry_source_registration_decoder_endpoint >>
     qpat_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` (irule_at Any) >>
     qpat_assum `entry_source_metadata _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_guarded_body _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_register_positional_args body_ce _ _ _ = _` (irule_at Any) >>
     simp[] >> qexists_tac `sb` >> simp[]) >>
  qexistsl_tac [`v`, `p`, `t`] >> simp[] >>
  qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_child_result_def] >> strip_tac >>
  drule entry_decode_path_sim >> simp[abi_decode_sim_def] >> strip_tac >>
  conj_tac >- fs[entry_loop_fields_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem registration_result_previous_value:
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    first last cell tv value ready t /\
  FLOOKUP ready.vs_allocas old_id = SOME (old_root,old_extent) /\
  old_id <> oid /\ old_id NOTIN ids /\
  old_root <= p /\ p + type_memory_size old_tv <= old_root + old_extent /\
  val_in_memory old_tv old_value p ready.vs_memory /\ val_wf old_tv old_value ==>
  val_in_memory old_tv old_value p t.vs_memory
Proof
  simp_tac bool_ss [array_child_result_def, entry_owned_region_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP t.vs_allocas old_id = SOME (old_root,old_extent)` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `old_root+old_extent <= root \/ root+extent <= old_root` by
    (irule abi_caller_allocation_separate >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `oid` >> simp[]) >>
  irule ctor_actual_registered_value >> simp[] >>
  qexistsl_tac [`ids`, `[(cell,type_memory_size tv)]`, `ready`] >> simp[] >>
  rpt strip_tac >> rename1 `FLOOKUP t.vs_allocas i = SOME (q,k)` >>
  `old_id <> i` by metis_tac[] >>
  `old_root+old_extent <= q \/ q+k <= old_root` by
    (irule abi_caller_allocation_separate >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `t` >> simp[]) >>
  simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED
