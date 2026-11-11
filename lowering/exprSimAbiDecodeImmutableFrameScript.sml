Theory exprSimAbiDecodeImmutableFrame
Ancestors
  exprSimAbiDecodeResources exprSimAbiDecodeSuccessPrefix exprSimAbiDecodeAllocaErasePrefix
  exprSimAbiDecodeProtection exprSimAbiDecodeAllocaErase
  abiEncoderPrefixSafety exprSimAbiDecodeRegionFrame
  exprSimAbiDecodeQuantifiedLift exprSimAbiDecodeEndpointFrame
  exprSimAbiDecodeSetupExec exprSimAbiGasBridge fragExec venomExecProofs
  exprLoweringProps exprSimAbiDecodeCoverageBoundary localPtrsProps venomState venomInst list rich_list
  abiEncoderObserver exprSimAbiDecodeAllocationPreserve venomExecSemantics venomMemProofs
  venomExecProps valueEncodingProofs abiDecoderSiteEffect finite_map

Theorem abi_decode_closed_region_frame[local]:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  q + n <= s.vs_alloca_next /\
  (!id b sz. start.cs_next_id <= id /\ id < final.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz q n) /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> drule abi_decode_output_site_interval >> strip_tac >>
  qpat_x_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `abi_decode_success_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_post_def] >> strip_tac >>
  fs[abi_decode_allocation_floor_def] >>
  `abi_decode_allocation_floor s.vs_alloca_next s.vs_allocas u` by
    simp[abi_decode_allocation_floor_def] >>
  qpat_x_assum `decode_site_effect _ _ _ _ _ _` mp_tac >>
  rewrite_tac[GSYM abi_decode_write_set_def] >> strip_tac >>
  irule (SRULE [] abi_decode_write_set_memory_frame) >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  conj_tac >- decide_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >> asm_rewrite_tac []
QED

Theorem abi_decode_prefix_region_frame:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v /\
  local_prefix ctx fn (frag_observer_cut final) s t /\
  q + n <= s.vs_alloca_next /\
  (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz q n) ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  `!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func` by
    (simp[abi_decode_alloca_ids_def] >> rpt strip_tac >>
     qexists_tac `i` >> simp[] >> first_x_assum irule >> simp[]) >>
  `abi_builtin_decode_output_site start (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty) IN abi_decode_alloca_ids func` by
    (`!i. MEM i (frag_code start final) ==> MEM i (fn_insts fn)` by
       metis_tac[abi_decode_resources_code_member] >>
     drule abi_decode_lower_output_allocation >> strip_tac >>
     metis_tac[]) >>
  drule_all abi_decode_clean_builtin_resources >> strip_tac >>
  `?u. abi_decode_success_closed ce env ty tv bs out d start final ctx func
       (abi_decode_clean_allocas func s) u /\
       local_prefix ctx fn (frag_observer_cut final)
         (abi_decode_clean_allocas func s) u` by
    (mp_tac (Q.INST [`s` |-> `abi_decode_clean_allocas func s`, `n` |-> `k`]
       abi_decode_original_entry_success_prefix) >>
     (impl_tac >- simp[abi_decode_clean_allocas_def, eval_operand_def]) >>
     metis_tac[]) >>
  `local_prefix ctx fn (frag_observer_cut final)
      (abi_decode_clean_allocas func s) (abi_decode_clean_allocas func t)` by
    metis_tac[abi_decode_clean_local_prefix] >>
  `u = abi_decode_clean_allocas func t` by metis_tac[local_prefix_endpoint_unique] >>
  drule_at (Pat `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`)
    abi_decode_closed_region_frame >>
  disch_then (qspecl_then [`q`, `n`, `data`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    irule abi_decode_clean_protected_rows >> goal_assum (drule_at Any) >> metis_tac[])) >>
  simp[]
QED

Theorem abi_decode_prefix_immutable_frame:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v /\
  local_prefix ctx fn (frag_observer_cut final) s t /\
  immutable_alloca_sep func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
  mem_bytes_at off (type_memory_size itv) t.vs_memory =
  mem_bytes_at off (type_memory_size itv) s.vs_memory
Proof
  strip_tac >>
  `off + type_memory_size itv <= s.vs_alloca_next /\
   (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint b sz off (type_memory_size itv))` by
    (qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [immutable_alloca_sep_def] >>
     disch_then (drule_all o CONJUNCT2) >> strip_tac >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  irule abi_decode_prefix_region_frame >> asm_rewrite_tac [] >>
  goal_assum (drule_at (Pat `local_prefix _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_abi_decode _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `abi_builtin_decode_site_resources _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  asm_rewrite_tac [] >> metis_tac[]
QED


(* ===== Window frame: windows clear of the decoder's allocations ===== *)

Definition abi_decode_window_frame_def:
  abi_decode_window_frame func start s t <=>
    !q n. (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             start.cs_next_id <= i.inst_id /\
             FLOOKUP t.vs_allocas i.inst_id = SOME (b,sz) ==>
             loweringStateRelDefs$regions_disjoint q n b sz) ==>
          mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
End

Theorem abi_decode_window_frame_updates[simp]:
  abi_decode_window_frame func start s
    (t with <|vs_returndata := rd; vs_prev_bb := prev|>) =
  abi_decode_window_frame func start s t
Proof
  simp[abi_decode_window_frame_def]
QED

Theorem abi_decode_window_bytewise[local]:
  (!i. q <= i /\ i < q + n ==> mem_bytes_at i 1 m1 = mem_bytes_at i 1 m2) ==>
  mem_bytes_at q n m1 = mem_bytes_at q n m2
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `q + x` mp_tac) >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[valueEncodingProofsTheory.EL_mem_bytes_at]
QED

(* The memory between the old and new allocation frontiers is covered by
   allocations the run made. *)
Theorem abi_decode_step_alloca_tiling[local]:
  step_inst_base inst s = OK t /\ s.vs_alloca_next <= a /\ a < t.vs_alloca_next ==>
  ?id b sz. FLOOKUP s.vs_allocas id = NONE /\ FLOOKUP t.vs_allocas id = SOME (b,sz) /\
    b <= a /\ a < b + sz
Proof
  Cases_on `inst.inst_opcode = ALLOCA` >> strip_tac
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      asm_simp_tac (srw_ss()) [Once step_inst_base_def, AllCaseEqs()] >>
      simp[exec_alloca_def, AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[] >>
      qexists_tac `inst.inst_id` >> gvs[FLOOKUP_UPDATE]) >>
  drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_fields] >>
  `F` suffices_by simp[] >> decide_tac
QED

Theorem abi_decode_observer_alloca_tiling[local]:
  abi_observer_step ctx fn cut s t /\
  s.vs_alloca_next <= a /\ a < t.vs_alloca_next ==>
  ?id b sz. FLOOKUP s.vs_allocas id = NONE /\ FLOOKUP t.vs_allocas id = SOME (b,sz) /\
    b <= a /\ a < b + sz
Proof
  rw[abi_observer_step_def] >> gvs[step_inst_non_invoke] >>
  rpt (qpat_x_assum `eval_phis _ _ = OK _`
    (strip_assume_tac o MATCH_MP eval_phis_preserves_alloca_fields)) >>
  gvs[] >> drule_all abi_decode_step_alloca_tiling >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem abi_decode_local_prefix_alloca_tiling:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !a. s.vs_alloca_next <= a /\ a < t.vs_alloca_next ==>
    ?id b sz. FLOOKUP s.vs_allocas id = NONE /\
      FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz
Proof
  ho_match_mp_tac local_prefix_strongind >> conj_tac
  >- (rpt strip_tac >> `F` suffices_by simp[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >> rpt strip_tac >>
  rename1 `abi_observer_step ctx fn cut s m` >>
  Cases_on `m.vs_alloca_next <= a`
  >- (qpat_x_assum `!a. m.vs_alloca_next <= a /\ _ ==> _` (qspec_then `a` mp_tac) >> impl_tac >- decide_tac >> strip_tac >>
      qexistsl_tac [`id`, `b`, `sz`] >> simp[] >>
      Cases_on `FLOOKUP s.vs_allocas id` >> simp[] >>
      drule_all abi_decode_observer_preserves_allocation >> simp[]) >>
  `a < m.vs_alloca_next` by decide_tac >>
  drule_all abi_decode_observer_alloca_tiling >> strip_tac >>
  qexistsl_tac [`id`, `b`, `sz`] >> simp[] >>
  metis_tac[abi_decode_local_prefix_preserves_allocation]
QED

Theorem abi_decode_closed_window_frame[local]:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decode_success_closed ce env ty tv bs out d start final ctx func s t /\
  (!a. s.vs_alloca_next <= a /\ a < t.vs_alloca_next ==>
     ?id b sz. FLOOKUP s.vs_allocas id = NONE /\
       FLOOKUP t.vs_allocas id = SOME (b,sz) /\ b <= a /\ a < b + sz) /\
  (!id b sz. start.cs_next_id <= id /\ FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
     loweringStateRelDefs$regions_disjoint q n b sz) ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> drule abi_decode_output_site_interval >> strip_tac >>
  qpat_x_assum `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_closed_def] >> strip_tac >>
  qpat_x_assum `abi_decode_success_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_success_post_def] >> strip_tac >>
  qpat_x_assum `decode_site_effect _ _ _ _ s u`
    (strip_assume_tac o REWRITE_RULE [decode_site_effect_def]) >>
  gvs[] >>
  irule abi_decode_window_bytewise >> rpt strip_tac >>
  `!id b sz. start.cs_next_id <= id /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
     ~(b <= i /\ i < b + sz)` by
    (rpt strip_tac >>
     `loweringStateRelDefs$regions_disjoint q n b sz` by metis_tac[] >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  Cases_on `u.vs_alloca_next <= i`
  >- (qpat_x_assum `decode_upper_frame s u` mp_tac >>
      simp_tac bool_ss [decode_upper_frame_def, decode_memory_frame_def] >>
      disch_then irule >> simp[] >> rpt strip_tac >> decide_tac) >>
  `~(s.vs_alloca_next <= i)` by
    (strip_tac >>
     qpat_x_assum `!a. s.vs_alloca_next <= a /\ _ ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- decide_tac >> strip_tac >>
     `start.cs_next_id <= id` by
       (CCONTR_TAC >> `id < start.cs_next_id` by decide_tac >>
        `FLOOKUP u.vs_allocas id = FLOOKUP s.vs_allocas id` by metis_tac[] >>
        fs[]) >>
     metis_tac[]) >>
  qpat_x_assum `decode_memory_frame _ s u` mp_tac >>
  simp_tac bool_ss [decode_memory_frame_def] >> disch_then irule >>
  rpt strip_tac >> `a = i` by decide_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_prefix_window_frame:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
   !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  evaluate_abi_decode env ty bs = INL v /\
  local_prefix ctx fn (frag_observer_cut final) s t ==>
  abi_decode_window_frame func start s t
Proof
  strip_tac >> simp_tac bool_ss [abi_decode_window_frame_def] >> rpt strip_tac >>
  `!i. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func` by
    (simp[abi_decode_alloca_ids_def] >> rpt strip_tac >>
     qexists_tac `i` >> simp[] >> first_x_assum irule >> simp[]) >>
  `abi_builtin_decode_output_site start (abi_static_size ce.ce_struct_fields ty)
      (abi_size_bound ce.ce_struct_fields ty) IN abi_decode_alloca_ids func` by
    (`!i. MEM i (frag_code start final) ==> MEM i (fn_insts fn)` by
       metis_tac[abi_decode_resources_code_member] >>
     drule abi_decode_lower_output_allocation >> strip_tac >>
     metis_tac[]) >>
  drule_all abi_decode_clean_builtin_resources >> strip_tac >>
  `?u. abi_decode_success_closed ce env ty tv bs out d start final ctx func
       (abi_decode_clean_allocas func s) u /\
       local_prefix ctx fn (frag_observer_cut final)
         (abi_decode_clean_allocas func s) u` by
    (mp_tac (Q.INST [`s` |-> `abi_decode_clean_allocas func s`, `n` |-> `k`]
       abi_decode_original_entry_success_prefix) >>
     (impl_tac >- simp[abi_decode_clean_allocas_def, eval_operand_def]) >>
     metis_tac[]) >>
  `local_prefix ctx fn (frag_observer_cut final)
      (abi_decode_clean_allocas func s) (abi_decode_clean_allocas func t)` by
    metis_tac[abi_decode_clean_local_prefix] >>
  `u = abi_decode_clean_allocas func t` by metis_tac[local_prefix_endpoint_unique] >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  `!a. (abi_decode_clean_allocas func s).vs_alloca_next <= a /\
       a < (abi_decode_clean_allocas func t).vs_alloca_next ==>
     ?id b sz. FLOOKUP (abi_decode_clean_allocas func s).vs_allocas id = NONE /\
       FLOOKUP (abi_decode_clean_allocas func t).vs_allocas id = SOME (b,sz) /\
       b <= a /\ a < b + sz` by
    metis_tac[abi_decode_local_prefix_alloca_tiling] >>
  `!id b sz. start.cs_next_id <= id /\
     FLOOKUP (abi_decode_clean_allocas func t).vs_allocas id = SOME (b,sz) ==>
     loweringStateRelDefs$regions_disjoint q n b sz` by
    (rpt gen_tac >> simp[abi_decode_clean_lookup] >> rw[] >>
     fs[abi_decode_alloca_ids_def] >> metis_tac[]) >>
  drule_all abi_decode_closed_window_frame >>
  simp[abi_decode_clean_allocas_def]
QED
