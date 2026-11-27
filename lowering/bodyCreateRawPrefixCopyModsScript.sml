(* RawCreate writes only the live bytecode prefix of the registered buffer. *)
Theory bodyCreateRawPrefixCopyMods
Ancestors
  bodyAbiTupleBufferResourcesMods bodyFullAbiEncodeCopy bodyPtrMakeArrayPrimitiveInstall
  bodyIfExpTypedGhostMods bodyIfExpTypedImmFrameMods placeStoreDynPrepare
  bodyFullPathHistory bodyFullUnwrapRun bodyMemoryDefs reasonCopySourcePtr
  allocaSiteResource exprSimHash exprSimAbiEncodeMemoryLength valueCopy
  assignTuplePtrCopyLen taintAgree memoryReadProps venomExecSemantics
  context words venomInst venomState unitTransformDefs contextCodegenRel codegenRel
  bodyPtrDefs exprLoweringProps loweringStateRelDefs loweringPosts typedMemoryCopy
  bodyFullShadowBodyInv bodyFullPostsMods bodyAbiTupleBufferStateMods stateRelProj
  venomMemDefs ptrDiscipline allocaHistory pred_set memSafeRun
Libs horizonTypeLib

Triviality raw_prefix_mcopy_path:
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ lookup_var root u = SOME (n2w pbase) /\
  lookup_var src u = SOME (n2w source) /\ eval_operand len u = SOME (n2w n) /\
  op_taint tu len = {} /\ ptr_covers Gu tu root u n /\ ptr_covers Gu tu src u n /\
  pbase < dimword (:256) /\ source < dimword (:256) /\ n < dimword (:256) /\
  pbase+n <= u.vs_alloca_next /\ source+n <= u.vs_alloca_next /\
  (!i. source <= i /\ i < source+n ==> i NOTIN tu.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ allocas_from lo u /\
  ~u.vs_halted /\ u.vs_current_bb = a.cs_current_bb /\
  u.vs_inst_idx = LENGTH a.cs_current_insts ==>
  b.cs_current_bb = a.cs_current_bb /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) []
    (OK (mcopy pbase source n u with vs_inst_idx := LENGTH b.cs_current_insts),Gu,
     tu with t_mem := tu.t_mem DIFF {i | pbase <= i /\ i < pbase+n}))
Proof
  rewrite_tac[compile_copy_memory_dynamic_def] >> strip_tac >>
  drule_all_then strip_assume_tac emit_void_fetch_boundary >>
  `w2n (n2w pbase:bytes32) = pbase /\ w2n (n2w source:bytes32) = source /\
   w2n (n2w n:bytes32) = n` by simp[w2n_n2w,arithmeticTheory.LESS_MOD] >>
  qabbrev_tac `i = mk_inst a.cs_next_id MCOPY [Var root;Var src;len] []` >>
  `step_taint i u (mcopy pbase source n u) tu =
   tu with t_mem := tu.t_mem DIFF {j | pbase <= j /\ j < pbase+n}` by
    (`{pbase+q | q < n /\ q+source IN tu.t_mem} = {}` by
       (simp[pred_setTheory.EXTENSION] >> gen_tac >> Cases_on `q < n` >> simp[] >>
        qpat_assum `!i. source <= i /\ i < source+n ==> _`
          (qspec_then `q+source` mp_tac) >> simp[]) >>
     `i.inst_opcode = MCOPY /\ i.inst_outputs = [] /\
      i.inst_operands = [Var root;Var src;len] /\
      eval_operand (Var root) u = SOME (n2w pbase) /\
      eval_operand (Var src) u = SOME (n2w source)`
       by simp[Abbr `i`,mk_inst_def,eval_operand_def] >>
     drule_all_then mp_tac taintAgreeTheory.step_taint_mcopy >>
     simp[pred_setTheory.EXTENSION]) >>
  `get_instruction bb u.vs_inst_idx = SOME i /\
   lookup_block u.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `i`] >>
  `inst_mem_below_frontier i u /\ inst_dload_in_section i u` by
    simp[Abbr `i`,inst_mem_below_frontier_def,inst_dload_in_section_def,mk_inst_def,
         source_memory_read_ranges_def,source_memory_write_ranges_def,
         sized_source_write_range_def,eval_operand_def] >>
  `ptr_covers Gu tu root u (w2n (n2w n:bytes32)) /\
   ptr_covers Gu tu src u (w2n (n2w n:bytes32))` by simp[] >>
  `SUC u.vs_inst_idx = LENGTH b.cs_current_insts` by simp[] >>
  simp[] >> rpt gen_tac >>
  qpat_x_assum `Abbrev (i = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all bodyFullAbiEncodeCopyTheory.abi_encode_mcopy_origin_path >> simp[]
QED

Triviality raw_prefix_copy_frame:
  n <= cap ==>
  let v = mcopy pbase source n u with vs_inst_idx := idx in
    typed_copy_state_frame se pbase n u v /\
    typed_copy_state_frame se pbase cap u v /\
    (!o'. eval_operand o' v = eval_operand o' u) /\
    (!x. lookup_var x v = lookup_var x u) /\
    (!name b sz. local_region ce scopes v name b sz <=>
                 local_region ce scopes u name b sz)
Proof
  simp[LET_THM] >> strip_tac >>
  `!x. lookup_var x (mcopy pbase source n u) = lookup_var x u` by
    simp[mcopy_def,write_memory_with_expansion_def,write_memory_def,lookup_var_def] >>
  `!o'. eval_operand o' (mcopy pbase source n u) = eval_operand o' u` by
    (Cases >> simp[eval_operand_def,mcopy_def,write_memory_with_expansion_def,write_memory_def]) >>
  `!k. n <= k ==> typed_copy_frame pbase k u.vs_memory
                           (mcopy pbase source n u).vs_memory` by
    (simp[typed_copy_frame_def,exprSimAbiEncodeMemoryLengthTheory.abi_encode_mcopy_memory_length] >>
     rpt strip_tac >> irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[typed_copy_state_frame_def,venom_state_component_equality,local_region_def] >>
  simp[mcopy_def,write_memory_with_expansion_def,write_memory_def,
       venom_state_component_equality,lookup_var_def,eval_operand_def]
QED

Theorem raw_create_prefix_copy_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    inst.inst_id pbase cap root root 0 [] a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  compile_copy_memory_dynamic (Var root) (Var src) len a = ((),b) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
  FLOOKUP Gu root = SOME (pbase,cap) /\
  LENGTH bs <= cap /\ pbase+cap < dimword (:256) /\ pbase+cap <= u.vs_alloca_next /\
  source < dimword (:256) /\ source+LENGTH bs <= u.vs_alloca_next /\
  lookup_var src u = SOME (n2w source) /\ ptr_covers Gu tu src u (LENGTH bs) /\
  eval_operand len u = SOME (n2w (LENGTH bs)) /\ op_taint tu len = {} /\ op_prov Gu len = NONE /\
  read_memory source (LENGTH bs) u = bs /\
  (!i. source <= i /\ i < source+LENGTH bs ==> i NOTIN tu.t_mem) ==>
  let v = mcopy pbase source (LENGTH bs) u with vs_inst_idx := LENGTH b.cs_current_insts in
  let tv = tu with t_mem := tu.t_mem DIFF {i | pbase <= i /\ i < pbase+LENGTH bs} in
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      inst.inst_id pbase cap root root 0 [] b v Gu tv /\
    read_memory pbase (LENGTH bs) v = bs /\
    (!i. pbase <= i /\ i < pbase+LENGTH bs ==> i NOTIN tv.t_mem) /\
    (!x. lookup_var x v = lookup_var x u) /\
    (!op. op_taint tv op = op_taint tu op) /\
    eval_operand len v = SOME (n2w (LENGTH bs)) /\ op_taint tv len = {} /\ op_prov Gu len = NONE /\
    FLOOKUP Gu root = SOME (pbase,cap) /\ FLOOKUP v.vs_allocas inst.inst_id = SOME (pbase,cap) /\
    pbase+cap < dimword (:256) /\ pbase+cap <= v.vs_alloca_next /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gu,tv))
Proof
  simp_tac pure_ss [LET_THM] >> strip_tac >>
  drule_then (fn th => mp_tac th >> impl_tac >- (qexists_tac `H` >> first_assum ACCEPT_TAC) >> strip_tac)
    abi_tuple_buffer_resources_mods >>
  qhdtm_x_assum `abi_tuple_buffer_state_mods`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  `ptr_covers Gu tu root u (LENGTH bs)` by
    (irule ptr_covers_mono >> qexists_tac `cap` >> simp[]) >>
  `LENGTH bs < dimword (:256) /\ pbase < dimword (:256) /\
   pbase+LENGTH bs <= u.vs_alloca_next` by decide_tac >>
  `lookup_var root u = SOME (n2w pbase)` by fs[eval_operand_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by simp[] >>
  drule_all_then (qspec_then `PG` strip_assume_tac) raw_prefix_mcopy_path >>
  qabbrev_tac `v = mcopy pbase source (LENGTH bs) u with vs_inst_idx := LENGTH b.cs_current_insts` >>
  qabbrev_tac `tv = tu with t_mem := tu.t_mem DIFF {i | pbase <= i /\ i < pbase+LENGTH bs}` >>
  `ci_mono a b` by
    (qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
       (assume_tac o REWRITE_RULE [compile_copy_memory_dynamic_def]) >>
     qspecl_then [`MCOPY`,`[Var root;Var src;len]`,`a`] mp_tac ci_mono_emit_void >> simp[]) >>
  `se.cs_next_var <= b.cs_next_var /\ not_fresh_at b root /\ inst.inst_id < b.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `typed_copy_state_frame se pbase (LENGTH bs) u v /\
   typed_copy_state_frame se pbase cap u v /\
   (!op. eval_operand op v = eval_operand op u) /\
   (!x. lookup_var x v = lookup_var x u) /\
   (!name b sz. local_region ce ee.scopes v name b sz <=>
                local_region ce ee.scopes u name b sz)` by
        (simp_tac pure_ss [Abbr `v`] >>
     irule (SIMP_RULE pure_ss [LET_THM] raw_prefix_copy_frame) >> simp[]) >>
  `v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next /\
   v.vs_current_bb = b.cs_current_bb /\ v.vs_inst_idx = LENGTH b.cs_current_insts /\
   ~v.vs_halted /\ v.vs_accounts = u.vs_accounts /\
   v.vs_transient = u.vs_transient /\ v.vs_call_ctx = u.vs_call_ctx /\
   v.vs_immutables = u.vs_immutables /\ v.vs_data_section = u.vs_data_section` by
    simp[Abbr `v`,mcopy_def,write_memory_with_expansion_def,write_memory_def] >>
  `tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
   (!op. op_taint tv op = op_taint tu op) /\ tv.t_mem SUBSET tu.t_mem /\
   (!i. ~(pbase <= i /\ i < pbase+LENGTH bs) ==> (i IN tv.t_mem <=> i IN tu.t_mem))` by
    (simp[Abbr `tv`,SUBSET_DEF] >> Cases >> simp[op_taint_def]) >>
  `read_memory pbase (LENGTH bs) v = read_memory pbase (LENGTH bs) (mcopy pbase source (LENGTH bs) u)` by
    simp[Abbr `v`,read_memory_def] >>
  reverse conj_tac
  >- simp[memoryReadPropsTheory.read_memory_mcopy_self,Abbr `tv`] >>
  suspend "buffer"
QED

Resume raw_create_prefix_copy_mods[buffer]:
  `lo <= pbase` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func ce cx ee v /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at_mods (DF H) lo d ce cx ee Gu tv v /\ immutable_frame_mods func ce cx ee v` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     `!name b sz. local_region ce ee.scopes u name b sz ==>
                 regions_disjoint pbase (LENGTH bs) b sz` by
       (rpt strip_tac >> drule_all_then mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     conj_tac >- (drule_all_then ACCEPT_TAC place_typed_copy_alloca_state_frame) >>
     simp[] >> conj_tac
     >- (irule ifexp_typed_copy_ghost_mods >>
         qpat_assum `typed_copy_state_frame _ _ (LENGTH bs) _ _` (irule_at Any) >>
         qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ u` (irule_at Any) >>
         qpat_assum `local_ptrs_rel func _ _ _` (irule_at Any) >>
         simp[] >> first_assum ACCEPT_TAC) >>
     drule_all_then ACCEPT_TAC ifexp_typed_immutable_frame_mods) >>
  `alloca_history func v` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK v,Gu,tv)`
       (qspecl_then [`DF H`,`explicit`] (mp_then Any mp_tac body_full_path_alloca_history)) >>
     simp[]) >>
  `return_buf_frame d ce b v` by
    (irule return_buf_frame_frame >> qpat_assum `return_buf_frame _ _ a u` (irule_at Any) >>
     fs[ci_mono_def]) >>
  `ptr_covers Gu tv root v cap` by
    (irule ptr_covers_lookup_frame >> qpat_assum `ptr_covers Gu tu root u cap` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo ce ee se G tn s Gu tv` by
    (irule ghost_kept_at_clean_suffix >>
     qhdtm_assum `ghost_kept_at` (irule_at Any) >> simp[]) >>
  `!off k. off+k <= pbase \/ pbase+LENGTH bs <= off ==>
           mem_bytes_at off k v.vs_memory = mem_bytes_at off k u.vs_memory` by
    (qpat_assum `typed_copy_state_frame _ _ (LENGTH bs) _ _`
       (mp_tac o REWRITE_RULE [typed_copy_state_frame_def,typed_copy_frame_def]) >>
     simp_tac pure_ss [] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!aid off k. aid < se.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (off,k) ==>
              mem_bytes_at off k v.vs_memory = mem_bytes_at off k u.vs_memory` by
    (rpt gen_tac >> strip_tac >>
     `inst.inst_id <> aid` by decide_tac >>
     drule_all_then mp_tac alloca_site_registered_disjoint >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> strip_tac
     >- (`LENGTH bs = 0` by decide_tac >>
         `v.vs_memory = (mcopy pbase source 0 u).vs_memory` by simp[Abbr `v`] >>
         qpat_assum `v.vs_memory = _` SUBST1_TAC >>
         PURE_REWRITE_TAC[GSYM read_memory_eq_mem_bytes_at] >> simp[read_memory_mcopy_zero])
     >- simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
     qpat_assum `!off k. _ ==> mem_bytes_at off k v.vs_memory = _` irule >> decide_tac) >>
  `!name off k. local_region ce ee.scopes u name off k ==>
               mem_bytes_at off k v.vs_memory = mem_bytes_at off k u.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     drule_all_then mp_tac localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> strip_tac >>
     qpat_assum `!off k. _ ==> mem_bytes_at off k v.vs_memory = _` irule >> decide_tac) >>
  `wb_frame ce ee ee se s v` by
    (irule wb_frame_allocating_tail >>
     qpat_assum `wb_frame _ _ _ _ _ u` (irule_at Any) >>
     qexistsl_tac [`se`,`ee.scopes`] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[abi_tuple_buffer_state_mods_def,read_memory_def] >>
  suspend "saved_intervals"
QED

Resume raw_create_prefix_copy_mods[saved_intervals]:
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ v /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  qx_genl_tac [`off`,`k`] >> disch_tac >>
  qpat_assum `!b n. _ ==> mem_bytes_at b n u.vs_memory = _ /\ _`
    (drule_then strip_assume_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> fs[SUBSET_DEF]) >>
  qpat_assum `mem_bytes_at _ _ u.vs_memory = mem_bytes_at _ _ s.vs_memory`
    (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  qpat_x_assum `off = 0 /\ _ \/ _` strip_assume_tac
  >- (gvs[] >> qpat_assum `!off k. _ ==> mem_bytes_at off k v.vs_memory = _` irule >> simp[])
  >- (qpat_assum `!name off k. local_region _ _ u name off k ==> _` irule >>
      qpat_assum `local_region ce ee.scopes s _ _ _`
        (qx_choosel_then [`entry`,`p`,`w`] strip_assume_tac o REWRITE_RULE[local_region_def]) >>
      rename1 `lookup_scopes id ee.scopes = SOME entry` >>
      `not_fresh_at se p` by
        (qpat_assum `local_ptrs_reserved ce se` (strip_assume_tac o REWRITE_RULE[local_ptrs_reserved_def]) >>
         qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP ce.ce_vars n1 = _ ==> _`
           (drule_then (qspecl_then [`id`,`k`] mp_tac)) >> simp[]) >>
      `lookup_var p u = SOME w` by
        (irule exprSimWordArgsTheory.wb_frame_vars >>
         qpat_assum `wb_frame _ _ _ _ _ u` (irule_at Any) >> simp[]) >>
      qexists_tac `id` >> simp[local_region_def] >> qexists_tac `p` >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas old = SOME (off,k)` >>
  `FLOOKUP u.vs_allocas old = SOME (off,k)` by
    (qpat_assum `wb_frame _ _ _ _ _ u` (strip_assume_tac o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  qpat_assum `!aid off k. aid < se.cs_next_id /\ _ ==> mem_bytes_at off k v.vs_memory = _`
    irule >> qexists_tac `old` >> simp[]
QED

Finalise raw_create_prefix_copy_mods
