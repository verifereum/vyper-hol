Theory calldataNoneArrayFold
Ancestors
  vyperCalldata fragGasOriginPtr arithmetic list
  calldataInitSequence calldataInitLocalFrontier calldataRecursiveProducers
  decoderArrayInitPtr decoderNavigationPtr decoderLoopHeaderCorePtr
  entrySinkExtraction abiDecoderArrayInit abiDecoderArrayLoopInit
  abiDecoderIndexInit abiDecoderContract abiDecoderReentry abiDecoderExecution
  abiDecoderDynarrayPrefix allocaFrontierBound lowerDloadPtrTaint
  abiDecoderGuards emitHelper calldataCountGuardRejectOrigin calldataNoneArrayIteration
  abiDecoderCoherence calldataSourceCorrespondence calldataSourceSize calldataSourceDecisions
  abiDecoderFrame abiCallerAllocation abiDecoderCounters abiDecoderRecursiveLoopLayout
  gasOriginPtrLabels
  calldataDynInit fragBlockPath valueEncoding exprLowering abiDecoderLoopEmit entryDecoderStateFrame
  compileEnv emitHelperProps venomState venomInst venomExecSemantics
  venomMemDefs bodyPtrDefs ptrSafetyTransport codegenRel contextCodegenRel
  loweringStateRelDefs words finite_map pred_set ptrDiscipline
Libs
  BasicProvers

(* Count down the number of unexecuted elements, rather than assuming a
   running loop can reach the exit independently of its child outcomes. *)
Theorem none_nonbulk_suffix_paths[local]:
  (!i s G tn. i < cnt /\ H i s G tn ==>
    (?z B u. z.vs_returndata = [] /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort z,B,u)) \/
    ?t B u. H (SUC i) t B u /\
      IS_SOME (cd_decode F cd tv (cd_member_ptr F cd tv arr_head (i * tv_abi_size tv))) /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,B,u)) /\
  (!s G tn. H cnt s G tn ==>
    ?t B u. R t B u /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,B,u)) ==>
  !n i s G tn. i + n = cnt /\ H i s G tn ==>
    (?z B u. z.vs_returndata = [] /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (Abort Revert_abort z,B,u)) \/
    ?t B u. R t B u /\ IS_SOME (cd_decode_elems F cd tv arr_head i n) /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,G,tn) [] (OK t,B,u)
Proof
  strip_tac >> Induct
  >- (simp[cd_decode_def] >> rpt strip_tac >> disj2_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `i < cnt /\ SUC i + n = cnt` by decide_tac >>
  qpat_x_assum `!i s G tn. i < cnt /\ _ ==> _`
    (qspecl_then [`i`, `s`, `G`, `tn`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac
  >- (disj1_tac >> metis_tac[]) >>
  rename1 `H (SUC i) m M v` >>
  qpat_x_assum `!i s G tn. i + n = cnt /\ _ ==> _`
    (qspecl_then [`SUC i`, `m`, `M`, `v`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj1_tac >> goal_assum (drule_at Any) >> rpt gen_tac >>
      metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL]) >>
  disj2_tac >> goal_assum (drule_at Any) >>
  conj_tac
  >- (simp[cd_decode_def, ADD1] >> every_case_tac >> gvs[ADD1]) >>
  rpt gen_tac >> metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL]
QED

(* Only the actual counter site needs allocation credit. *)
Theorem none_array_first_header:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn asz st = ((ip,cnt),ls) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),gs) /\
  abi_decode_array_header (Var root) src CALLDATALOAD gs = (cnt,hs) /\
  abi_decode_index_init hs = (ip,ls) /\
  fn_has_code st ls fn /\
  (!ins. MEM ins (emitted_insts hs ls) ==> MEM ins (fn_insts fn)) /\
  lookup_block ls.cs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (LENGTH ls.cs_current_insts) = SOME (mk_inst jid JMP [Label hdr] []) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ unit_alloca_budget ctx < dimword(:256) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src s = SOME sw /\ lookup_var root s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var (Var root) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\ ptr_covers G tn root s sz /\
  d < dimword(:256) /\ 32 <= sz /\ d+sz <= s.vs_alloca_next /\
  w2n (abi_decode_load CALLDATALOAD sw s) <= maxn MOD dimword(:256) /\
  ((FLOOKUP s.vs_allocas hs.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
   (FLOOKUP s.vs_allocas hs.cs_next_id = SOME (p,32) /\ p < dimword(:256) /\ p+32 <= s.vs_alloca_next)) /\
  p+32 < dimword(:256) /\ (d+sz <= p \/ p+32 <= d) ==>
  ?v H u q. ip = Var q /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,H,u)) /\
    ~v.vs_halted /\ v.vs_current_bb = hdr /\ v.vs_inst_idx = 0 /\
    lookup_var q v = SOME (n2w p) /\ ptr_covers H u q v 32 /\
    ptr_covers H u root v sz /\ mload p v = 0w /\
    mem_word_at d v.vs_memory = abi_decode_load CALLDATALOAD sw s /\
    op_taint u src = {} /\ op_prov H src = NONE /\ eval_operand src v = SOME sw /\
    v.vs_call_ctx = s.vs_call_ctx /\ v.vs_data_section = s.vs_data_section /\
    allocas_from lo v /\ p+32 <= v.vs_alloca_next /\ s.vs_alloca_next <= v.vs_alloca_next /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\
    (!id. id <> hs.cs_next_id ==> FLOOKUP v.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    FLOOKUP v.vs_allocas hs.cs_next_id = SOME (p,32) /\
    (!id b cap. FLOOKUP s.vs_allocas id = SOME (b,cap) ==> FLOOKUP v.vs_allocas id = SOME (b,cap)) /\
    (!limit. fresh_vars_wrt limit s /\ ls.cs_next_var <= limit.cs_next_var ==> fresh_vars_wrt limit v) /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
      mem_bytes_at a n v.vs_memory = mem_bytes_at a n s.vs_memory) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = (tn.t_mem DIFF {x | d <= x /\ x < d+32}) DIFF {x | p <= x /\ x < p+32} /\
    (!x. not_fresh_at st x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (maxn MOD dimword(:256)) asz st = ((ip,cnt),ls) /\
   abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w)
    (maxn MOD dimword(:256)) asz st = ((),gs)` by
    (simp[abi_decode_array_loop_init_def,abi_decode_dynarray_position_prefix_def,
          abi_decode_dynarray_prefix_def,abi_decode_count_guard_def,n2w_mod] >>
     qpat_assum `abi_decode_array_loop_init _ _ _ _ _ maxn _ _ = _` mp_tac >>
     qpat_assum `abi_decode_dynarray_prefix _ _ _ maxn _ _ = _` mp_tac >>
     simp[NoAsms,abi_decode_array_loop_init_def,abi_decode_dynarray_position_prefix_def,
          abi_decode_dynarray_prefix_def,abi_decode_count_guard_def,n2w_mod]) >>
  `maxn MOD dimword(:256) < dimword(:256)` by simp[] >>
  drule_all calldata_array_loop_init_repeat_sequence >> strip_tac >>
  drule_all calldata_index_init_local_frontier_fields >> strip_tac >>
  `not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[]) >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `ls.cs_next_id - 2 = hs.cs_next_id` by decide_tac >>
  `s.vs_alloca_next < dimword(:256)` by (fs[alloca_frontier_inv_def] >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `(FLOOKUP s.vs_allocas (ls.cs_next_id - 2) = NONE /\ s.vs_alloca_next+32 < dimword(:256)) \/
     (?r. FLOOKUP s.vs_allocas (ls.cs_next_id - 2) = SOME (r,32) /\
         r+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256))`
    >- metis_tac[] >>
  drule_all actual_array_init_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`]
    (qx_choosel_then [`HG`,`u`,`q`,`header_base`] strip_assume_tac)) >>
  suspend "finish"
QED

Resume none_array_first_header[finish]:
  `header_base = p` by
    (qpat_assum `(FLOOKUP s.vs_allocas hs.cs_next_id = NONE /\ _) \/ _`
       strip_assume_tac >> gvs[]) >>
  `d + 32 <= s.vs_alloca_next` by decide_tac >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ls.cs_current_insts),HG,u)` by
    (rpt gen_tac >> first_assum irule >> simp[]) >>
  `~t.vs_halted /\ t.vs_current_bb = ls.cs_current_bb` by
    (drule abi_decode_array_loop_init_shape >>
     simp[abi_decode_source_opcode_def] >> strip_tac >>
     drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  `op_taint u src = {} /\ op_prov HG src = NONE` by
    (Cases_on `src` >> fs[op_taint_def,op_prov_def] >> metis_tac[]) >>
  `lo <= p /\ p+32 <= t.vs_alloca_next` by
    (qpat_assum `(FLOOKUP s.vs_allocas hs.cs_next_id = NONE /\ _) \/ _`
       strip_assume_tac >> fs[allocas_from_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (fs[allocas_from_def] >> rpt strip_tac >>
     Cases_on `aid = hs.cs_next_id` >> gvs[] >> metis_tac[]) >>
  qexistsl_tac [`jump_to hdr t`,`HG`,`u`,`q`] >>
  conj_tac >- fs[] >>
  conj_tac
  >- (rpt gen_tac >>
      `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (t with vs_inst_idx := LENGTH ls.cs_current_insts,HG,u) []
        (OK (jump_to hdr t),HG,u)` by
        (`jump_to hdr t = jump_to hdr (t with vs_inst_idx := LENGTH ls.cs_current_insts)` by
           simp[jump_to_def] >> pop_assum SUBST1_TAC >>
         irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
         simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
      metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  `lookup_var q t = SOME (n2w p)` by
    gvs[eval_operand_def] >>
  `ptr_covers HG u q (jump_to hdr t) 32 /\ ptr_covers HG u root (jump_to hdr t) sz` by
    (qpat_assum `ptr_covers HG u q (t with vs_inst_idx := _) 32` mp_tac >>
     qpat_assum `ptr_covers HG u root (t with vs_inst_idx := _) sz` mp_tac >>
     simp[NoAsms,ptr_covers_def,jump_to_def,lookup_var_def]) >>
  `eval_operand src (jump_to hdr t) = SOME sw` by
    (`eval_operand src t = SOME sw` by metis_tac[] >>
     Cases_on `src` >> fs[eval_operand_def,lookup_var_def,jump_to_def]) >>
  `alloca_inv (jump_to hdr t)` by
    (qpat_assum `alloca_inv t` mp_tac >>
     simp[NoAsms,jump_to_def,alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def]) >>
  `alloca_frontier_inv ctx fn site (jump_to hdr t)` by
    (qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     simp[NoAsms,jump_to_def,alloca_frontier_inv_def,
          allocaBudgetPropsTheory.remaining_alloca_budget_def]) >>
  `allocas_from lo (jump_to hdr t)` by
    (qpat_assum `allocas_from lo t` mp_tac >> simp[NoAsms,jump_to_def,allocas_from_def]) >>
  `!limit. fresh_vars_wrt limit (jump_to hdr t) = fresh_vars_wrt limit t` by
    simp[jump_to_def,fresh_vars_wrt_def] >>
  `!x. lookup_var x (jump_to hdr t) = lookup_var x t` by
    simp[jump_to_def,lookup_var_def] >>
  `mload p (jump_to hdr t) = mload p t` by simp[NoAsms,jump_to_def,mload_def] >>
  simp[jump_to_def] >> metis_tac[]
QED

Finalise none_array_first_header

(* The final comparison executes the same header, but no child or backedge. *)
Theorem none_array_final_header[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    abi_decode_header_insts id (Var q) src CALLDATALOAD iv cv cmp done body_lbl exit_lbl /\
  s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ALL_DISTINCT [q;iv;cv;cmp;done] /\ src <> Var iv /\
  ptr_covers G tn q s 32 /\ lookup_var q s = SOME (n2w slot) /\
  slot + 32 < dimword (:256) /\ slot + 32 <= s.vs_alloca_next /\
  mload slot s = n2w cnt /\ DISJOINT {a | slot <= a /\ a < slot+32} tn.t_mem /\
  eval_operand src s = SOME sw /\ op_taint tn src = {} /\
  abi_decode_load CALLDATALOAD sw s = n2w cnt /\ cnt < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block body_lbl fn.fn_blocks = SOME body_bb /\
  phi_prefix_length body_bb.bb_instructions = 0 /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 ==>
  ?v H u.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK v,H,u)) /\
    ~v.vs_halted /\ v.vs_current_bb = exit_lbl /\ v.vs_inst_idx = 0 /\
    v.vs_call_ctx = s.vs_call_ctx /\ v.vs_data_section = s.vs_data_section /\
    v.vs_allocas = s.vs_allocas /\ v.vs_alloca_next = s.vs_alloca_next /\
    v.vs_memory = s.vs_memory /\
    (alloca_inv s ==> alloca_inv v) /\
    (!site. alloca_frontier_inv ctx fn site s ==> alloca_frontier_inv ctx fn site v) /\
    allocas_from lo v /\
    (!limit. fresh_vars_wrt limit s /\
       (!x. MEM x [iv;cv;cmp;done] ==> ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
       ==> fresh_vars_wrt limit v) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. ~MEM x [iv;cv;cmp;done] ==>
       lookup_var x v = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
       op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by simp[] >>
  `cnt <= cnt` by simp[] >>
  drule_all (Q.INST [`j` |-> `cnt`, `ncount` |-> `cnt`]
    decoder_index_header_ptr_core_uniform_origin) >>
  disch_then (qspec_then `PG` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`jump_to exit_lbl (abi_decode_header_state iv cv cmp done cnt cnt s)`,`H`,`u`] >>
  conj_tac >- simp[] >>
  `!limit. fresh_vars_wrt limit s /\
     (!x. MEM x [iv;cv;cmp;done] ==> ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
     ==> fresh_vars_wrt limit (jump_to exit_lbl (abi_decode_header_state iv cv cmp done cnt cnt s))` by
    (gen_tac >> strip_tac >>
     irule (cj 1 (Q.INST [`t` |-> `jump_to lbl (abi_decode_header_state iv cv cmp done j ncount s)`]
                    decoder_index_header_replay_frame)) >> asm_rewrite_tac[]) >>
  pop_assum mp_tac >>
  qpat_assum `allocas_from lo s` mp_tac >>
  simp[jump_to_def,abi_decode_header_state_def,update_var_def,
       alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def,
       alloca_frontier_inv_def,allocaBudgetPropsTheory.remaining_alloca_budget_def,
       lookup_var_def,allocas_from_def] >>
  disch_tac >> conj_tac >- fs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

(* The count failure occurs before the header store and counter allocation. *)
Theorem none_array_count_reject[local]:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),gs) /\
  abi_decode_array_header (Var root) src CALLDATALOAD gs = (cnt,hs) /\
  abi_decode_index_init hs = (ip,ls) /\ fn_has_code st ls fn /\
  eval_operand src s = SOME sw /\ abi_decoder_operand_live st.cs_next_var src /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD sw s) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?z H u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (Abort Revert_abort z,H,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?cop. abi_decode_count_guard CALLDATALOAD src maxn st = (cop,gs)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def,abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
          comp_bind_def,comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `cs_extends st gs /\ cs_extends gs ls` by
    (conj_tac >> irule cs_extends_same_block >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[inst_extends_trans,inst_extends_def]) >>
  `fn_has_code st gs fn` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all calldata_count_guard_rejected_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`z`,`H`,`u`] >> asm_rewrite_tac[]
QED

(* A child certificate is used only at the actually installed child interval. *)
Theorem none_nonbulk_fold_paths:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) st = ((),last) /\
  fn_has_code st last fn /\ fn_inst_ids_distinct fn /\ last.cs_next_var <= limit.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  (last.cs_current_insts = [] ==> !bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  eval_operand src initial = SOME sw /\ eval_operand (Var root) initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var (Var root) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\ FLOOKUP initial.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+owner_cap /\
  d+(32+maxn*type_memory_size tv) < dimword (:256) /\
  ptr_covers G tn root initial (32+maxn*type_memory_size tv) /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  fresh_vars_wrt limit initial /\ allocas_from lo initial /\ lo <= initial.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!a b child sop s p e A ta.
    compile_abi_decode_to_buf (Var child) sop CALLDATALOAD (Lit 0w) (Lit 0w)
      (type_to_abi_dec_info sf ce ty) a = ((),b) /\
    fn_has_code a b fn /\ b.cs_next_var <= limit.cs_next_var /\
    (b.cs_current_insts = [] ==> !bb. lookup_block b.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    eval_operand sop s = SOME p /\ eval_operand (Var child) s = SOME (n2w e) /\
    abi_decoder_operand_live a.cs_next_var sop /\ abi_decoder_operand_live a.cs_next_var (Var child) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    (!id q k. a.cs_next_id <= id /\ id < b.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < a.cs_next_id \/ b.cs_next_id <= oid) /\
    base_addr <= e /\ e+type_memory_size tv <= base_addr+owner_cap /\
    e+type_memory_size tv < dimword (:256) /\ ptr_covers A ta child s (type_memory_size tv) /\
    op_taint ta sop = {} /\ op_prov A sop = NONE /\
    fresh_vars_wrt limit s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
    (?z B u. z.vs_returndata = [] /\
        !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,A,ta) [] (Abort Revert_abort z,B,u)) \/
    ?r sc B u. IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p)) /\
      ~r.vs_halted /\ r.vs_current_bb = b.cs_current_bb /\ r.vs_inst_idx = LENGTH b.cs_current_insts /\
      r.vs_call_ctx = s.vs_call_ctx /\ r.vs_data_section = s.vs_data_section /\
      alloca_inv r /\ alloca_frontier_inv ctx fn site r /\ allocas_from lo r /\
      (!id q k. a.cs_next_id <= id /\ id < b.cs_next_id /\ FLOOKUP r.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= r.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      s.vs_alloca_next <= r.vs_alloca_next /\
      (!id q k. FLOOKUP s.vs_allocas id = SOME (q,k) ==> FLOOKUP r.vs_allocas id = SOME (q,k)) /\
      (!id. id < a.cs_next_id \/ b.cs_next_id <= id ==> FLOOKUP r.vs_allocas id = FLOOKUP s.vs_allocas id) /\
      (!op. abi_decoder_operand_live a.cs_next_var op ==> eval_operand op r = eval_operand op s) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::sc) s r /\
      (!q k. MEM (q,k) sc ==> ?id. a.cs_next_id <= id /\ id < b.cs_next_id /\ FLOOKUP r.vs_allocas id = SOME (q,k)) /\
      fresh_vars_wrt limit r /\
      (!x. not_fresh_at a x ==> FLOOKUP B x = FLOOKUP A x /\ op_taint u (Var x) = op_taint ta (Var x)) /\
      u.t_mem SUBSET ta.t_mem /\ u.t_stor = ta.t_stor /\ u.t_trans = ta.t_trans /\ u.t_imm = ta.t_imm /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,A,ta) [] (OK r,B,u)) ==>
  (?z B u. z.vs_returndata = [] /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (initial,G,tn) [] (Abort Revert_abort z,B,u)) \/
  ?v sc B u. IS_SOME (cd_decode F initial.vs_call_ctx.cc_calldata (ArrayTV tv (Dynamic maxn)) (w2n sw)) /\
    ~v.vs_halted /\ v.vs_current_bb = last.cs_current_bb /\ v.vs_inst_idx = LENGTH last.cs_current_insts /\
    v.vs_call_ctx = initial.vs_call_ctx /\ v.vs_data_section = initial.vs_data_section /\
    alloca_inv v /\ alloca_frontier_inv ctx fn site v /\ allocas_from lo v /\
    (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\ FLOOKUP v.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= v.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= v.vs_alloca_next /\
    (!id p k. FLOOKUP initial.vs_allocas id = SOME (p,k) ==> FLOOKUP v.vs_allocas id = SOME (p,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==> FLOOKUP v.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op v = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::sc) initial v /\
    (!p k. MEM (p,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\ FLOOKUP v.vs_allocas id = SOME (p,k)) /\
    fresh_vars_wrt limit v /\ ptr_covers B u root v (32+maxn*type_memory_size tv) /\
    (!x. not_fresh_at st x ==> FLOOKUP B x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (initial,G,tn) [] (OK v,B,u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    (qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` mp_tac >>
     simp[NoAsms,Once abi_decoder_coherent_array_iff]) >>
  `type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
     DecDynArray (type_to_abi_dec_info sf ce ty) (tv_abi_size tv) (type_memory_size tv)
       (is_abi_dynamic ce.ce_struct_fields ty) maxn` by
    (drule abi_decoder_coherent_header >> drule calldata_coherent_embedded_size >>
     simp[abi_decoder_header_def,type_to_abi_dec_info_def]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ st = _` mp_tac >>
  qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _` (once_rewrite_tac o single) >>
  disch_tac >>
  drule_all calldata_nonbulk_parent_shell_conditional >>
  disch_then (qx_choose_then `ip` (qx_choose_then `cop` strip_assume_tac)) >>
  Cases_on `maxn MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD sw initial)`
  >- (disj1_tac >> drule_all none_array_count_reject >>
      disch_then (qspec_then `PG` ACCEPT_TAC)) >>
  qabbrev_tac `cap = 32+maxn*type_memory_size tv` >>
  `base_addr+owner_cap <= initial.vs_alloca_next` by
    (qpat_assum `alloca_inv initial` mp_tac >>
     pure_rewrite_tac[alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> first_x_assum drule >> simp[NoAsms]) >>
  `d < dimword (:256) /\ 32 <= cap /\ d+cap <= initial.vs_alloca_next` by
    (conj_tac >- decide_tac >> conj_tac >- simp[NoAsms,Abbr `cap`] >> decide_tac) >>
  `w2n (abi_decode_load CALLDATALOAD sw initial) <= maxn MOD dimword (:256)` by decide_tac >>
  `?bb. lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb (LENGTH loop_st.cs_current_insts) =
          SOME (mk_inst loop_st.cs_next_id JMP [Label (FST labels)] [])` by
    (qpat_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     `labels = (FST labels, FST (SND labels), SND (SND labels))` by
       (Cases_on `labels` >> Cases_on `r` >> simp[NoAsms]) >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     disch_tac >> drule_all calldataDynInitTheory.calldata_loop_prefix_entry_code >>
     strip_tac >> qexists_tac `bb` >> asm_rewrite_tac[] >>
     qpat_assum `bb.bb_instructions = _`
       (fn th => simp[NoAsms, get_instruction_def, th, rich_listTheory.EL_LENGTH_APPEND_0])) >>
  `header_st.cs_next_id < last.cs_next_id` by decide_tac >>
  `FLOOKUP initial.vs_allocas oid = SOME (base_addr,owner_cap) /\
   oid <> header_st.cs_next_id` by (conj_tac >- asm_rewrite_tac[] >> decide_tac) >>
  drule_all calldataDynOwnedTheory.calldata_index_init_literal_site >> strip_tac >>
  `initial.vs_alloca_next < dimword(:256)` by
    (qpat_assum `alloca_frontier_inv ctx fn site initial` mp_tac >>
     pure_rewrite_tac[alloca_frontier_inv_def] >> strip_tac >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm
    (qx_choose_then `slot` (map_every assume_tac o CONJUNCTS)))
    `?slot. ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
            slot = initial.vs_alloca_next) \/
           (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (slot,32) /\
            slot < dimword(:256) /\ slot+32 <= initial.vs_alloca_next)) /\
          slot+32 < dimword(:256) /\ (d+cap <= slot \/ slot+32 <= d)`
    >- (Cases_on `FLOOKUP initial.vs_allocas header_st.cs_next_id`
     >- (`FLOOKUP initial.vs_allocas ins.inst_id = NONE` by asm_rewrite_tac[] >>
         drule_all actualAllocExecTheory.actual_word_alloca_fresh_run >> strip_tac >>
         qexists_tac `initial.vs_alloca_next` >> asm_rewrite_tac[]) >>
     PairCases_on `x` >>
     qpat_assum `!id p k. _ /\ _ /\ FLOOKUP initial.vs_allocas id = SOME (p,k) ==> _`
       (qspecl_then [`header_st.cs_next_id`,`x0`,`x1`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
     `FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (x0,32)` by asm_rewrite_tac[] >>
     `base_addr+owner_cap <= x0 \/ x0+32 <= base_addr` by
       (qpat_assum `alloca_inv initial` mp_tac >>
        pure_rewrite_tac[alloca_inv_def,allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`oid`,`header_st.cs_next_id`,`base_addr`,`owner_cap`,`x0`,`32`] mp_tac o CONJUNCT1) >>
        asm_rewrite_tac[]) >>
     qexists_tac `x0` >> asm_rewrite_tac[] >> decide_tac) >>
  `lookup_var root initial = SOME (n2w d)` by
    (qpat_assum `eval_operand (Var root) initial = _` mp_tac >> simp[NoAsms,eval_operand_def]) >>
  drule_all none_array_first_header >>
  disch_then (qspec_then `PG` (qx_choose_then `first` (qx_choose_then `A0`
    (qx_choose_then `tn0` (qx_choose_then `q` (map_every assume_tac o CONJUNCTS)))))) >>
  qabbrev_tac `cnt = w2n (abi_decode_load CALLDATALOAD sw initial)` >>
  qabbrev_tac `sb = w2n sw` >>
  `n2w sb : bytes32 = sw /\ cnt < dimword(:256) /\
   abi_decode_load CALLDATALOAD sw initial = n2w cnt /\
   w2n (cd_word initial.vs_call_ctx.cc_calldata sb) = cnt` by
    simp[Abbr `sb`, Abbr `cnt`, w2n_lt, calldata_decode_load_word] >>
  `cnt <= maxn` by
    (`maxn MOD dimword(:256) <= maxn` by simp[MOD_LESS_EQ] >>
     qpat_assum `cnt <= _` mp_tac >> decide_tac) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac) `tv_abi_dynamic tv \/ tv_needs_clamp tv`
  >- (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (fn th => qpat_assum `is_abi_dynamic _ ty \/ _`
         (ACCEPT_TAC o PURE_REWRITE_RULE
           [MATCH_MP calldata_coherent_dynamic th, MATCH_MP calldata_coherent_clamp th]))) >>
  `DISJOINT {x | slot <= x /\ x < slot+32} tn0.t_mem /\ tn0.t_mem SUBSET tn.t_mem` by
    (qpat_assum `tn0.t_mem = _` SUBST1_TAC >>
     POP_ASSUM_LIST (K all_tac) >> SET_TAC[]) >>
  `middle.cs_next_var <= st1.cs_next_var` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ middle = _`
      (mp_tac o MATCH_MP abi_decoder_variable_counter) >> simp[]) >>
  `last.cs_next_var = st1.cs_next_var + 1` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ st1 = _` mp_tac >>
     qpat_assum `FST ops = _` (fn th =>
       simp[NoAsms,th,abi_decode_loop_suffix_shape]) >>
     disch_then (fn th => simp[NoAsms, GSYM th, abi_decode_loop_suffix_state_def])) >>
  `st0.cs_next_var = loop_st.cs_next_var + 4` by
    (qpat_assum `abi_decode_loop_prefix _ _ _ _ loop_st = _` mp_tac >>
     simp[NoAsms,abi_decode_loop_prefix_shape] >>
     disch_then (fn th => simp[NoAsms,GSYM (CONJUNCT2 th),
       abi_decode_loop_prefix_state_def,abi_decode_position_header_delta_def])) >>
  `loop_st.cs_next_var + 3 < middle.cs_next_var` by
    (qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> _` mp_tac >>
     simp[NoAsms,abi_decoder_operand_live_def,abi_decoder_older_vars_def] >>
     disch_then (qspec_then `Var (STRING #"%" (toString (loop_st.cs_next_var+3)))` mp_tac) >>
     simp[NoAsms,ASCIInumbersTheory.toString_inj] >>
     decide_tac) >>
  `st1.cs_next_var < limit.cs_next_var /\ loop_st.cs_next_var <= limit.cs_next_var` by decide_tac >>
  qmatch_asmsub_abbrev_tac `lookup_block (FST labels) fn.fn_blocks = SOME hdr_bb` >>
  qmatch_asmsub_abbrev_tac `lookup_block st1.cs_current_bb fn.fn_blocks = SOME back_bb` >>
  `phi_prefix_length hdr_bb.bb_instructions = 0 /\
    (st1.cs_current_insts = [] ==> phi_prefix_length back_bb.bb_instructions = 0)` by
    simp[NoAsms, Abbr `hdr_bb`, Abbr `back_bb`, abi_decode_header_insts_def,
      abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def] >>
  qabbrev_tac `iv = STRING #"%" (toString loop_st.cs_next_var)` >>
  qabbrev_tac `cv = STRING #"%" (toString (loop_st.cs_next_var+1))` >>
  qabbrev_tac `cmp = STRING #"%" (toString (loop_st.cs_next_var+2))` >>
  qabbrev_tac `done = STRING #"%" (toString (loop_st.cs_next_var+3))` >>
  qabbrev_tac `ix = STRING #"%" (toString st0.cs_next_var)` >>
  qabbrev_tac `nv = STRING #"%" (toString st1.cs_next_var)` >>
  qabbrev_tac `protect = {x | x = q \/ not_fresh_at st x}` >>
  `q IN protect /\ root IN protect /\ (!x. src = Var x ==> x IN protect)` by
    (simp[NoAsms,Abbr `protect`,GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh] >>
     (conj_tac >- asm_rewrite_tac[]) >> gen_tac >> disch_tac >>
     pop_assum (fn th => qpat_assum `abi_decoder_operand_live st.cs_next_var src`
       (mp_tac o REWRITE_RULE[th])) >>
     disch_then (fn th => simp[NoAsms,th])) >>
  `!x. x IN protect ==> not_fresh_at st0 x /\ not_fresh_at middle x /\
       ~MEM x [iv;cv;cmp;done] /\ x <> nv` by
    (gen_tac >> disch_tac >>
     qpat_assum `!op. op = src \/ _ ==> _` (qspec_then `Var x` mp_tac) >>
     (impl_tac >- (qpat_assum `x IN protect` mp_tac >>
       qpat_assum `ip = Var q` (fn th =>
         simp[NoAsms,Abbr `protect`,th,GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh]))) >>
     disch_then (fn th =>
       (map_every assume_tac (CONJUNCTS th) >>
        qpat_assum `!op. abi_decoder_operand_live st0.cs_next_var op ==> _`
          (qspec_then `Var x` drule) >>
        mp_tac th >>
        simp[NoAsms,MEM,GSYM calldataDynOwnedTheory.calldata_operand_live_not_fresh]))) >>
  `ALL_DISTINCT [q;iv;cv;cmp;done]` by
     (qpat_assum `!x. x IN protect ==> not_fresh_at st0 x /\ _` (qspec_then `q` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      simp[NoAsms,ALL_DISTINCT,MEM,Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`,
           ASCIInumbersTheory.toString_inj]) >>
  `!x. MEM x [iv;cv;cmp;done] ==>
       ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var` by
    (simp[NoAsms,Abbr `iv`,Abbr `cv`,Abbr `cmp`,Abbr `done`,
          DISJ_IMP_THM, FORALL_AND_THM, ASCIInumbersTheory.toString_inj] >>
     decide_tac) >>
  `abi_decoder_operand_live st0.cs_next_var src /\ src <> Var iv` by
    (qpat_assum `!op. op = src \/ _ ==> _` (qspec_then `src` mp_tac) >> simp[NoAsms]) >>
  `hdr_bb.bb_instructions = abi_decode_header_insts (loop_st.cs_next_id+1)
         (Var q) src CALLDATALOAD iv cv cmp done (FST (SND labels)) (SND (SND labels)) /\
   back_bb.bb_instructions = st1.cs_current_insts ++ abi_decode_backedge_insts
         st1.cs_next_id ix nv (Var q) (FST labels)` by
    (qpat_assum `ip = Var q` (fn th => simp[NoAsms,Abbr `hdr_bb`,Abbr `back_bb`,th])) >>
  `st1.cs_current_insts = [] ==> !b. lookup_block st1.cs_current_bb fn.fn_blocks = SOME b ==>
       phi_prefix_length b.bb_instructions = 0` by
    (asm_rewrite_tac[] >> simp[NoAsms] >> disch_tac >> first_assum irule >> asm_rewrite_tac[]) >>
  qabbrev_tac `Q = \s A ta.
    ~s.vs_halted /\ s.vs_call_ctx = initial.vs_call_ctx /\
    s.vs_data_section = initial.vs_data_section /\ s.vs_labels = initial.vs_labels /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ allocas_from lo s /\
    initial.vs_alloca_next <= s.vs_alloca_next /\ fresh_vars_wrt limit s /\
    ptr_covers A ta root s cap /\
    (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    (!id p k. FLOOKUP initial.vs_allocas id = SOME (p,k) ==> FLOOKUP s.vs_allocas id = SOME (p,k)) /\
    (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==> FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!x. not_fresh_at st x ==> lookup_var x s = lookup_var x initial /\
        FLOOKUP A x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
    ta.t_mem SUBSET tn.t_mem /\ ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (?sc. abi_decode_footprint_frame ((d,cap)::(slot,32)::sc) initial s /\
      !p k. MEM (p,k) sc ==> ?id. st.cs_next_id <= id /\ id < last.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (p,k))` >>
  qabbrev_tac `H = \i s A ta. Q s A ta /\ i <= cnt /\
    s.vs_current_bb = FST labels /\ s.vs_inst_idx = 0 /\
    lookup_var q s = SOME (n2w slot) /\ ptr_covers A ta q s 32 /\
    mload slot s = n2w i /\ DISJOINT {x | slot <= x /\ x < slot+32} ta.t_mem /\
    slot+32 <= s.vs_alloca_next /\ FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (slot,32)` >>
  qabbrev_tac `R = \s A ta. Q s A ta /\ s.vs_current_bb = SND (SND labels) /\
    s.vs_inst_idx = 0 /\ FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (slot,32)` >>
  `!s A ta t B u. (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s,A,ta) [] (OK t,B,u)) ==> t.vs_labels = s.vs_labels` by
    (rpt gen_tac >> disch_then (qspecl_then [`ARB`,`ARB`]
      (ACCEPT_TAC o MATCH_MP gas_origin_ptr_path_preserves_labels))) >>
  `not_fresh_at st root` by
     (qpat_assum `abi_decoder_operand_live st.cs_next_var (Var root)` mp_tac >>
      simp[NoAsms,calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  `!x. src = Var x ==> not_fresh_at st x` by
     (gen_tac >> disch_then (fn th => qpat_assum `abi_decoder_operand_live st.cs_next_var src`
        (mp_tac o REWRITE_RULE[th])) >> simp[NoAsms,calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  `!s A ta. Q s A ta ==>
    lookup_var root s = SOME (n2w d) /\ eval_operand src s = SOME sw /\
    op_taint ta src = {} /\ op_prov A src = NONE /\
    abi_decode_load CALLDATALOAD sw s = n2w cnt` by
    (simp[NoAsms,Abbr `Q`] >> rpt gen_tac >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `lookup_var root s = lookup_var root initial` by
       (qpat_assum `!x. not_fresh_at st x ==> lookup_var x s = _ /\ _`
          (qspec_then `root` drule) >> disch_then (ACCEPT_TAC o CONJUNCT1)) >>
     `abi_decode_load CALLDATALOAD sw s = n2w cnt` by
       (qpat_assum `abi_decode_load CALLDATALOAD sw initial = _` mp_tac >>
        qpat_assum `s.vs_call_ctx = initial.vs_call_ctx` (fn th =>
          simp[NoAsms,calldata_decode_load_word,th])) >>
     qpat_assum `lookup_var root initial = _` (fn th =>
       qpat_assum `lookup_var root s = _` (fn th' =>
         qpat_assum `abi_decode_load CALLDATALOAD sw s = _` (fn th'' =>
           simp[NoAsms,th,th',th'']))) >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x s = _ /\ _` mp_tac >>
     qpat_assum `!x. src = Var x ==> not_fresh_at st x` mp_tac >>
     qpat_assum `eval_operand src initial = _` mp_tac >>
     qpat_assum `op_taint tn src = _` mp_tac >>
     qpat_assum `op_prov G src = _` mp_tac >>
     qpat_assum `s.vs_labels = initial.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `src` >>
     simp[eval_operand_def,op_taint_def,op_prov_def]) >>
  mp_tac (Q.INST [`H` |-> `H`, `R` |-> `R`, `cnt` |-> `cnt`,
    `cd` |-> `initial.vs_call_ctx.cc_calldata`, `arr_head` |-> `cd_at F sb 32`]
    none_nonbulk_suffix_paths) >>
  impl_tac
  >- (reverse conj_tac >- suspend "exit" >> suspend "iteration") >>
  disch_then (qspecl_then [`cnt`,`0`,`first`,`A0`,`tn0`] mp_tac) >>
  rewrite_tac[ADD_CLAUSES] >> impl_tac
  >- suspend "initial" >> suspend "compose"
QED

Resume none_nonbulk_fold_paths[exit]:
  map_every qx_gen_tac [`s`,`A`,`ta`] >>
  simp[NoAsms,Abbr `H`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!s A ta. Q s A ta ==> _` drule >> strip_tac >>
  (qpat_assum `Q s A ta` mp_tac >> simp[NoAsms, Abbr `Q`]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hdr_bb` by asm_rewrite_tac[] >>
  mp_tac (Q.INST [`bb` |-> `hdr_bb`, `id` |-> `loop_st.cs_next_id+1`,
    `G` |-> `A`, `tn` |-> `ta`, `body_lbl` |-> `FST (SND (labels:string#string#string))`,
    `exit_lbl` |-> `SND (SND (labels:string#string#string))`] none_array_final_header) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `v` (qx_choose_then `B` (qx_choose_then `u`
    (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl_tac [`v`,`B`,`u`] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms,Abbr `R`] >>
  `!x. not_fresh_at st x ==> ~MEM x [iv;cv;cmp;done]` by
    (gen_tac >> disch_tac >>
     `x IN protect` by simp[Abbr `protect`] >>
     qpat_assum `!x. x IN protect ==> not_fresh_at st0 x /\ _` (qspec_then `x` drule) >>
     disch_then (ACCEPT_TAC o cj 3)) >>
  `!x. not_fresh_at st x ==> lookup_var x v = lookup_var x s /\
      FLOOKUP B x = FLOOKUP A x /\ op_taint u (Var x) = op_taint ta (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. ~MEM x _ ==> lookup_var x v = _ /\ _` (qspec_then `x` mp_tac) >> simp[]) >>
  `ptr_covers B u root v cap` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x v = _ /\ _`
       (qspec_then `root` drule) >> strip_tac >>
     drule_all decoderGhostFramePtrTheory.ptr_covers_frame >> simp[]) >>
  `v.vs_labels = s.vs_labels` by
    (qpat_assum `!s A ta t B u. _ ==> t.vs_labels = s.vs_labels`
       (qspecl_then [`s`,`A`,`ta`,`v`,`B`,`u`] drule) >> simp[]) >>
  `fresh_vars_wrt limit v` by
    (qpat_assum `!limit. _ ==> fresh_vars_wrt limit v` (qspec_then `limit` irule) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_inv v /\ alloca_frontier_inv ctx fn site v` by
    (conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC) >>
     first_assum irule >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at st x ==> lookup_var x v = _ /\ _`
        (qspec_then `x` drule) >>
      qpat_assum `!x. not_fresh_at st x ==> lookup_var x s = _ /\ _`
        (qspec_then `x` drule) >>
      disch_then (fn th => disch_then (fn th' => simp[NoAsms,th,th']))) >>
  qpat_assum `?sc. abi_decode_footprint_frame _ initial s /\ _`
    (qx_choose_then `sc` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexists_tac `sc` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `abi_decode_footprint_frame _ initial s` mp_tac >>
  qpat_assum `v.vs_memory = s.vs_memory` (fn m =>
    qpat_assum `v.vs_call_ctx = s.vs_call_ctx` (fn c =>
      qpat_assum `v.vs_data_section = s.vs_data_section` (fn d =>
        simp[NoAsms,abi_decode_footprint_frame_def,m,c,d])))
QED

Resume none_nonbulk_fold_paths[iteration]:
  map_every qx_gen_tac [`i`,`s`,`A`,`ta`] >>
  simp[NoAsms,Abbr `H`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!s A ta. Q s A ta ==> _` drule >> strip_tac >>
  qpat_assum `Abbrev (Q = _)` (fn def =>
    qpat_assum `Q s A ta`
      (map_every assume_tac o CONJUNCTS o BETA_RULE o
        REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] def])) >>
  `32+i*type_memory_size tv+type_memory_size tv <= cap` by
    (`SUC i <= maxn` by decide_tac >>
     `SUC i * type_memory_size tv <= maxn * type_memory_size tv` by
       (irule numberTheory.LE_MONO_MULT2 >> simp[]) >>
     pop_assum mp_tac >>
     qpat_assum `Abbrev (cap = _)` (fn th =>
       rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th, MULT_CLAUSES, ADD_ASSOC]) >>
     decide_tac) >>
  `FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap)` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  (SUBGOAL_THEN ``oid < middle.cs_next_id \/ st1.cs_next_id <= oid`` assume_tac
   >- decide_tac) >>
  `lo <= s.vs_alloca_next` by decide_tac >>
  `!id p k. middle.cs_next_id <= id /\ id < st1.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\ ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!id p k. st.cs_next_id <= id /\ _ /\ FLOOKUP s.vs_allocas id = SOME (p,k) ==> _`
       (qspecl_then [`id`,`p`,`k`] mp_tac) >>
     `st.cs_next_id <= id /\ id < last.cs_next_id` by decide_tac >>
     (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC) >>
  mp_tac (none_array_iteration_paths |>
    CONV_RULE (REWR_CONV LET_THM THENC BETA_CONV THENC REWR_CONV LET_THM THENC BETA_CONV) |>
    Q.INST [`st` |-> `st0`, `ready` |-> `middle`, `last` |-> `st1`, `j` |-> `i`,
      `G` |-> `A`, `tn` |-> `ta`, `hid` |-> `loop_st.cs_next_id+1`,
      `hdr` |-> `FST (labels:string#string#string)`,
      `body_lbl` |-> `FST (SND (labels:string#string#string))`,
      `exit_lbl` |-> `SND (SND (labels:string#string#string))`,
      `counter_id` |-> `header_st.cs_next_id`]) >>
  (impl_tac >-
    (asm_rewrite_tac[] >> conj_tac
     >- (qpat_assum `ip = Var q` (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
     conj_tac >- simp[NoAsms, Abbr `nv`] >>
     conj_tac >- decide_tac >>
     map_every qx_gen_tac [`a`,`C`,`ct`,`child`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qmatch_asmsub_abbrev_tac `eval_operand (FST (SND ops)) a = SOME (n2w pos : bytes32)` >>
     qmatch_asmsub_abbrev_tac `lookup_var child a = SOME (n2w e : bytes32)` >>
     qpat_assum `!a b child sop s p e A ta. _`
       (qspecl_then [`middle`,`st1`,`child`,`FST (SND ops)`,`a`,
         `n2w pos : bytes32`,`e`,`C`,`ct`] mp_tac) >>
     (impl_tac >-
       (asm_rewrite_tac[eval_operand_def] >> conj_tac
        >- (qpat_assum `SND (SND ops) = Var child` (fn th => rewrite_tac[GSYM th]) >>
            first_assum ACCEPT_TAC) >>
        qpat_assum `Abbrev (e = _)` (fn th => rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
        decide_tac)) >>
     (disch_then (DISJ_CASES_THEN2 assume_tac
       (qx_choose_then `r` (qx_choose_then `sc` (qx_choose_then `B` (qx_choose_then `u`
         (map_every assume_tac o CONJUNCTS))))))
      >- (disj1_tac >> first_assum ACCEPT_TAC)) >>
     disj2_tac >> qexistsl_tac [`r`,`B`,`u`,`sc`] >> asm_rewrite_tac[])) >>
  (disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `t` (qx_choose_then `B` (qx_choose_then `u` (qx_choose_then `new`
      (map_every assume_tac o CONJUNCTS))))))
   >- (disj1_tac >> first_assum ACCEPT_TAC)) >>
  disj2_tac >> qexistsl_tac [`t`,`B`,`u`] >>
  reverse conj_tac
  >- (reverse conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `s.vs_call_ctx = initial.vs_call_ctx` (fn eq =>
        qpat_assum `IS_SOME (cd_decode F s.vs_call_ctx.cc_calldata tv _)`
          (ACCEPT_TAC o REWRITE_RULE[eq]))) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_assum `!s A ta t B u. _ ==> t.vs_labels = s.vs_labels`
      (qspecl_then [`s`,`A`,`ta`,`t`,`B`,`u`] drule) >> simp[]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x initial /\
     FLOOKUP B x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     `x IN protect` by simp[Abbr `protect`] >>
     qpat_assum `!x. x IN protect ==> lookup_var x t = _ /\ _` (qspec_then `x` drule) >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x s = _ /\ _` (qspec_then `x` drule) >>
     disch_then (fn th => disch_then (fn th' => rewrite_tac[th,th']))) >>
  `lookup_var q t = SOME (n2w slot)` by
    (qpat_assum `!x. x IN protect ==> lookup_var x t = _ /\ _` (qspec_then `q` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn th => rewrite_tac[CONJUNCT1 th] >> first_assum ACCEPT_TAC)) >>
  `slot+32 <= t.vs_alloca_next` by decide_tac >>
  `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (slot,32)` by
    (qpat_assum `!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> simp[NoAsms,Abbr `Q`] >> asm_rewrite_tac[] >>
  conj_tac >- decide_tac >>
  conj_tac
  >- (map_every qx_gen_tac [`id`,`p`,`k`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      Cases_on `middle.cs_next_id <= id /\ id < st1.cs_next_id`
      >- (qpat_assum `!id p k. middle.cs_next_id <= id /\ _ /\ FLOOKUP t.vs_allocas id = _ ==> _`
            (qspecl_then [`id`,`p`,`k`] mp_tac) >>
          (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >> disch_then ACCEPT_TAC) >>
      `FLOOKUP s.vs_allocas id = SOME (p,k)` by
        (qpat_assum `!id. _ ==> FLOOKUP t.vs_allocas id = _` (qspec_then `id` mp_tac) >>
         (impl_tac >- decide_tac) >>
         disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!id p k. st.cs_next_id <= id /\ _ /\ FLOOKUP s.vs_allocas id = _ ==> _`
        (qspecl_then [`id`,`p`,`k`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      asm_rewrite_tac[] >> decide_tac) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!id p k. FLOOKUP s.vs_allocas id = _ ==> _` irule >>
      qpat_assum `!id p k. FLOOKUP initial.vs_allocas id = _ ==> FLOOKUP s.vs_allocas id = _` irule >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qx_gen_tac `id` >> disch_tac >>
      qpat_assum `!id. _ ==> FLOOKUP t.vs_allocas id = _` (qspec_then `id` mp_tac) >>
      (impl_tac >- decide_tac) >> disch_then (fn th => rewrite_tac[th]) >>
      qpat_assum `!id. _ ==> FLOOKUP s.vs_allocas id = _` (qspec_then `id` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  conj_tac >- (irule SUBSET_TRANS >> qexists_tac `ta.t_mem` >> asm_rewrite_tac[]) >>
  qpat_assum `?sc. abi_decode_footprint_frame _ initial s /\ _`
    (qx_choose_then `old` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  qexists_tac `old ++ new` >>
  conj_tac
  >- (irule abi_decode_footprint_frame_trans >> qexists_tac `s` >>
      conj_tac
      >- (irule abi_decode_footprint_frame_weaken >>
          qexists_tac `(d,cap)::(slot,32)::old` >>
          reverse conj_tac >- first_assum ACCEPT_TAC >>
          map_every qx_gen_tac [`a`,`n`] >> disch_tac >> qexistsl_tac [`a`,`n`] >>
          pop_assum mp_tac >> POP_ASSUM_LIST (K all_tac) >>
          simp[MEM,MEM_APPEND] >> metis_tac[]) >>
      irule abi_decode_footprint_frame_weaken >>
      qexists_tac `(d+32+i*type_memory_size tv,type_memory_size tv)::(slot,32)::new` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rewrite_tac[MEM,MEM_APPEND] >> map_every qx_gen_tac [`a`,`n`] >>
      disch_then (DISJ_CASES_THEN2 assume_tac assume_tac)
      >- (qexistsl_tac [`d`,`cap`] >> pop_assum mp_tac >>
          simp[NoAsms] >> decide_tac) >>
      qexistsl_tac [`a`,`n`] >> pop_assum mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  rewrite_tac[MEM_APPEND] >> map_every qx_gen_tac [`p`,`k`] >>
  disch_then (DISJ_CASES_THEN assume_tac)
  >- (qpat_assum `!p k. MEM (p,k) old ==> _` (qspecl_then [`p`,`k`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (qx_choose_then `id` strip_assume_tac) >>
      qexists_tac `id` >> asm_rewrite_tac[] >>
      qpat_assum `!id p k. FLOOKUP s.vs_allocas id = _ ==> _` irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `!p k. MEM (p,k) new ==> _` (qspecl_then [`p`,`k`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (qx_choose_then `id` strip_assume_tac) >>
  qexists_tac `id` >> asm_rewrite_tac[] >> decide_tac
QED

Resume none_nonbulk_fold_paths[initial]:
  `first.vs_labels = initial.vs_labels` by
    (qpat_assum `!s A ta t B u. _ ==> t.vs_labels = s.vs_labels`
       (qspecl_then [`initial`,`G`,`tn`,`first`,`A0`,`tn0`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  `fresh_vars_wrt limit first` by
    ((qpat_assum `!limit. _ ==> fresh_vars_wrt limit first`
       (qspec_then `limit` mp_tac) >> asm_rewrite_tac[] >> (simp[]))) >>
  simp[NoAsms,Abbr `H`,Abbr `Q`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (map_every qx_gen_tac [`id`,`p`,`k`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      Cases_on `id = header_st.cs_next_id`
      >- (`p = slot /\ k = 32` by
            (qpat_assum `FLOOKUP first.vs_allocas id = SOME (p,k)` (fn th =>
               qpat_assum `id = header_st.cs_next_id` (fn eq =>
                 mp_tac (REWRITE_RULE [eq] th))) >> asm_rewrite_tac[] >> simp[NoAsms]) >>
          `p < dimword (:256) /\ p+32 <= first.vs_alloca_next` by decide_tac >>
          asm_rewrite_tac[] >> qexists_tac `ins` >> asm_rewrite_tac[]) >>
      `FLOOKUP initial.vs_allocas id = SOME (p,k)` by
        (qpat_assum `!id. id <> header_st.cs_next_id ==> _` (qspec_then `id` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
      qpat_assum `!id p k. st.cs_next_id <= id /\ _ /\ FLOOKUP initial.vs_allocas id = _ ==> _`
        (qspecl_then [`id`,`p`,`k`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >>
      disch_then (map_every assume_tac o CONJUNCTS) >> asm_rewrite_tac[] >> decide_tac) >>
  conj_tac
  >- (qx_gen_tac `id` >> disch_tac >>
      qpat_assum `!id. id <> header_st.cs_next_id ==> _` (qspec_then `id` mp_tac) >>
      (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC) >>
  qexists_tac `[]` >> simp[NoAsms,abi_decode_footprint_frame_def] >> asm_rewrite_tac[] >>
  map_every qx_gen_tac [`a`,`n`] >> disch_tac >>
  qpat_assum `abi_footprint_disjoint a n _` (mp_tac o REWRITE_RULE [abi_footprint_disjoint_def]) >>
  disch_then (fn th =>
    mp_tac (Q.SPECL [`d`,`cap`] th) >> mp_tac (Q.SPECL [`slot`,`32`] th)) >>
  simp[NoAsms] >> rpt disch_tac >>
  qpat_assum `!a n. (a+n <= d \/ _) /\ _ ==> _` (qspecl_then [`a`,`n`] mp_tac) >>
  (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC
QED

Resume none_nonbulk_fold_paths[compose]:
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `z` (qx_choose_then `B` (qx_choose_then `u`
      (CONJUNCTS_THEN2 assume_tac assume_tac))))
    (qx_choose_then `v` (qx_choose_then `B` (qx_choose_then `u`
      (map_every assume_tac o CONJUNCTS)))))
  >- (disj1_tac >> qexistsl_tac [`z`,`B`,`u`] >> conj_tac
      >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> qpat_assum `!D explicit. gas_origin_ptr_path _ (initial,G,tn) [] _`
        (qspecl_then [`D`,`explicit`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
      disch_then (qspecl_then [`first`,`A0`,`tn0`,`[]`,`Abort Revert_abort z`,`B`,`u`] mp_tac) >>
      asm_rewrite_tac[APPEND_NIL]) >>
  `IS_SOME (cd_decode F initial.vs_call_ctx.cc_calldata (ArrayTV tv (Dynamic maxn)) sb)` by
    (qpat_assum `IS_SOME (cd_decode_elems F _ tv _ 0 cnt)` mp_tac >>
     qpat_assum `w2n (cd_word _ sb) = cnt` (fn eq =>
       qpat_assum `tv_abi_dynamic tv \/ tv_needs_clamp tv` mp_tac >>
       qpat_assum `cnt <= maxn` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[cd_decode_def,eq] >> rpt strip_tac >>
       TOP_CASE_TAC >> gvs[])) >>
  qpat_x_assum `R v B u` (fn packet =>
    qpat_assum `Abbrev (R = _)` (fn r_def =>
      qpat_assum `Abbrev (Q = _)` (fn q_def =>
        map_every assume_tac (CONJUNCTS (BETA_RULE (REWRITE_RULE
          [REWRITE_RULE [markerTheory.Abbrev_def] r_def,
           REWRITE_RULE [markerTheory.Abbrev_def] q_def] packet)))))) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op v = eval_operand op initial` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x v = _ /\ _` mp_tac >>
     qpat_assum `v.vs_labels = initial.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> Cases >>
     simp[eval_operand_def,calldataDynOwnedTheory.calldata_operand_live_not_fresh]) >>
  qpat_assum `?sc. abi_decode_footprint_frame _ initial v /\ _`
    (qx_choose_then `sc` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  disj2_tac >> qexistsl_tac [`v`,`(slot,32)::sc`,`B`,`u`] >>
  qpat_assum `Abbrev (cap = _)` (fn th =>
    rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  `LENGTH last.cs_current_insts = 0` by asm_rewrite_tac[LENGTH] >>
  `!x. not_fresh_at st x ==> FLOOKUP B x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x v = _ /\ _`
       (qspec_then `x` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  asm_rewrite_tac[] >> conj_tac
  >- (simp[NoAsms,MEM] >> map_every qx_gen_tac [`p`,`k`] >>
      disch_then (DISJ_CASES_THEN2 assume_tac assume_tac)
      >- (qexists_tac `header_st.cs_next_id` >>
          pop_assum (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) >>
          asm_rewrite_tac[]) >>
      qpat_assum `!p k. MEM (p,k) sc ==> _` (qspecl_then [`p`,`k`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  rpt gen_tac >> qpat_assum `!D explicit. gas_origin_ptr_path _ (initial,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_tac o MATCH_MP gas_origin_ptr_path_append)) >>
  disch_then (qspecl_then [`first`,`A0`,`tn0`,`[]`,`OK v`,`B`,`u`] mp_tac) >>
  asm_rewrite_tac[APPEND_NIL]
QED

Finalise none_nonbulk_fold_paths
