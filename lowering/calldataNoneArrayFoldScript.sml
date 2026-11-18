Theory calldataNoneArrayFold
Ancestors
  vyperCalldata fragGasOriginPtr arithmetic list
  calldataInitSequence calldataInitLocalFrontier calldataRecursiveProducers
  decoderArrayInitPtr decoderNavigationPtr decoderLoopHeaderCorePtr
  entrySinkExtraction abiDecoderArrayInit abiDecoderArrayLoopInit
  abiDecoderIndexInit abiDecoderContract abiDecoderReentry abiDecoderExecution
  abiDecoderDynarrayPrefix allocaFrontierBound lowerDloadPtrTaint
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
  w2n (abi_decode_load CALLDATALOAD sw s) <= maxn /\ maxn < dimword(:256) /\
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
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`ARB`] strip_assume_tac) >>
  suspend "finish"
QED

Resume none_array_first_header[finish]:
  `p' = p` by
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
