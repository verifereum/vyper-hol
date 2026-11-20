(* The finite decoder loop is executed only as far as its first rejection. *)
Theory abiDecodeRejectFiniteArray
Ancestors abiDecoderIndexInit[qualified,ignore_grammar]
  loweringHalt[qualified,ignore_grammar] abiDecoderArrayLoopInit[qualified,ignore_grammar]
  abiDecoderRecursiveArray[qualified,ignore_grammar] abiDecoderDynarrayPrefix[qualified,ignore_grammar]
  abiWidthInhabited abiMalformedBoundedContract abiDecoderOffset abiDecoderCoherence
  abiValidAllocatedArraySource exprSimAbiDecodePrimitiveOwned vyperTypeSystem
  exprLowering
  abiDecodeRejectFiniteHeader abiDecodeRejectIndexedReads abiDecodeRejectIndexedPass
  abiDecodeRejectIndexedGuard abiDecodeValidFiniteInit abiMalformedAggregateFirstBadChild
  abiValidAllocatedArrayLoop decoderLoopBackedgeCorePtr decoderGhostFramePtr
  abiDecodePtrMemberFrame abiMalformedTraversal abiMalformedMemberSetup allocaHistory
  allocaSiteResource stateRelProj abiValidAllocatedContract fragGasOriginPtr
  abiDecoderReentry abiDecoderContract abiDecoderLoopEmit abiDecoderLoopCode
  abiDecoderRecursiveLoopLayout
  abiDecoderArraySetupCode abiDecoderIndexedAddress abiDecoderArrayBound abiDecoderGuard
  abiEncoder compileEnv emitHelper vyperABI contractABI
  abiMalformedRecursiveInterface abiMalformedBulkConstructor bodyFullPathHistory
  calldataDynOwned exprLoweringProps loweringStateRelDefs ptrDiscipline
  venomExecSemantics venomMemDefs venomState words finite_map pred_set list arithmetic
  exprSimConvertFromBytes exprSimAbiDecodeArrayRuntimeSetup freshWrites

val worlds = ``\s t. t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables``;
val path = ``\s G tn out H z. !D explicit.
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (out,H,z)``;
val abort = ``\s G tn. ?u H z. (^worlds) s u /\ (^path) s G tn (Abort Revert_abort u) H z``;
val parent = ``\s. abi_malformed_entry H0 ctx func cenv cx es st sites dstid live
  (Var source) hi pos (Var output) B L xs p d outsz s``;
val counter = ``\s. FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32) /\
  lookup_var ip s = SOME (n2w slot)``;
val root_ghosts = ``\s G tn.
  abi_decode_ptr_window G tn s source (n2w B) L /\ ptr_covers G tn output s outsz /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\ op_prov G hi = NONE /\ op_taint tn hi = {} /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next``;
val repeat_entry = ``\j s G tn. (^parent) s /\ (^counter) s /\ (^root_ghosts) s G tn /\
  fresh_vars_wrt ceiling s /\ ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  ptr_covers G tn ip s 32 /\ mload slot s = n2w j /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem)``;

(* At the successful child's actual return, the backedge restores exactly the
   same counter site. The physical resource and ghost proofs share the jump state. *)
Theorem finite_reject_repeat[local]:
  (^parent) u /\ (^counter) u /\ (^root_ghosts) u G tn /\
  fresh_vars_wrt ceiling u /\ ~u.vs_halted /\
  fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [ip] /\ not_local_ptr cenv es.scopes ip /\ inst.inst_id IN sites /\
  st.cs_next_var <= next /\ next < ceiling.cs_next_var /\
  ip <> STRING #"%" (toString next) /\
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
     (STRING #"%" (toString next)) (Var ip) hdr /\ u.vs_inst_idx = LENGTH prefix /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ptr_covers G tn ip u 32 /\ eval_operand (Var iv) u = SOME (n2w j) /\
  op_prov G (Var iv) = NONE /\ op_taint tn (Var iv) = {} /\ j < n /\ n < dimword (:256) ==>
  ?t H z. (^repeat_entry) (SUC j) t H z /\ (^worlds) u t /\ (^path) u G tn (OK t) H z
Proof
  simp_tac bool_ss [] >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE[abi_malformed_entry_def]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `slot+32 <= u.vs_alloca_next` by metis_tac[alloca_site_registered_below] >>
  `slot+32 < dimword (:256)` by fs[alloca_room_def] >>
  qabbrev_tac `P = {a | w2n (n2w B:bytes32) <= a /\ a < w2n (n2w B:bytes32)+L}` >>
  `DISJOINT P tn.t_mem` by fs[Abbr `P`, abi_decode_ptr_window_def, DISJOINT_ALT] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qhdtm_assum `abi_malformed_entry`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) o
        cj 1 o REWRITE_RULE [abi_malformed_entry_def])) >>
  drule_all decoder_index_backedge_ptr_core_uniform_origin_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`Hg`,`zg`,`t`] strip_assume_tac)) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid u t /\
   fresh_vars_wrt ceiling t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     match_mp_tac (GEN_ALL abi_malformed_backedge_resource) >>
     simp[] >> qexistsl [`st`,`ip`,`inst`,`H0`] >> simp[]) >>
  `(^parent) t` by
    (simp_tac bool_ss [] >> irule abi_malformed_aggregate_reentry >>
     simp_tac (srw_ss()) [] >> conj_tac
     >- simp[] >> qexistsl [`u`,`sites`,`st`] >> simp[]) >>
  `t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\ t.vs_halted = u.vs_halted /\
   t.vs_alloca_next = u.vs_alloca_next /\ (^worlds) u t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     simp[jump_to_def,mstore_def,update_var_def,write_memory_with_expansion_def]) >>
  `alloca_history func t /\ allocas_from lo t` by
    (conj_tac >- metis_tac[alloca_history_jump] >>
     qpat_assum `t.vs_allocas = _` (fn th => rewrite_tac [allocas_from_def,th]) >>
     fs[allocas_from_def]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
       lookup_var x t = lookup_var x u /\ FLOOKUP Hg x = FLOOKUP G x /\
       op_taint zg (Var x) = op_taint tn (Var x)` by
    (fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
        abiDecoderReentryTheory.abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `abi_decode_ptr_window Hg zg t source (n2w B) L /\ ptr_covers Hg zg output t outsz` by
    (fs[abi_decode_ptr_window_def, EVERY_DEF, Abbr `P`, DISJOINT_ALT] >>
     metis_tac[ptr_covers_frame]) >>
  qexistsl [`t`,`Hg`,`zg`] >>
  fs[EVERY_DEF, DISJOINT_ALT] >>
  Cases_on `pos` >> Cases_on `hi` >>
  fs[op_prov_def,op_taint_def,abiDecoderReentryTheory.abi_decoder_operand_live_def] >> metis_tac[]
QED

(* The header jumps to the body before its first (separate) index load. *)
Theorem finite_reject_header[local]:
  (^repeat_entry) j h Gh th /\
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
    (Var ip) cnt ls = ((),en) /\ fn_has_code ls en func /\
  hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
  st.cs_next_var <= ls.cs_next_var /\ not_fresh_at ls ip /\
  ls.cs_next_var + 5 <= ceiling.cs_next_var /\
  n = abi_head_word (DROP p xs) /\ j < n /\ p+32 <= L ==>
  ?b Gb tb. (^parent) b /\ (^counter) b /\ (^root_ghosts) b Gb tb /\
    fresh_vars_wrt ceiling b /\ ~b.vs_halted /\
    b.vs_current_bb = fresh_label_output "dec_dyn_body" (ls.cs_next_label+1) /\
    b.vs_inst_idx = 0 /\ ptr_covers Gb tb ip b 32 /\ mload slot b = n2w j /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN tb.t_mem) /\
    (^worlds) h b /\ (^path) h Gh th (OK b) Gb tb
Proof
  simp_tac bool_ss [] >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE[abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (strip_assume_tac o PURE_REWRITE_RULE[abi_malformed_allocated_window_def]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `B+L <= h.vs_alloca_next /\ slot+32 <= h.vs_alloca_next` by
    (conj_tac >- (drule_all alloca_site_registered_below >> decide_tac) >>
     metis_tac[alloca_site_registered_below]) >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `w2n (n2w slot:bytes32) = slot` by
    (fs[alloca_room_def] >> simp[w2n_n2w,LESS_MOD]) >>
  `not_fresh_at ls source /\ not_fresh_at ls output /\
   (!x. pos = Var x \/ hi = Var x ==> not_fresh_at ls x)` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
        abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `h.vs_current_bb = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
   w2n (n2w slot:bytes32) + 32 <= h.vs_alloca_next /\
   mload (w2n (n2w slot:bytes32)) h = n2w j /\
   (!a. w2n (n2w slot:bytes32) <= a /\ a < w2n (n2w slot:bytes32)+32 ==>
         a NOTIN th.t_mem)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp h` by
    (qhdtm_assum `abi_malformed_entry`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) o
        cj 1 o REWRITE_RULE [abi_malformed_entry_def])) >>
  drule_all malformed_finite_header_body_joint >>
  disch_then (qspec_then `PG` (qx_choosel_then [`b`,`Gb`,`tb`] strip_assume_tac)) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid h b` by
    (qpat_assum `b = jump_to _ _` SUBST1_TAC >>
     irule abi_malformed_resource_weaken >>
     qexistsl [`ls.cs_next_var`,`sites`] >>
     simp_tac bool_ss [SUBSET_REFL] >>
     conj_tac >- simp[] >>
     irule (cj 1 abi_malformed_header_resource) >>
     conj_tac >-
       (qexists `ceiling` >> simp[abiDecoderExecutionTheory.abi_decode_position_header_delta_def]) >>
     conj_tac >- (qexists `st` >> simp[]) >>
     qexists `H0` >> simp[]) >>
  `(^parent) b` by
    (simp_tac bool_ss [] >> irule abi_malformed_aggregate_reentry >>
     simp_tac (srw_ss()) [] >> conj_tac
     >- simp[] >> qexistsl [`h`,`sites`,`st`] >> simp[]) >>
  `alloca_history func b` by metis_tac[alloca_history_jump] >>
  qpat_x_assum `mload (w2n _) b = _` (fn th =>
    qpat_assum `w2n _ = slot` (fn eq => assume_tac (PURE_REWRITE_RULE [eq] th))) >>
  qexistsl [`b`,`Gb`,`tb`] >>
  qpat_x_assum `b = jump_to _ _` kall_tac >> simp[] >>
  Cases_on `pos` >> Cases_on `hi` >> fs[op_prov_def,op_taint_def] >> metis_tac[]
QED

(* The body cursor is the one created by this loop prefix; its first
   instruction is not the index load already performed by the header. *)
Theorem finite_reject_body_cursor[local]:
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
    (Var ip) cnt ls = ((),en) /\ fn_has_code ls en func ==>
  ?sa sb se iv child dstop bb hdr_bb.
    abi_decode_array_element_setup (Var ip) pos (Var output) MLOAD (Var source)
      hi di stride memsz sa = ((Var iv,child,dstop),sb) /\
    compile_abi_decode_to_buf dstop child MLOAD (Var source) hi di sb = ((),se) /\
    fn_has_code sa sb func /\ fn_has_code sb se func /\
    sa.cs_current_bb = fresh_label_output "dec_dyn_body" (ls.cs_next_label+1) /\
    sa.cs_current_insts = [] /\ sa.cs_next_var = ls.cs_next_var+5 /\
    sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= se.cs_next_var /\
    ls.cs_next_id <= sb.cs_next_id /\ se.cs_next_id <= en.cs_next_id /\
    en.cs_next_var = SUC se.cs_next_var /\
    lookup_block se.cs_current_bb func.fn_blocks = SOME bb /\
    bb.bb_instructions = se.cs_current_insts ++ abi_decode_backedge_insts
      se.cs_next_id iv (STRING #"%" (toString se.cs_next_var)) (Var ip)
      (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) /\
    lookup_block (fresh_label_output "dec_dyn_hdr" ls.cs_next_label) func.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule_all abi_decoder_loop_phase_lookups >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  PairCases_on `ops` >> fs[] >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `ls.cs_next_id <= middle.cs_next_id` by
    (drule abi_decoder_loop_prefix_facts >> strip_tac >> decide_tac) >>
  qexistsl [`st0`,`middle`,`st1`,`STRING #"%" (toString st0.cs_next_var)`,`ops1`,`ops2`] >>
  gvs[abi_decode_loop_prefix_shape, abi_decode_loop_prefix_state_def,
      abiDecoderExecutionTheory.abi_decode_position_header_delta_def] >>
  simp[abiDecoderExecutionTheory.abi_decode_position_header_insts_def,
       phi_prefix_length_def,venomInstTheory.mk_inst_def]
QED

val read_layout = ``\cut t H z data head.
  if dec_info_needs_offset di then
    ?off cmp nav.
      eval_operand off t = SOME (n2w (abi_head_word (DROP (p+32+j*stride) xs))) /\
      op_taint z off = {} /\ op_prov H off = NONE /\
      abi_decoder_operand_live cut.cs_next_var off /\
      emit_op ADD [data;off] cut = (child,cmp) /\
      abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) /\
      fn_has_code cut nav func /\ fn_has_code nav sb func /\
      abi_decode_indexed_address (Var output) idx memsz nav = (dstop,sb)
  else child = head /\ abi_decode_indexed_address (Var output) idx memsz cut = (dstop,sb)``;

Theorem finite_reject_indexed_read_boundary[local]:
  (^parent) b /\ (^counter) b /\ (^root_ghosts) b Gb tb /\
  fresh_vars_wrt ceiling b /\ ~b.vs_halted /\
  ptr_covers Gb tb ip b 32 /\ mload slot b = n2w j /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tb.t_mem) /\
  abi_decode_array_element_setup (Var ip) pos (Var output) MLOAD (Var source)
    hi di stride memsz sa = ((idx,child,dstop),sb) /\ fn_has_code sa sb func /\
  st.cs_next_var <= sa.cs_next_var /\ not_fresh_at sa ip /\
  sb.cs_next_var <= ceiling.cs_next_var /\
  b.vs_current_bb = sa.cs_current_bb /\ b.vs_inst_idx = LENGTH sa.cs_current_insts /\
  j < n /\ p+32+n*stride <= L /\ (dec_info_needs_offset di ==> 32 <= stride) /\
  fn_inst_ids_distinct func ==>
  ?data head cut t H z.
    (^parent) t /\
    abi_malformed_entry H0 ctx func cenv cx es cut sites dstid live
      (Var source) hi pos (Var output) B L xs p d outsz t /\
    (^counter) t /\ (^root_ghosts) t H z /\
    fresh_vars_wrt ceiling t /\ ~t.vs_halted /\
    ptr_covers H z ip t 32 /\ mload slot t = n2w j /\
    (!a. slot <= a /\ a < slot+32 ==> a NOTIN z.t_mem) /\
    t.vs_current_bb = cut.cs_current_bb /\ t.vs_inst_idx = LENGTH cut.cs_current_insts /\
    sa.cs_next_var <= cut.cs_next_var /\ cut.cs_next_var <= sb.cs_next_var /\
    fn_has_code cut sb func /\
    eval_operand idx t = SOME (n2w j) /\ op_taint z idx = {} /\ op_prov H idx = NONE /\
    eval_operand data t = SOME (n2w (p+32)) /\ op_taint z data = {} /\ op_prov H data = NONE /\
    eval_operand head t = SOME (n2w (p+32+j*stride)) /\ op_taint z head = {} /\ op_prov H head = NONE /\
    EVERY (abi_decoder_operand_live cut.cs_next_var) [idx;data;head] /\
    (^read_layout) cut t H z data head /\ (^worlds) b t /\ (^path) b Gb tb (OK t) H z
Proof
  simp_tac bool_ss [] >> strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE[abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (strip_assume_tac o PURE_REWRITE_RULE[abi_malformed_allocated_window_def]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `B+L <= b.vs_alloca_next /\ slot+32 <= b.vs_alloca_next` by
    (conj_tac >- (drule_all alloca_site_registered_below >> decide_tac) >>
     metis_tac[alloca_site_registered_below]) >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `w2n (n2w slot:bytes32) = slot` by (fs[alloca_room_def] >> simp[w2n_n2w,LESS_MOD]) >>
  `not_fresh_at sa source /\ not_fresh_at sa output /\
   abi_decoder_operand_live sa.cs_next_var pos` by
    (fs[GSYM calldata_operand_live_not_fresh] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `w2n (n2w slot:bytes32)+32 <= b.vs_alloca_next /\ mload (w2n (n2w slot:bytes32)) b = n2w j /\
   (!a. w2n (n2w slot:bytes32) <= a /\ a < w2n (n2w slot:bytes32)+32 ==> a NOTIN tb.t_mem)` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp b` by
    (qhdtm_assum `abi_malformed_entry`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) o
        cj 1 o REWRITE_RULE [abi_malformed_entry_def])) >>
  drule_all malformed_indexed_reads_joint_frame >>
  disch_then (qspec_then `PG` (qx_choosel_then [`data`,`head`,`cut`,`t`,`H`,`z`] strip_assume_tac)) >>
  `alloca_history func t` by (irule body_full_path_alloca_history >> metis_tac[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid b t` by
    (`abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid b b` by
       metis_tac[abi_malformed_resource_refl] >>
     irule abi_malformed_resource_register_update >> simp[] >>
     qexists `b with vs_inst_idx := LENGTH cut.cs_current_insts` >>
     simp[abi_malformed_resource_post_inst_idx] >>
     simp[lookup_var_def] >> fs[not_fresh_at_def, GSYM lookup_var_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  `st.cs_next_var <= cut.cs_next_var` by decide_tac >>
  `(^parent) t` by
    (simp_tac bool_ss [] >> irule abi_malformed_aggregate_reentry >>
     simp_tac (srw_ss()) [] >> conj_tac >- simp[] >> qexistsl [`b`,`sites`,`st`] >> simp[]) >>
  `abi_malformed_entry H0 ctx func cenv cx es cut sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz t` by
    (irule abi_malformed_aggregate_reentry >> simp_tac (srw_ss()) [] >>
     conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
     qexistsl [`b`,`sites`,`st`] >> simp[]) >>
  `mload slot t = mload slot b` by (pure_rewrite_tac[mload_def] >> simp[]) >>
  qexistsl [`data`,`head`,`cut`,`t`,`H`,`z`] >>
  qpat_x_assum `t = b with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
  simp[] >>
  Cases_on `pos` >> Cases_on `hi` >>
  fs[op_prov_def,op_taint_def,GSYM calldata_operand_live_not_fresh] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

(* Keep the scalar-lift premise identical to the guard producer's premise. *)
val (scalar_abort_lift, _) =
  boolSyntax.dest_conj (#1 (boolSyntax.dest_imp (concl malformed_indexed_guard_revert_joint)));

val pass_mode = ``\cut nav cmp off data delta q t H z.
  if dec_info_needs_offset di then
    emit_op ADD [data;off] cut = (child,cmp) /\
    abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) /\
    fn_has_code cut nav func /\
    eval_operand data t = SOME (n2w (p+32)) /\ eval_operand off t = SOME (n2w delta) /\
    abi_decoder_operand_live cut.cs_next_var data /\
    p+32 < dimword (:256) /\ delta < dimword (:256) /\
    ~(w2n (n2w (p+32+delta):bytes32) < p+32 \/
      L < w2n (n2w (p+32+delta):bytes32) + stride) /\
    (!op. op IN {data;off;hi} ==> op_prov H op = NONE /\ op_taint z op = {}) /\
    q = p+32+delta
  else nav = cut /\ q = p+32+j*stride /\ q < dimword (:256) /\
    eval_operand child t = SOME (n2w q) /\ abi_decoder_operand_live cut.cs_next_var child /\
    op_prov H child = NONE /\ op_taint z child = {}``;

val child_cut = ``\q t H z u Gu tu.
  abi_malformed_entry H0 ctx func cenv cx es sb child_sites dstid live
    (Var source) hi child dstop B L xs q (d+32+j*memsz) memsz u /\
  (^parent) u /\ (^counter) u /\ (^root_ghosts) u Gu tu /\
  (?r. dstop = Var r /\ ptr_covers Gu tu r u memsz) /\
  op_prov Gu child = NONE /\ op_taint tu child = {} /\
  eval_operand idx u = SOME (n2w j) /\ abi_decoder_operand_live sb.cs_next_var idx /\
  op_prov Gu idx = NONE /\ op_taint tu idx = {} /\
  ptr_covers Gu tu ip u 32 /\ mload slot u = n2w j /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tu.t_mem) /\
  fresh_vars_wrt ceiling u /\ ~u.vs_halted /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (^worlds) t u /\ (^path) t H z (OK u) Gu tu``;

Theorem finite_reject_indexed_pass_boundary[local]:
  (^parent) t /\ (^counter) t /\ (^root_ghosts) t H z /\
  abi_malformed_entry H0 ctx func cenv cx es cut sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz t /\
  (^pass_mode) cut nav cmp off data delta q t H z /\
  abi_decode_indexed_address (Var output) idx memsz nav = (dstop,sb) /\
  fn_has_code nav sb func /\ child_sites SUBSET sites /\
  st.cs_next_var <= cut.cs_next_var /\ not_fresh_at cut ip /\
  cut.cs_next_var <= nav.cs_next_var /\ nav.cs_next_var <= ceiling.cs_next_var /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fn_inst_ids_distinct func /\
  32+j*memsz+memsz <= outsz /\ fresh_vars_wrt ceiling t /\ ~t.vs_halted /\
  t.vs_current_bb = cut.cs_current_bb /\ t.vs_inst_idx = LENGTH cut.cs_current_insts /\
  eval_operand idx t = SOME (n2w j) /\ abi_decoder_operand_live cut.cs_next_var idx /\
  op_prov H idx = NONE /\ op_taint z idx = {} /\
  ptr_covers H z ip t 32 /\ mload slot t = n2w j /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN z.t_mem) ==>
  ?u Gu tu. (^child_cut) q t H z u Gu tu
Proof
  simp_tac bool_ss [] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qhdtm_assum `abi_malformed_entry`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) o
        cj 1 o REWRITE_RULE [abi_malformed_entry_def])) >>
  drule_all (SIMP_RULE bool_ss [pairTheory.FST,pairTheory.SND]
    (Q.INST [`ops` |-> `(idx,pos,dstop)`] malformed_indexed_pass_joint)) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`u`,`Gu`,`tu`,`r`] strip_assume_tac)) >>
  `alloca_inv t /\ local_ptrs_reserved cenv st` by
    (qpat_assum `abi_malformed_entry _ _ _ _ _ _ st _ _ _ _ _ _ _ _ _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE [abi_malformed_entry_def]) >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `alloca_history func u` by (irule body_full_path_alloca_history >> metis_tac[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid t u` by
    (irule abi_malformed_resource_weaken >> qexistsl [`cut.cs_next_var`,`sites`] >> simp[]) >>
  `(^parent) u` by
    (simp_tac bool_ss [] >> irule abi_malformed_aggregate_reentry >>
     simp_tac (srw_ss()) [] >> conj_tac
     >- simp[] >> qexistsl [`t`,`sites`,`st`] >> simp[]) >>
  `lookup_var ip u = lookup_var ip t /\ ptr_covers Gu tu ip u 32` by
    (qpat_assum `!x. not_fresh_at cut x ==> _` (qspec_then `ip` mp_tac) >>
     simp[GSYM AND_IMP_INTRO] >> rpt strip_tac >>
     irule ptr_covers_frame >> qexistsl [`H`,`t`,`z`] >> simp[]) >>
  `mload slot u = mload slot t` by (pure_rewrite_tac[mload_def] >> simp[]) >>
  `op_prov Gu pos = NONE /\ op_taint tu pos = {} /\
   op_prov Gu hi = NONE /\ op_taint tu hi = {}` by
    (Cases_on `pos` >> Cases_on `hi` >>
     fs[abi_malformed_entry_def,op_prov_def,op_taint_def,GSYM calldata_operand_live_not_fresh] >>
     metis_tac[]) >>
  qexistsl [`u`,`Gu`,`tu`] >> simp[] >> first_assum (ACCEPT_TAC o BETA_RULE)
QED

(* The indirect arm only extends the compiler's variable counter. *)
Theorem finite_reject_guard_counter[local]:
  emit_op ADD [data;off] cut = (child,cmp) /\
  abi_decode_array_pointer_guard child data hi stride cmp = ((),nav) ==>
  cut.cs_next_var <= nav.cs_next_var
Proof
  `dynamic_straight_fresh (abi_decode_array_pointer_guard child data hi stride)` by
    (simp[abi_decode_array_pointer_guard_def,abi_decode_ge_guard_def,
          compile_abi_decode_range_check_def] >>
     rpt (FIRST [CHANGED_TAC BETA_TAC,irule dynamic_straight_fresh_bind,
                 irule dynamic_straight_fresh_ignore_bind,gen_tac,conj_tac]) >>
     simp[dynamic_straight_fresh_return,dynamic_straight_fresh_emit_op,
          dynamic_straight_fresh_emit_void,fresh_write_op_def]) >>
  strip_tac >> fs[dynamic_straight_fresh_def] >>
  first_x_assum drule >> strip_tac >>
  drule exprSimAccountsTheory.emit_op_extends_next_var >> decide_tac
QED

(* Normalize both arms to the same passing interface before invoking it. *)
Theorem finite_reject_after_indexed_reads[local]:
  ^scalar_abort_lift /\ (^parent) t /\ (^counter) t /\ (^root_ghosts) t H z /\
  abi_malformed_entry H0 ctx func cenv cx es cut sites dstid live
    (Var source) hi pos (Var output) B L xs p d outsz t /\
  (^read_layout) cut t H z data head /\ fn_has_code cut sb func /\
  child_sites SUBSET sites /\ st.cs_next_var <= cut.cs_next_var /\ not_fresh_at cut ip /\
  sb.cs_next_var <= ceiling.cs_next_var /\ fn_inst_ids_distinct func /\
  32+j*memsz+memsz <= outsz /\ fresh_vars_wrt ceiling t /\ ~t.vs_halted /\
  t.vs_current_bb = cut.cs_current_bb /\ t.vs_inst_idx = LENGTH cut.cs_current_insts /\
  eval_operand idx t = SOME (n2w j) /\ op_taint z idx = {} /\ op_prov H idx = NONE /\
  eval_operand data t = SOME (n2w (p+32)) /\ op_taint z data = {} /\ op_prov H data = NONE /\
  eval_operand head t = SOME (n2w (p+32+j*stride)) /\ op_taint z head = {} /\ op_prov H head = NONE /\
  EVERY (abi_decoder_operand_live cut.cs_next_var) [idx;data;head] /\
  ptr_covers H z ip t 32 /\ mload slot t = n2w j /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN z.t_mem) /\
  p+32+j*stride+stride <= L /\ stride < dimword (:256) ==>
  (^abort) t H z \/ ?u Gu tu.
    (p+32 + if dec_info_needs_offset di then abi_head_word (DROP (p+32+j*stride) xs) else
      j*stride)+stride <= L /\
    (^child_cut) (p+32 + if dec_info_needs_offset di then abi_head_word (DROP (p+32+j*stride) xs) else
      j*stride) t H z u Gu tu
Proof
  simp_tac bool_ss [listTheory.EVERY_DEF] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qhdtm_assum `abi_malformed_entry`
       (ACCEPT_TAC o MATCH_MP (SPEC_ALL bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) o
        cj 1 o REWRITE_RULE [abi_malformed_entry_def])) >>
  `L < dimword (:256) /\ hi <> Lit 0w /\ eval_operand hi t = SOME (n2w L) /\
   abi_decoder_operand_live cut.cs_next_var hi` by
    (fs[abi_malformed_entry_def,abi_malformed_allocated_window_def] >> decide_tac) >>
  `p+32 < dimword (:256)` by decide_tac >>
  qabbrev_tac `delta = abi_head_word (DROP (p+32+j*stride) xs)` >>
  `delta < dimword (:256)` by
    simp[Abbr `delta`,abi_head_word_def,dec_number_def,contractABITheory.dest_NumV_def,w2n_lt] >>
  qabbrev_tac `q = p+32 + if dec_info_needs_offset di then delta else j*stride` >>
  `(^abort) t H z \/ ?nav cmp off.
    (^pass_mode) cut nav cmp off data delta q t H z /\
    abi_decode_indexed_address (Var output) idx memsz nav = (dstop,sb) /\
    fn_has_code nav sb func /\ cut.cs_next_var <= nav.cs_next_var` by
    (BETA_TAC >> Cases_on `dec_info_needs_offset di` >>
     qpat_x_assum `if _ then _ else _` mp_tac >> pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac
     >- (Cases_on `w2n (n2w (p+32+delta):bytes32) < p+32 \/
                       L < w2n (n2w (p+32+delta):bytes32) + stride`
         >- (disj1_tac >>
             `EVERY (abi_decoder_operand_live cut.cs_next_var) [data;off;hi]` by simp[] >>
             `!op. MEM op [data;off;hi] ==> op_prov H op = NONE /\ op_taint z op = {}` by
               simp[DISJ_IMP_THM] >>
             drule_all malformed_indexed_guard_revert_joint >>
             disch_then (qspec_then `PG` (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac)) >>
             qexistsl [`v`,`Gv`,`tv`] >> simp[]) >>
         disj2_tac >> qexistsl [`nav`,`cmp`,`off`] >>
         drule_all finite_reject_guard_counter >> strip_tac >>
         simp_tac bool_ss [Abbr `q`,DISJ_IMP_THM,pred_setTheory.IN_INSERT,
                           pred_setTheory.NOT_IN_EMPTY] >>
         asm_rewrite_tac[] >> decide_tac) >>
     disj2_tac >> qexistsl [`cut`,`cut`,`head`] >> simp[Abbr `q`] >> decide_tac) >>
  RULE_ASSUM_TAC BETA_RULE
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  `nav.cs_next_var <= ceiling.cs_next_var` by
    (drule abi_decode_indexed_address_counters >> decide_tac) >>
  `q+stride <= L` by
    (Cases_on `dec_info_needs_offset di` >>
     fs[Abbr `q`] >>
     mp_tac (Q.INST [`data_base` |-> `p+32`, `H` |-> `L`, `sz` |-> `stride`]
       abi_array_pointer_check_bounds) >> simp[]) >>
  mp_tac (BETA_RULE finite_reject_indexed_pass_boundary) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] assume_tac) >>
  qexistsl [`u`,`Gu`,`tu`] >> gvs[Abbr `q`, Abbr `delta`]
QED

(* Splice execution up to the child, with an early exit for a failed guard. *)
Theorem finite_reject_to_child[local]:
  ^scalar_abort_lift /\ (^repeat_entry) j h Gh th /\
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
    (Var ip) cnt ls = ((),en) /\ fn_has_code ls en func /\
  hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
  st.cs_next_var <= ls.cs_next_var /\ not_fresh_at ls ip /\
  ls.cs_next_var + 5 <= ceiling.cs_next_var /\ fn_inst_ids_distinct func /\
  abi_decode_array_element_setup (Var ip) pos (Var output) MLOAD (Var source)
    hi di stride memsz sa = ((idx,child,dstop),sb) /\ fn_has_code sa sb func /\
  sa.cs_current_bb = fresh_label_output "dec_dyn_body" (ls.cs_next_label+1) /\
  sa.cs_current_insts = [] /\ sa.cs_next_var = ls.cs_next_var+5 /\
  sb.cs_next_var <= ceiling.cs_next_var /\ child_sites SUBSET sites /\
  n = abi_head_word (DROP p xs) /\ j < n /\ p+32+n*stride <= L /\
  (dec_info_needs_offset di ==> 32 <= stride) /\ stride < dimword (:256) /\
  32+n*memsz <= outsz ==>
  (^abort) h Gh th \/ ?u Gu tu.
    (p+32 + if dec_info_needs_offset di then abi_head_word (DROP (p+32+j*stride) xs) else
      j*stride)+stride <= L /\
    (^child_cut) (p+32 + if dec_info_needs_offset di then abi_head_word (DROP (p+32+j*stride) xs) else
      j*stride) h Gh th u Gu tu
Proof
  simp_tac bool_ss [] >> strip_tac >>
  `p+32 <= L` by decide_tac >>
  drule_all (BETA_RULE finite_reject_header) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`b`,`Gb`,`tb`] strip_assume_tac)) >>
  `b.vs_current_bb = sa.cs_current_bb /\ b.vs_inst_idx = LENGTH sa.cs_current_insts /\
   st.cs_next_var <= sa.cs_next_var /\ not_fresh_at sa ip` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  drule_all (BETA_RULE finite_reject_indexed_read_boundary) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`data`,`head`,`cut`,`t`,`H`,`z`] strip_assume_tac)) >>
  `st.cs_next_var <= cut.cs_next_var /\ not_fresh_at cut ip` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  `p+32+j*stride+stride <= L /\ 32+j*memsz+memsz <= outsz` by
    (`SUC j <= n` by decide_tac >>
     `SUC j * stride <= n * stride /\ SUC j * memsz <= n * memsz` by simp[LE_MULT_RCANCEL] >>
     qpat_x_assum `SUC j * stride <= _` mp_tac >>
     qpat_x_assum `SUC j * memsz <= _` mp_tac >>
     pure_rewrite_tac[MULT_CLAUSES] >> decide_tac) >>
  `EVERY (abi_decoder_operand_live cut.cs_next_var) [idx;data;head]` by simp[] >>
  mp_tac (BETA_RULE finite_reject_after_indexed_reads) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choosel_then [`v`,`Gv`,`tv`] strip_assume_tac)
    (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac))
  >- (disj1_tac >> qexistsl [`v`,`Gv`,`tv`] >> simp[] >>
      rpt gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]) >>
  disj2_tac >> qexistsl [`u`,`Gu`,`tu`] >> simp[] >>
  rpt gen_tac >> metis_tac[fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans]
QED

(* After a good child, frame the parent's live operands and both pointers at
   the child's actual return. The resource post restores the source bytes;
   the child ghost post already supplies the clean source window. *)
Theorem finite_reject_child_return[local]:
  (^parent) u /\ (^counter) u /\ (^root_ghosts) u Gu tu /\
  ptr_covers Gu tu ip u 32 /\ not_fresh_at sb ip /\
  eval_operand (Var iv) u = SOME (n2w j) /\
  abi_decoder_operand_live sb.cs_next_var (Var iv) /\
  op_prov Gu (Var iv) = NONE /\ op_taint tu (Var iv) = {} /\
  abi_valid_allocated_post tv v ctx func cenv cx es sb se ceiling dstid
    (d+32+j*memsz) memsz u r /\
  abi_malformed_scratch_sites sb se func SUBSET sites /\
  st.cs_next_var <= sb.cs_next_var /\
  abi_decode_ptr_window Gr tr r source (n2w B) L /\
  (!x. abi_decoder_operand_live sb.cs_next_var (Var x) ==>
     FLOOKUP Gr x = FLOOKUP Gu x /\ op_taint tr (Var x) = op_taint tu (Var x)) /\
  alloca_history func r /\ allocas_from lo r /\ lo <= r.vs_alloca_next ==>
  (^parent) r /\ (^counter) r /\ (^root_ghosts) r Gr tr /\
  fresh_vars_wrt ceiling r /\ ~r.vs_halted /\
  r.vs_current_bb = se.cs_current_bb /\ r.vs_inst_idx = LENGTH se.cs_current_insts /\
  ptr_covers Gr tr ip r 32 /\ eval_operand (Var iv) r = SOME (n2w j) /\
  op_prov Gr (Var iv) = NONE /\ op_taint tr (Var iv) = {}
Proof
  simp_tac bool_ss [abi_valid_allocated_post_def] >> strip_tac >>
  `local_ptrs_reserved cenv st` by fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid u r` by
    (irule abi_malformed_resource_weaken >> qexistsl [`sb.cs_next_var`,
       `abi_malformed_scratch_sites sb se func`] >> simp[]) >>
  `(^parent) r` by
    (simp_tac bool_ss [] >> irule abi_malformed_aggregate_reentry >>
     simp_tac (srw_ss()) [] >> conj_tac >- simp[] >> qexistsl [`u`,`sites`,`st`] >> simp[]) >>
  `abi_decoder_operand_live sb.cs_next_var (Var output) /\
   abi_decoder_operand_live sb.cs_next_var hi /\
   abi_decoder_operand_live sb.cs_next_var pos` by
    (fs[abi_malformed_entry_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `abi_decoder_operand_live sb.cs_next_var (Var ip)` by
    fs[GSYM calldata_operand_live_not_fresh] >>
  `!x. abi_decoder_operand_live sb.cs_next_var (Var x) /\ IS_SOME (lookup_var x u) ==>
       lookup_var x r = lookup_var x u` by
    (fs[abi_malformed_resource_post_def] >> rpt gen_tac >>
     Cases_on `lookup_var x u` >> simp[] >> metis_tac[eval_operand_def]) >>
  `ptr_covers Gr tr ip r 32 /\ ptr_covers Gr tr output r outsz` by
    (conj_tac >> irule ptr_covers_frame >>
     qexistsl [`Gu`,`u`,`tu`] >> fs[bodyPtrDefsTheory.ptr_covers_def]) >>
  fs[abi_malformed_resource_post_def, eval_operand_def] >>
  Cases_on `pos` >> Cases_on `hi` >> fs[op_prov_def,op_taint_def] >> metis_tac[]
QED

val old_live = ``\st (G:string |-> num # num) tn H z.
  !x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP H x = FLOOKUP G x /\ op_taint z (Var x) = op_taint tn (Var x)``;
val child_ghosts = ``\pos output sz s G tn.
  abi_decode_ptr_window G tn s source (n2w B) L /\ ptr_covers G tn output s sz /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\ op_taint tn pos = {} /\ op_taint tn hi = {} /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s``;
val source_view = ``\ty b. if is_dynamic (vyper_to_abi_type env ty) then DROP b (xs:word8 list)
  else TAKE (static_length (vyper_to_abi_type env ty)) (DROP b xs)``;
val malformed_view = ``\ty bytes. ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bytes /\
  abi_vyper_admissible env ty (dec (vyper_to_abi_type env ty) bytes))``;
val success_ih = ``!H0 ce env sf ty tv v ctx func cenv cx es st en source hi pos
  output B L xs p d dstid live ceiling s G tn lo PG.
  abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
    st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s /\
  ~ctx_has_dalloca ctx /\ (^child_ghosts) pos output (type_memory_bytes ce ty) s G tn ==>
  ?u H z. abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
      d (type_memory_bytes ce ty) s u /\ (^worlds) s u /\ (^path) s G tn (OK u) H z /\
    ptr_covers H z output u (type_memory_bytes ce ty) /\
    abi_decode_ptr_window H z u source (n2w B) L /\
    (!mem. mem_agree_outside z.t_mem u.vs_memory mem ==> val_in_memory tv v d mem) /\
    (^old_live) st G tn H z /\
    z.t_stor = tn.t_stor /\ z.t_trans = tn.t_trans /\ z.t_imm = tn.t_imm /\
    (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN z.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
val reject_ih = ``\ce env sf ty tv. !H0 output b_op source hi st en func ctx cenv cx es
  dstid live B L xs b d s ceiling bytes G tn lo PG.
  abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
  compile_abi_decode_to_buf (Var output) b_op MLOAD (Var source) hi
    (type_to_abi_dec_info sf ce ty) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\
  assignable_type env ty /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf ty < dimword (:256) /\
  abi_malformed_entry H0 ctx func cenv cx es st (abi_malformed_scratch_sites st en func)
    dstid live (Var source) hi b_op (Var output) B L xs b d (type_memory_bytes ce ty) s /\
  (case type_to_abi_dec_info sf ce ty of DecPrimWord clamp => b+32 <= L | _ => T) /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  bytes = (^source_view) ty b /\ (^malformed_view) ty bytes /\
  ~ctx_has_dalloca ctx /\ (^child_ghosts) b_op output (type_memory_bytes ce ty) s G tn ==>
  (^abort) s G tn``;

val good_at = ``\q. q <= L /\
  (is_dynamic (vyper_to_abi_type env ty) \/ q + static_length (vyper_to_abi_type env ty) <= L) /\
  vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
  (?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP q xs)) = SOME v)``;
val child_layout = ``
  di = type_to_abi_dec_info (sf:string |-> (string # type # num) list) ce ty /\
  memsz = type_memory_bytes ce ty /\
  child_sites = abi_malformed_scratch_sites sb se func /\ child_sites SUBSET sites /\
  compile_abi_decode_to_buf dstop child MLOAD (Var source) hi di sb = ((),se) /\
  fn_has_code sb se func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  st.cs_next_var <= sb.cs_next_var /\ se.cs_next_var <= ceiling.cs_next_var /\
  not_fresh_at sb ip /\ idx = Var iv``;
val child_meta = ``
  abi_decoder_coherent ce env sf ty tv /\ abi_decode_bytes_widths env ty /\
  (?av. has_type (vyper_to_abi_type env ty) av) /\ assignable_type env ty /\
  type_memory_size tv < dimword (:256) /\ abi_size_bound sf ty < dimword (:256)``;
val backedge_layout = ``
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [ip] /\ not_local_ptr cenv es.scopes ip /\ inst.inst_id IN sites /\
  st.cs_next_var <= se.cs_next_var /\ se.cs_next_var < ceiling.cs_next_var /\
  ip <> STRING #"%" (toString se.cs_next_var) /\
  lookup_block se.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = se.cs_current_insts ++ abi_decode_backedge_insts se.cs_next_id iv
     (STRING #"%" (toString se.cs_next_var)) (Var ip) hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0``;

Theorem finite_reject_bad_child[local]:
  (^reject_ih) ce env sf ty tv /\ ^child_layout /\ ^child_meta /\
  (^child_cut) q h Gh th u Gu tu /\
  (^malformed_view) ty ((^source_view) ty q) /\
  (case di of DecPrimWord clamp => q+32 <= L | _ => T) ==>
  (^abort) h Gh th
Proof
  simp_tac bool_ss [] >> disch_then (CONJUNCTS_THEN2 (mk_asm "reject")
    (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qpat_x_assum `?r. dstop = Var r /\ _` strip_assume_tac >>
  rule_assum_tac BETA_RULE >> gnvs[] >>
  asm "reject" drule_all >>
  disch_then (qspec_then `PG` (qx_choosel_then [`w`,`Gw`,`tw`] strip_assume_tac)) >>
  qexistsl [`w`,`Gw`,`tw`] >> simp[] >> rpt gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> simp[]
QED

Theorem finite_reject_good_child[local]:
  (^success_ih) /\ ^child_layout /\ ^child_meta /\ ^backedge_layout /\
  (^child_cut) q h Gh th u Gu tu /\ (^good_at) q /\ j < n /\ n < dimword (:256) ==>
  ?t H z. (^repeat_entry) (SUC j) t H z /\ (^worlds) h t /\ (^path) h Gh th (OK t) H z
Proof
  simp_tac bool_ss [] >> disch_then (CONJUNCTS_THEN2 (mk_asm "valid") strip_assume_tac) >>
  `(^child_ghosts) child r memsz u Gu tu` by (BETA_TAC >> simp[]) >>
  `abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es sb se
      (Var source) hi child dstop B L xs q (d+32+j*memsz) dstid live ceiling u` by
    gvs[abi_valid_allocated_entry_def] >>
  rule_assum_tac BETA_RULE >> gvs[] >>
  asm "valid" drule_all >>
  disch_then (qspec_then `PG` (qx_choosel_then [`w`,`Gw`,`tw`] strip_assume_tac)) >>
  mp_tac (BETA_RULE (Q.INST [`r` |-> `w`, `Gr` |-> `Gw`, `tr` |-> `tw`,
    `memsz` |-> `type_memory_bytes ce ty`] finite_reject_child_return)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `lookup_block w.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all (BETA_RULE (Q.INST [`id` |-> `se.cs_next_id`,
    `next` |-> `se.cs_next_var`, `prefix` |-> `se.cs_current_insts`] finite_reject_repeat)) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`t`,`H`,`z`] strip_assume_tac)) >>
  qexistsl [`t`,`H`,`z`] >> simp[] >> rpt gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gu`,`u`,`tu`] >> simp[] >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gw`,`w`,`tw`] >> simp[]
QED

val loop_layout = ``
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
    (Var ip) cnt ls = ((),en) /\ fn_has_code ls en func /\
  hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label /\
  st.cs_next_var <= ls.cs_next_var /\ not_fresh_at ls ip /\
  ls.cs_next_var + 5 <= ceiling.cs_next_var /\
  abi_decode_array_element_setup (Var ip) pos (Var output) MLOAD (Var source)
    hi di stride memsz sa = ((idx,child,dstop),sb) /\ fn_has_code sa sb func /\
  sa.cs_current_bb = fresh_label_output "dec_dyn_body" (ls.cs_next_label+1) /\
  sa.cs_current_insts = [] /\ sa.cs_next_var = ls.cs_next_var+5 /\
  sb.cs_next_var <= ceiling.cs_next_var /\ n = abi_head_word (DROP p xs) /\
  p+32+n*stride <= L /\ (dec_info_needs_offset di ==> 32 <= stride) /\
  stride < dimword (:256) /\ 32+n*memsz <= outsz``;
val selected_pos = ``\j. p+32 + if dec_info_needs_offset di then
  abi_head_word (DROP (p+32+j*stride) xs) else j*stride``;
val first_bad = ``\i.
  i < n /\ n < dimword (:256) /\ (!j. j < i ==> (^good_at) ((^selected_pos) j)) /\
  (^malformed_view) ty ((^source_view) ty ((^selected_pos) i))``;

Theorem finite_reject_loop_to_bad[local]:
  ^scalar_abort_lift /\ ^loop_layout /\ ^child_layout /\ ^child_meta /\
  ^backedge_layout /\ (^success_ih) /\ (^reject_ih) ce env sf ty tv /\
  (case di of DecPrimWord clamp => 32 <= stride | _ => T) /\
  (^first_bad) i ==> !j h Gh th. j <= i /\ (^repeat_entry) j h Gh th ==> (^abort) h Gh th
Proof
  simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!m j h Gh th. m = i-j /\ j <= i /\ (^repeat_entry) j h Gh th ==> (^abort) h Gh th`
    suffices_by
      (BETA_TAC >> strip_tac >> qx_genl_tac [`j`,`h`,`Gh`,`th`] >>
       qpat_x_assum `!m j h Gh th. m = i-j /\ _ ==> _`
         (qspecl_then [`i-j`,`j`,`h`,`Gh`,`th`] mp_tac) >>
       qpat_assum `hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label`
         (fn th => simp_tac bool_ss [th])) >>
  BETA_TAC >> completeInduct_on `m` >>
  rpt gen_tac >> strip_tac >> `j < n` by decide_tac >>
  mp_tac (BETA_RULE finite_reject_to_child) >> (impl_tac >- asm_rewrite_tac[]) >>
  simp_tac bool_ss [LET_THM] >>
  qabbrev_tac `q = p+32 + if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*stride) xs) else j*stride` >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC (qx_choosel_then [`u`,`Gu`,`tu`]
    (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  Cases_on `j = i`
  >- (`(case di of DecPrimWord clamp => q+32 <= L | _ => T)` by
        (qpat_assum `q+stride <= L` mp_tac >>
         qpat_assum `(case di of DecPrimWord clamp => 32 <= stride | _ => T)` mp_tac >>
         Cases_on `di` >> simp_tac (srw_ss()) [] >> decide_tac) >>
      Q.SUBGOAL_THEN `(^malformed_view) ty ((^source_view) ty q)`
        (assume_tac o SIMP_RULE bool_ss [])
      >- (qpat_assum `j = i` (fn th => simp_tac bool_ss [Abbr `q`,th]) >>
          first_assum ACCEPT_TAC) >>
      mp_tac (SIMP_RULE bool_ss [] finite_reject_bad_child) >>
      (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
      disch_then ACCEPT_TAC) >>
  `j < i` by decide_tac >>
  Q.SUBGOAL_THEN `(^good_at) q` (assume_tac o SIMP_RULE bool_ss [])
  >- (simp_tac bool_ss [Abbr `q`] >>
      first_assum irule >> simp[]) >>
  mp_tac (SIMP_RULE bool_ss [] finite_reject_good_child) >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choosel_then [`t`,`H`,`z`]
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  qpat_x_assum `!m'. m' < m ==> _` (qspec_then `i-SUC j` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`SUC j`,`t`,`H`,`z`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> decide_tac)) >>
  disch_then (qx_choosel_then [`w`,`Gw`,`tw`] strip_assume_tac) >>
  qexistsl [`w`,`Gw`,`tw`] >> simp[] >> rpt gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`H`,`t`,`z`] >> simp[]
QED

(* The span guard has passed, so the selected failure cannot be a short
   member head. Normalize the homogeneous source scan to the loop stride. *)
Theorem finite_reject_select[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decode_bytes_widths env (ArrayT ty (Dynamic maxn)) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  abi_size_bound sf (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  (?av. has_type (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av) /\
  p < dimword (:256) /\ L < dimword (:256) /\ LENGTH xs = L /\
  (^malformed_view) (ArrayT ty (Dynamic maxn)) ((^source_view) (ArrayT ty (Dynamic maxn)) p) /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  stride = abi_member_head_size (vyper_to_abi_type env ty) /\
  di = type_to_abi_dec_info sf ce ty ==>
  ?i. (^first_bad) i
Proof
  simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (xs:word8 list) < dimword (:256) /\ p+32 <= L /\ ~(L < p+32) /\ ~(maxn < n)` by decide_tac >>
  drule_all (SIMP_RULE bool_ss [] malformed_aggregate_first_bad_child) >>
  simp_tac bool_ss [TypeBase.case_def_of ``:type``, vyperASTTheory.bound_case_def, LET_THM] >>
  qpat_x_assum `n = abi_head_word _` (fn th => rewrite_tac [GSYM th]) >>
  asm_simp_tac bool_ss [rich_listTheory.LENGTH_REPLICATE] >>
  disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 kall_tac (qx_choose_then `i` (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "good_scan")
        (CONJUNCTS_THEN2 kall_tac (mk_asm "bad_scan")))))))) >>
  `!j. j < n ==> EL j (REPLICATE n ty) = ty /\
      SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) (TAKE j (REPLICATE n ty)))) = j*stride` by
    (rpt strip_tac >- simp[rich_listTheory.EL_REPLICATE] >>
     `TAKE j (REPLICATE n ty) = REPLICATE j ty` by
       (mp_tac (Q.ISPECL [`j:num`,`[]:vyperAST$type list`,`n:num`,`j:num`,`ty:vyperAST$type`] valueEncodingProofsTheory.TAKE_append_REPLICATE) >>
        simp[TAKE_LENGTH_TOO_LONG] >> decide_tac) >>
     simp[rich_listTheory.map_replicate,rich_listTheory.SUM_REPLICATE]) >>
  qexists_tac `i` >> asm_simp_tac bool_ss [] >> conj_tac
  >- (gen_tac >> disch_tac >> `j < n` by decide_tac >>
      asm "good_scan" (qspec_then `j` mp_tac) >>
      asm_simp_tac bool_ss [] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `SUC i * stride <= n * stride` by (simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `p+32+i*stride+stride <= L` by
    (qpat_assum `SUC i * stride <= n * stride` mp_tac >>
     simp_tac bool_ss [MULT_CLAUSES] >> decide_tac) >>
  `~(L < p+32+i*stride+stride)` by decide_tac >>
  qpat_assum `stride = abi_member_head_size _` (fn stride_eq =>
    qpat_assum `~(L < p+32+i*stride+stride)`
      (assume_tac o PURE_REWRITE_RULE [stride_eq])) >>
  asm "bad_scan" mp_tac >> asm_simp_tac bool_ss [] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Theorem finite_reject_enter_loop[local]:
  abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
    ((Var ip,cnt),ls) /\
  compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
    (Var ip) cnt ls = ((),en) /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (^parent) s /\ (^root_ghosts) s G tn /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  inst = mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (ls.cs_next_var-1))] /\
  MEM inst (fn_insts func) /\ ls.cs_next_id-2 IN sites /\
  hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label ==>
  ?h slot Gh th. (^repeat_entry) 0 h Gh th /\ (^worlds) s h /\ (^path) s G tn (OK h) Gh th
Proof
  simp_tac bool_ss [] >> strip_tac >>
  qspec_then `ip` mp_tac (Q.GEN `ix`
    (SIMP_RULE bool_ss [rich_listTheory.LENGTH_REPLICATE]
      (Q.INST [`vs` |-> `REPLICATE n (NoneV:vyperValue$value)`,
               `ip` |-> `Var ix`, `H` |-> `H0`]
        abi_valid_allocated_finite_init_joint))) >>
  (impl_tac >- (qpat_x_assum `inst = mk_inst _ _ _ _` SUBST_ALL_TAC >> asm_rewrite_tac[])) >>
  disch_then (qx_choosel_then [`h`,`slot`,`Gh`,`th`] strip_assume_tac) >>
  qhdtm_x_assum `abi_valid_allocated_array_inv`
    (strip_assume_tac o SIMP_RULE bool_ss [abiValidAllocatedArrayPrefixTheory.abi_valid_allocated_array_inv_def]) >>
  qexistsl [`h`,`slot`,`Gh`,`th`] >>
  fs[eval_operand_def,venomInstTheory.mk_inst_def]
QED

(* Identify the actual allocation instruction, not just its address. *)
Theorem finite_reject_initializer_layout[local]:
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray di stride memsz dyn maxn) st = ((),en) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st en func /\
  local_ptrs_reserved cenv st /\ sites = abi_malformed_scratch_sites st en func ==>
  ?ip cnt ls inst.
    abi_decode_array_loop_init (Var output) pos MLOAD (Var source) hi maxn stride st =
      ((Var ip,cnt),ls) /\
    compile_abi_decode_dyn_loop (Var output) pos MLOAD (Var source) hi di stride memsz
      (Var ip) cnt ls = ((),en) /\ fn_has_code ls en func /\
    st.cs_next_var <= ls.cs_next_var /\ st.cs_next_id <= ls.cs_next_id /\
    not_fresh_at ls ip /\
    inst = mk_inst (ls.cs_next_id-2) ALLOCA [Lit 32w] [STRING #"%" (toString (ls.cs_next_var-1))] /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [ip] /\ not_local_ptr cenv scopes ip /\
    inst.inst_id IN sites /\ ls.cs_next_id-2 IN sites
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderRecursiveArrayTheory.abi_decoder_recursive_array_code >>
  disch_then (qx_choosel_then [`setup`,`loop_st`] strip_assume_tac) >>
  drule abiDecoderArrayLoopInitTheory.abi_decode_array_loop_init_trace >>
  disch_then (qx_choosel_then [`guard_st`,`header_st`,`ctop`,`ip`,`addr`] strip_assume_tac) >>
  drule abiDecoderIndexInitTheory.abi_decode_index_init_shape >> strip_tac >>
  drule_all abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abiDecoderArrayLoopInitTheory.abi_decode_array_header_shape >> strip_tac >>
  drule abiDecoderIndexInitTheory.abi_decode_index_init_trace >>
  disch_then (qx_choosel_then [`buf`,`allocation_st`] strip_assume_tac) >>
  `cs_extends st header_st /\ cs_extends header_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     metis_tac[emitHelperPropsTheory.inst_extends_trans,
               emitHelperPropsTheory.inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code header_st loop_st func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `allocation_st.cs_blocks = header_st.cs_blocks /\
   allocation_st.cs_current_bb = header_st.cs_current_bb` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> simp[]) >>
  `inst_extends header_st allocation_st /\ inst_extends allocation_st loop_st` by
    metis_tac[abiDecoderIndexInitTheory.abi_decode_alloc_buffer_inst_extends,
              emitHelperPropsTheory.inst_extends_emit_void] >>
  `cs_extends header_st allocation_st /\ cs_extends allocation_st loop_st` by
    (conj_tac >> irule cs_extends_same_block >>
     metis_tac[emitHelperPropsTheory.inst_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code header_st allocation_st func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `st.cs_next_var <= header_st.cs_next_var /\ st.cs_next_id <= loop_st.cs_next_id` by decide_tac >>
  `not_local_ptr cenv scopes (STRING #"%" (toString header_st.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists `st` >> simp[]) >>
  qexistsl [`STRING #"%" (toString header_st.cs_next_var)`,`ctop`,`loop_st`,
    `mk_inst header_st.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString header_st.cs_next_var)]`] >>
  gvs[not_fresh_at_def, abi_malformed_scratch_sites_def, venomInstTheory.mk_inst_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem malformed_finite_array_first_failure_joint:
  ^scalar_abort_lift /\ (^success_ih) /\ (^reject_ih) ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decode_bytes_widths env (ArrayT ty (Dynamic maxn)) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) = DecDynArray di stride memsz dyn maxn /\
  compile_abi_decode_to_buf (Var output) pos MLOAD (Var source) hi
    (DecDynArray di stride memsz dyn maxn) st = ((),en) /\
  (dyn \/ dec_info_needs_clamp di) /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (?av. has_type (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) av) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  type_memory_size (ArrayTV tv (Dynamic maxn)) < dimword (:256) /\
  abi_size_bound sf (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  abi_malformed_entry H0 ctx func cenv cx es st (abi_malformed_scratch_sites st en func)
    dstid live (Var source) hi pos (Var output) B L xs p d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  fresh_vars_wrt ceiling s /\ en.cs_next_var <= ceiling.cs_next_var /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (^malformed_view) (ArrayT ty (Dynamic maxn)) (DROP p xs) /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  ~ctx_has_dalloca ctx /\
  (^child_ghosts) pos output (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s G tn ==>
  (^abort) s G tn
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `sites = abi_malformed_scratch_sites st en func` >>
  qabbrev_tac `outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` >>
  `(^parent) s /\ (^root_ghosts) s G tn` by simp[] >>
  qhdtm_assum `abi_malformed_entry`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  `mem_bytes_at B L s.vs_memory = xs /\ B+L < dimword (:256)` by
    fs[abi_malformed_allocated_window_def] >>
  `LENGTH xs = L /\ L < dimword (:256)` by
    (conj_tac >- metis_tac[valueEncodingPropsTheory.LENGTH_mem_bytes_at] >> decide_tac) >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_decoder_coherent_array_iff] >>
  `di = type_to_abi_dec_info sf ce ty /\ memsz = type_memory_bytes ce ty /\
   stride = abi_member_head_size (vyper_to_abi_type env ty) /\ memsz = type_memory_size tv` by
    (qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _` mp_tac >>
     simp[NoAsms, Once type_to_abi_dec_info_def] >> strip_tac >>
     qpat_assum `abi_decoder_coherent _ _ _ ty _`
       (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
     simp[abi_decoder_header_def] >> strip_tac >> simp[]) >>
  `(^source_view) (ArrayT ty (Dynamic maxn)) p = DROP p xs` by
    simp[vyper_to_abi_type_def,is_dynamic_def] >>
  `(^malformed_view) (ArrayT ty (Dynamic maxn)) ((^source_view) (ArrayT ty (Dynamic maxn)) p)` by
    (BETA_TAC >>
     qpat_assum `(\x. _) _ _ = DROP p xs` (fn th => PURE_REWRITE_TAC[BETA_RULE th]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `(\x. _) _ _` (assume_tac o BETA_RULE) >>
  drule_all (BETA_RULE finite_reject_select) >>
  disch_then (qx_choose_then `i` (fn th => assume_tac th >> strip_assume_tac th)) >>
  `0 < maxn` by decide_tac >>
  `maxn < dimword (:256)` by
    (drule abiDecoderRecursiveArrayTheory.abi_decoder_coherent_array_capacity >> simp[]) >>
  `maxn*stride < dimword (:256) /\ abi_size_bound sf ty < dimword (:256)` by
    (drule_all abi_malformed_array_capacity >> simp[vyperASTTheory.bound_case_def]) >>
  `stride < dimword (:256)` by
    (`stride <= maxn*stride` suffices_by decide_tac >>
     simp[Once (GSYM MULT_LEFT_1), LE_MULT_RCANCEL]) >>
  drule_all abi_width_dynamic_child_inhabited >> strip_tac >>
  `32+n*memsz <= outsz /\ 32 <= outsz` by
    (`outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Abbr `outsz`] >>
     drule_all abi_valid_allocated_array_output_bounds >>
     disch_then (qspec_then `d` (assume_tac o CONJUNCT1)) >>
     qpat_assum `memsz = type_memory_size tv` (fn th => PURE_REWRITE_TAC[th]) >>
     decide_tac) >>
  `(dec_info_needs_offset di ==> 32 <= stride) /\
   (case di of DecPrimWord clamp => 32 <= stride | _ => T)` by
    (conj_tac
     >- (drule abi_decoder_array_child_offset >> simp[abiDecodeRangesTheory.abi_member_head_size_def]) >>
     Cases_on `di` >> simp[] >>
     qpat_assum `DecPrimWord _ = type_to_abi_dec_info _ _ _` (assume_tac o SYM) >>
     drule_all abi_decode_scalar_source_shape >> simp[abiDecodeRangesTheory.abi_member_head_size_def]) >>
  `sites = abi_malformed_scratch_sites st en func` by simp[Abbr `sites`] >>
  mp_tac (Q.INST [`scopes` |-> `es.scopes`] finite_reject_initializer_layout) >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choosel_then [`ip`,`cnt`,`ls`,`inst`] strip_assume_tac) >>
  qabbrev_tac `hdr = fresh_label_output "dec_dyn_hdr" ls.cs_next_label` >>
  qpat_assum `Abbrev (hdr = _)` (assume_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  rule_assum_tac BETA_RULE >>
  mp_tac (BETA_RULE finite_reject_enter_loop) >>
  (impl_tac >- rpt (first_assum ACCEPT_TAC ORELSE conj_tac)) >>
  disch_then (qx_choosel_then [`h`,`slot`,`Gh`,`th`]
    (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  drule_all finite_reject_body_cursor >>
  disch_then (qx_choosel_then [`sa`,`sb`,`se`,`iv`,`child`,`dstop`,`bb`,`hdr_bb`]
    strip_assume_tac) >>
  qabbrev_tac `child_sites = abi_malformed_scratch_sites sb se func` >>
  `child_sites = abi_malformed_scratch_sites sb se func /\ child_sites SUBSET sites` by
    (simp[Abbr `child_sites`, Abbr `sites`] >> irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `ls.cs_next_var+5 <= ceiling.cs_next_var /\ sb.cs_next_var <= ceiling.cs_next_var /\
   st.cs_next_var <= sb.cs_next_var /\ st.cs_next_var <= se.cs_next_var /\
   ls.cs_next_var <= se.cs_next_var /\ se.cs_next_var <= ceiling.cs_next_var /\
   se.cs_next_var < ceiling.cs_next_var` by decide_tac >>
  `not_fresh_at sb ip /\ ip <> STRING #"%" (toString se.cs_next_var)` by
    (conj_tac >- (irule freshWritesTheory.not_fresh_at_mono >> qexists `ls` >> simp[] >> decide_tac) >>
     qpat_assum `not_fresh_at ls ip` (mp_tac o REWRITE_RULE[not_fresh_at_def]) >>
     disch_then (qspec_then `se.cs_next_var` mp_tac) >> simp[]) >>
  mp_tac (BETA_RULE (Q.INST [`idx` |-> `Var iv`] finite_reject_loop_to_bad)) >>
  (impl_tac >-
    (rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE REFL_TAC) >>
     TRY (goal_assum (drule_at Any) >> NO_TAC) >>
     qpat_assum `hdr = fresh_label_output _ _` (fn th => PURE_REWRITE_TAC[th]) >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qspecl_then [`0`,`h`,`Gh`,`th`] mp_tac) >>
  (impl_tac >- (conj_tac >- simp[] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`u`,`Gu`,`tu`] strip_assume_tac) >>
  qexistsl [`u`,`Gu`,`tu`] >>
  conj_tac >- simp[] >> rpt gen_tac >>
  irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
  qexistsl [`Gh`,`h`,`th`] >> simp[]
QED
