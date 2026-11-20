(* Joint execution cuts for the nonbulk dynamic-array decoder. *)
Theory abiDecodeValidFiniteLoop
Ancestors abiDecoderLoopEmit[qualified,ignore_grammar] pair[qualified,ignore_grammar] abiEncoderWindowJointLeaves[qualified,ignore_grammar] abiDecodePtrMemberFrame[qualified] bodyPtrDefs[qualified,ignore_grammar] ghostPcTransportPtr[qualified,ignore_grammar]
  abiEncoderWindowJointPhases fragGasOriginPtr
  fragGasOrigin venomState venomInst venomMemDefs emitHelperProps
  abiMalformedRecursiveInterface stateRelProj allocaSiteResource allocaHistory
  ptrDiscipline finite_map pred_set words list abiCallerAllocation decoderGhostFramePtr
  decoderNavigationPtr decoderSetupStepPtr instMemFrontier wordLoadStorePtr
  venomExecSemantics memSafeRun ptrSafetyTransport bodyPtrBopScalarStep typedCopyPtr
  unitTransformDefs contextCodegenRel codegenRel abiDecoderExecution
  fragGasOriginPtrLoop abiValidAllocatedArrayInit abiValidAllocatedArrayPrefix
  abiMalformedTraversal abiMalformedNavigation abiDecoderArrayBackedge
  abiDecoderContract abiValidAllocatedContract normalizationPrefixPtr
  decoderArraySetupPtr abiDecoderDynamicLoopSetup abiDecoderStaticLoopSetup
  exprLoweringProps fragExec emitHelper compileEnv abiDecoderReentry
  bodyPtrBopScalarSeq[qualified,ignore_grammar]
  bodyPtrBopScalarOutcome[qualified,ignore_grammar]
  bodyFullBopWordSuccess[qualified,ignore_grammar]
  loweringStateRelDefs instIdxIndep calldataDynOwned exprSimAbiDecodeArrayRuntimeSetup
  entryDecoderHistoryFrame[qualified,ignore_grammar]
  abiValidAllocatedArrayLoop abiValidAllocatedArraySource abiValidAggregateHeads
  vyperTypeABI abiDecoderCoherence vyperTyping valueEncodingTyping
  abiDecoderSequenceReach abiMalformedMemberSetup
  abiDecoderOffset abiDecoderDynamic abiDecoderOffsetHead abiDecodeRanges arithmetic
  rich_list[qualified,ignore_grammar]
  bodyMemBopRestWordPath[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified]

Theorem finite_array_empty_edge_explicit[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) st [] out ==>
  gas_origin_ptr_edge (D,lo,explicit',ctx,func,PG) st [] out
Proof
  PairCases_on `st` >> PairCases_on `out` >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def] >> metis_tac[]
QED

(* An empty list of marks means no events, not merely all-false marks. *)
Theorem finite_array_empty_path_explicit[local]:
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) st [] out ==>
  gas_origin_ptr_path (D,lo,explicit',ctx,func,PG) st [] out
Proof
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !D lo explicit ctx func PG explicit'.
      cx = (D,lo,explicit,ctx,func,PG) /\ marks = [] ==>
      gas_origin_ptr_path (D,lo,explicit',ctx,func,PG) st [] out`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt strip_tac >> gvs[]
  >- simp[gas_origin_ptr_path_rules]
  >- (once_rewrite_tac[GSYM (Q.SPEC `[]` APPEND_NIL)] >>
      irule (cj 2 gas_origin_ptr_path_rules) >>
      metis_tac[finite_array_empty_edge_explicit]) >>
  irule (cj 3 gas_origin_ptr_path_rules) >>
  metis_tac[finite_array_empty_edge_explicit]
QED

(* The backedge changes one variable and one counter word. Keep the
   original encoder supplier's exact ghost update, and frame the source. *)
Theorem finite_array_backedge_window:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var ip) hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w k) /\
  eval_operand (Var ip) s = SOME (n2w slot) /\
  k < nitems /\ nitems < dimword (:256) /\
  ip <> nv /\ ptr_covers G tn ip s 32 /\
  slot+32 <= s.vs_alloca_next /\
  op_prov G (Var iv) = NONE /\ op_taint tn (Var iv) = {} /\
  alloca_inv s /\ alloca_room ctx func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s p b n /\ p <> nv /\
  (w2n b+n <= slot \/ slot+32 <= w2n b) /\
  t = jump_to hdr (mstore slot (n2w (SUC k))
    (update_var nv (n2w (SUC k)) s)) ==>
  ?G' tn'.
    abi_encode_exec_frame func s t /\
    abi_decode_ptr_window G' tn' t p b n /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. x <> nv ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    FLOOKUP G' nv = NONE /\ op_taint tn' (Var nv) = {} /\
    (!i. i < slot \/ slot+32 <= i ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  drule_all (window_array_backedge_joint |> Q.INST [`explicit` |-> `{}`]) >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  `!x. x <> nv ==> lookup_var x t = lookup_var x s` by
    (qpat_assum `t = jump_to _ _` (rewrite_tac o single) >>
     simp[jump_to_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!i. i < slot \/ slot+32 <= i ==> (i IN tn1.t_mem <=> i IN tn.t_mem)` by
    (rpt strip_tac >> simp[IN_DIFF]) >>
  `abi_decode_ptr_window G1 tn1 t p b n` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >>
     qexistsl [`G`,`s`,`tn`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!i. i < slot \/ _ ==> _` irule >> decide_tac) >>
  `!i. slot <= i /\ i < slot+32 ==> i NOTIN tn1.t_mem` by
    (rpt gen_tac >> disch_tac >> gs[IN_DIFF]) >>
  qexistsl [`G1`,`tn1`] >> simp[] >>
  rpt gen_tac >> irule finite_array_empty_path_explicit >>
  qexists_tac `{}` >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `D` mp_tac) >> gvs[]
QED

Theorem finite_array_child_backedge:
  lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv nv (Var ip) hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  u.vs_inst_idx = LENGTH prefix /\ ~u.vs_halted /\
  abi_malformed_resource_post ctx func cenv cx es next sites dstid b u /\
  abi_decoder_operand_live next (Var iv) /\
  abi_decoder_operand_live next (Var ip) /\
  eval_operand (Var iv) b = SOME (n2w k) /\
  eval_operand (Var ip) b = SOME (n2w slot) /\
  FLOOKUP b.vs_allocas counter = SOME (slot,32) /\
  FLOOKUP b.vs_allocas live = SOME (B,cap) /\ live <> counter /\
  L <= cap /\ B+L < dimword (:256) /\
  k < nitems /\ nitems < dimword (:256) /\
  ip <> nv /\ source <> nv /\ output <> nv /\
  ptr_covers G tn ip u 32 /\ ptr_covers G tn output u outsz /\
  op_prov G (Var iv) = NONE /\ op_taint tn (Var iv) = {} /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  alloca_history func u /\ abi_decode_ptr_window G tn u source (n2w B) L /\
  t = jump_to hdr (mstore slot (n2w (SUC k))
    (update_var nv (n2w (SUC k)) u)) ==>
  ?G' tn'.
    abi_encode_exec_frame func u t /\
    abi_decode_ptr_window G' tn' t source (n2w B) L /\
    ptr_covers G' tn' ip t 32 /\ ptr_covers G' tn' output t outsz /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. x <> nv ==>
      lookup_var x t = lookup_var x u /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. i < slot \/ slot+32 <= i ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (u,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_resource_post`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  drule stmt_state_rel_alloca_room >> strip_tac >>
  `FLOOKUP u.vs_allocas counter = SOME (slot,32) /\
   FLOOKUP u.vs_allocas live = SOME (B,cap)` by metis_tac[] >>
  `slot+32 <= u.vs_alloca_next` by
    metis_tac[alloca_site_registered_below] >>
  Q_TAC (fn tm => SUBGOAL_THEN tm ASSUME_TAC)
    `w2n (n2w B:bytes32) + L <= slot \/ slot+32 <= w2n (n2w B:bytes32)`
  >- (`B < dimword (:256)` by decide_tac >> simp[w2n_n2w] >>
      `B+cap <= slot \/ slot+32 <= B` by
        metis_tac[abi_caller_allocation_separate] >> decide_tac) >>
  `eval_operand (Var iv) u = SOME (n2w k) /\
   eval_operand (Var ip) u = SOME (n2w slot)` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  drule_all finite_array_backedge_window >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> conj_tac
     >- simp[jump_to_def] >>
     qexists_tac `u` >>
     simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]) >>
  `ptr_covers G1 tn1 ip t 32 /\ ptr_covers G1 tn1 output t outsz` by
    (conj_tac >> irule ptr_covers_frame >>
     qexistsl [`G`,`u`,`tn`] >> simp[]) >>
  qexistsl [`G1`,`tn1`] >> simp[] >>
  qpat_assum `!i. i < slot \/ _ ==> _` ACCEPT_TAC
QED

(* The two loop-test loads have the same read-only cursor effect. *)
Theorem finite_loop_read_word[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var q] [x]) /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\
  lookup_var q s = SOME a /\ ptr_covers G tn q s 32 /\
  w2n a + 32 <= s.vs_alloca_next /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  v = mload (w2n a) s /\
  t = ((update_var x v s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?G' tn'.
    op_taint tn' (Var x) = {} /\ op_prov G' (Var x) = NONE /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. y <> x ==> lookup_var y t = lookup_var y s /\
      FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  qabbrev_tac `raw = update_var x (mload (w2n a) s) s` >>
  qabbrev_tac `ins = mk_inst id MLOAD [Var q] [x]` >>
  qabbrev_tac `gp = step_prov PG G ins raw` >>
  qabbrev_tac `tp = step_taint ins s raw tn` >>
  `t = raw with vs_inst_idx := SUC s.vs_inst_idx` by simp[Abbr `raw`] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,gp,tp)` by
    (rpt gen_tac >> simp[Abbr `gp`, Abbr `tp`] >>
     irule straight_line_step_origin >>
     simp[Abbr `ins`, Abbr `raw`, mk_inst_def, is_terminator_def,
       inst_dload_in_section_other, eval_operand_def,
       SRULE [mk_inst_def] below_frontier_MLOAD,
       SRULE [mk_inst_def, eval_operand_def] step_MLOAD] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[SRULE [mk_inst_def] ptr_inst_ok_mload]) >>
  `op_taint tp (Var x) = {} /\ op_prov gp (Var x) = NONE /\
   raw.vs_memory = s.vs_memory /\ raw.vs_call_ctx = s.vs_call_ctx /\
   raw.vs_allocas = s.vs_allocas /\
   tp.t_mem = tn.t_mem /\ tp.t_stor = tn.t_stor /\
   tp.t_trans = tn.t_trans /\ tp.t_imm = tn.t_imm /\
   (!y. y <> x ==> lookup_var y raw = lookup_var y s /\
     FLOOKUP gp y = FLOOKUP G y /\ op_taint tp (Var y) = op_taint tn (Var y))` by
    (irule setup_mload_ghost >>
     qexistsl [`PG`,`a`,`id`,`q`] >> simp[Abbr `gp`, Abbr `tp`, Abbr `ins`, Abbr `raw`]) >>
  qexistsl [`gp`,`tp`] >> simp[] >> rpt strip_tac >>
  gvs[lookup_var_def] >> metis_tac[]
QED

(* Arithmetic in the header does not write memory. ADD can carry the
   source pointer; the two comparisons produce only scalar metadata. *)
Theorem finite_loop_test_op[local]:
  MEM opc [ADD;LT;ISZERO] /\
  (opc = ADD ==> ?left right. ops = [left;right]) /\
  EVERY (\op. op_taint tn op = {}) ops /\
  (opc <> ADD ==> EVERY (\op. op_prov G op = NONE) ops) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [x]) /\
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\
  step_inst_base (mk_inst id opc ops [x]) s = OK (update_var x v s) /\
  t = ((update_var x v s) with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?G' tn'.
    op_taint tn' (Var x) = {} /\
    FLOOKUP G' x = (if opc = ADD then first_prov G ops else NONE) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. y <> x ==> lookup_var y t = lookup_var y s /\
      FLOOKUP G' y = FLOOKUP G y /\ op_taint tn' (Var y) = op_taint tn (Var y)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  qabbrev_tac `raw = update_var x v s` >>
  qabbrev_tac `ins = mk_inst id opc ops [x]` >>
  qabbrev_tac `gp = step_prov PG G ins raw` >>
  qabbrev_tac `tp = step_taint ins s raw tn` >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn ins s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[Abbr `ins`] >>
     Cases_on `opc = ADD`
     >- (gvs[] >> irule ptr_inst_ok_copy_len_binop >> simp[]) >>
     irule bop_scalar_ptr_inst_ok >> simp[] >>
     gvs[EVERY_CONJ, Abbr `raw`]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,gp,tp)` by
    (rpt gen_tac >> simp[Abbr `gp`, Abbr `tp`] >>
     irule straight_line_step_origin >> simp[] >>
     `ins.inst_opcode = opc` by simp[Abbr `ins`] >>
     gvs[is_terminator_def, inst_mem_below_frontier_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  qexistsl [`gp`,`tp`] >> simp[] >>
  Cases_on `opc = ADD`
  >- (gvs[] >> simp[Abbr `gp`, Abbr `tp`, Abbr `ins`, Abbr `raw`,
          copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
          step_taint_def, imm_taint_def, mk_inst_def, step_prov_def,
          out_prov_def, set_prov_def, FLOOKUP_DRESTRICT] >>
      Cases_on `first_prov G [left;right]` >> simp[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  `MEM opc [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp; ADDMOD; MULMOD;
     LT; GT; SLT; SGT; EQ; ISZERO; AND; OR; XOR; NOT;
     SHL; SHR; SAR; SIGNEXTEND; BYTE; ASSIGN]` by gvs[] >>
  mp_tac (Q.INST [`u` |-> `raw`, `tmp` |-> `x`] bop_scalar_ghost_frame) >>
  simp[Abbr `gp`, Abbr `tp`, Abbr `ins`, Abbr `raw`, EVERY_CONJ,
       update_var_def, lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_UPDATE]
QED

(* Test the counter against the count word in the source allocation. The
   PC-normalized edge sequence ends at the same jump as the physical run. *)
Theorem finite_array_position_test_joint[local]:
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts id (Var ip) src MLOAD (Var source)
        first body_lbl exit_lbl|> /\
  abi_decode_position_loop_ready hdr (Var ip) src MLOAD (Var source)
    B p iw n j s /\ n < dimword (:256) /\
  src <> Var (STRING #"%" (toString first)) /\
  source <> STRING #"%" (toString first) /\
  op_taint tn src = {} /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  ptr_covers G tn ip s 32 /\ w2n iw + 32 <= s.vs_alloca_next /\
  (!a. w2n iw <= a /\ a < w2n iw + 32 ==> a NOTIN tn.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  t = jump_to (if j < n then body_lbl else exit_lbl)
    (abi_decode_position_header_state (Var source) first B p j n s) ==>
  ?G' tn'.
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 5 ==> x <> STRING #"%" (toString (first+k))) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    op_prov G' (Var (STRING #"%" (toString first))) = NONE /\
    op_taint tn' (Var (STRING #"%" (toString first))) = {} /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')
Proof
  strip_tac >>
  qhdtm_assum `abi_decode_position_loop_ready`
    (strip_assume_tac o REWRITE_RULE [abi_decode_position_loop_ready_def]) >>
  qabbrev_tac `iv = STRING #"%" (toString first)` >>
  qabbrev_tac `av = STRING #"%" (toString (first+1))` >>
  qabbrev_tac `cv = STRING #"%" (toString (first+2))` >>
  qabbrev_tac `tv = STRING #"%" (toString (first+3))` >>
  qabbrev_tac `dv = STRING #"%" (toString (first+4))` >>
  qmatch_asmsub_abbrev_tac `lookup_block hdr func.fn_blocks = SOME bb` >>
  `get_instruction bb 0 = SOME (mk_inst id MLOAD [Var ip] [iv]) /\
   get_instruction bb 1 = SOME (mk_inst (id+1) ADD [Var source;src] [av]) /\
   get_instruction bb 2 = SOME (mk_inst (id+2) MLOAD [Var av] [cv]) /\
   get_instruction bb 3 = SOME (mk_inst (id+3) LT [Var iv;Var cv] [tv]) /\
   get_instruction bb 4 = SOME (mk_inst (id+4) ISZERO [Var tv] [dv]) /\
   get_instruction bb 5 = SOME (mk_inst (id+5) JNZ [Var dv;Label exit_lbl;Label body_lbl] [])` by
    (simp[Abbr `bb`, get_instruction_def, abi_decode_position_header_insts_def,
          abi_decode_position_header_delta_def, Abbr `iv`, Abbr `av`,
          Abbr `cv`, Abbr `tv`, Abbr `dv`]) >>
  qabbrev_tac `s1 = (update_var iv (n2w j) s) with vs_inst_idx := 1` >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [Var ip] [iv]) /\
   lookup_var ip s = SOME iw /\
   s1 = (update_var iv (n2w j) s) with vs_inst_idx := SUC s.vs_inst_idx` by
    simp[Abbr `s1`, GSYM eval_operand_def] >>
  drule_at (Pat `s1 = _`) finite_loop_read_word >>
  disch_then (drule_at (Pat `lookup_var _ s = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ ip s 32`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, sym_tac >> first_assum ACCEPT_TAC])) >>
  disch_then (qx_choosel_then [`G1`,`tn1`] strip_assume_tac) >>
  qpat_x_assum `s1 = _` kall_tac >>
  `op_taint tn1 src = {} /\ eval_operand src s1 = SOME (n2w p)` by
    (Cases_on `src`
     >- (qpat_assum `eval_operand (Lit _) _ = _` mp_tac >>
         simp[NoAsms, eval_operand_def, op_taint_def])
     >- (rename1 `Var y <> Var iv` >>
         qpat_assum `!y. y <> iv ==> _` (qspec_then `y` mp_tac) >>
         qpat_assum `eval_operand (Var y) s = _` mp_tac >>
         qpat_assum `Var y <> Var iv` mp_tac >>
         simp[eval_operand_def] >> gvs[eval_operand_def]) >>
     qpat_assum `eval_operand (Label _) _ = _` mp_tac >>
     simp[NoAsms, eval_operand_def, op_taint_def, Abbr `s1`, update_var_def]) >>
  `op_taint tn1 (Var source) = {} /\ eval_operand (Var source) s1 = SOME (n2w B)` by
    ((qpat_assum `abi_decode_ptr_window _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,bodyPtrDefsTheory.ptr_covers_def]) >>
     simp[eval_operand_def] >> (gvs[eval_operand_def]))) >>
  qabbrev_tac `s2 = (update_var av (n2w (B+p)) s1) with vs_inst_idx := 2` >>
  `step_inst_base (mk_inst (id+1) ADD [Var source;src] [av]) s1 =
     OK (update_var av (n2w (B+p)) s1)` by
    (rewrite_tac[GSYM word_add_n2w] >> irule step_ADD >> simp[]) >>
  `lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME (mk_inst (id+1) ADD [Var source;src] [av]) /\
   ~s1.vs_halted /\ allocas_from lo s1 /\
   s2 = (update_var av (n2w (B+p)) s1) with vs_inst_idx := SUC s1.vs_inst_idx` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[Abbr `s1`, Abbr `s2`, update_var_def, allocas_from_def, arithmeticTheory.ADD1] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[Abbr `s1`, allocas_below_fmp_def, update_var_def]) >>
  drule_at (Pat `s2 = _`) finite_loop_test_op >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s1`)) >>
  disch_then (qspecl_then [`tn1`,`PG`,`G1`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G2`,`tn2`] strip_assume_tac) >>
  qpat_x_assum `s2 = _` kall_tac >>
  `B < dimword (:256) /\ B+p < dimword (:256)` by decide_tac >>
  `w2n (n2w B:bytes32) = B /\ w2n (n2w (B+p):bytes32) = B+p` by
    simp[w2n_n2w] >>
  `lookup_var av s2 = SOME (n2w (B+p))` by
    simp[Abbr `s2`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `ptr_covers G2 tn2 av s2 32` by
    (qpat_assum `abi_decode_ptr_window _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
                                        bodyPtrDefsTheory.ptr_covers_def]) >>
     `w = n2w B:bytes32` by metis_tac[optionTheory.SOME_11] >>
     qpat_assum `!y. y <> iv ==> _` (qspec_then `source` strip_assume_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def, first_prov_def, op_prov_def] >>
     gvs[]) >>
  `w2n (n2w (B+p):bytes32) + 32 <= s2.vs_alloca_next /\
   (!a. w2n (n2w (B+p):bytes32) <= a /\ a < w2n (n2w (B+p):bytes32) + 32 ==>
      a NOTIN tn2.t_mem)` by
    (conj_tac >- (simp[Abbr `s1`, Abbr `s2`, update_var_def] >> decide_tac) >>
     qpat_assum `abi_decode_ptr_window _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
     rpt strip_tac >>
     `B <= a /\ a < B+L` by gvs[] >>
     metis_tac[]) >>
  qabbrev_tac `s3 = (update_var cv (n2w n) s2) with vs_inst_idx := 3` >>
  `mload (w2n (n2w (B+p):bytes32)) s2 = n2w n` by
    (qpat_assum `abi_decode_load _ _ _ = _` mp_tac >>
     simp[NoAsms, Abbr `s2`, Abbr `s1`, abiDecoderContractTheory.abi_decode_load_def,
          mload_def, update_var_def]) >>
  `lookup_block s2.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s2.vs_inst_idx = SOME (mk_inst (id+2) MLOAD [Var av] [cv]) /\
   ~s2.vs_halted /\ allocas_from lo s2 /\
   s3 = (update_var cv (n2w n) s2) with vs_inst_idx := SUC s2.vs_inst_idx` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, update_var_def, allocas_from_def, arithmeticTheory.ADD1] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s2` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s1` mp_tac >>
     simp[Abbr `s2`, allocas_below_fmp_def, update_var_def]) >>
  drule_at (Pat `s3 = _`) finite_loop_read_word >>
  disch_then (drule_at (Pat `lookup_var av s2 = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ av s2 32`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s2`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G3`,`tn3`] strip_assume_tac) >>
  qpat_x_assum `s3 = _` kall_tac >>
  `iv <> av /\ iv <> cv /\ iv <> tv /\ iv <> dv` by
    simp[Abbr `iv`, Abbr `av`, Abbr `cv`, Abbr `tv`, Abbr `dv`,
         ASCIInumbersTheory.toString_11] >>
  `op_prov G3 (Var iv) = NONE /\ op_taint tn3 (Var iv) = {}` by
    (qpat_assum `!y. y <> cv ==> _` (qspec_then `iv` mp_tac) >>
     qpat_assum `!y. y <> av ==> _` (qspec_then `iv` mp_tac) >>
     qpat_assum `op_prov G1 (Var iv) = NONE`
       (assume_tac o SRULE [op_prov_def]) >>
     simp[op_prov_def]) >>
  qabbrev_tac `s4 = (update_var tv (bool_to_word (j < n)) s3) with vs_inst_idx := 4` >>
  `step_inst_base (mk_inst (id+3) LT [Var iv; Var cv] [tv]) s3 =
     OK (update_var tv (bool_to_word (j < n)) s3)` by
    (`j < dimword (:256)` by decide_tac >>
     mp_tac (Q.SPECL [`Var iv`,`Var cv`,`n2w j`,`n2w n`,`id+3`,`tv`,`s3`] step_LT) >>
     simp[Abbr `s3`, Abbr `s2`, Abbr `s1`, eval_operand_def,
          lookup_var_def, update_var_def, FLOOKUP_UPDATE, w2n_n2w]) >>
  `lookup_block s3.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s3.vs_inst_idx = SOME (mk_inst (id+3) LT [Var iv;Var cv] [tv]) /\
   ~s3.vs_halted /\ allocas_from lo s3 /\
   s4 = (update_var tv (bool_to_word (j < n)) s3) with vs_inst_idx := SUC s3.vs_inst_idx` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`, update_var_def, allocas_from_def, arithmeticTheory.ADD1] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s3` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s2` mp_tac >>
     simp[Abbr `s3`, allocas_below_fmp_def, update_var_def]) >>
  drule_at (Pat `s4 = _`) finite_loop_test_op >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s3`)) >>
  disch_then (qspecl_then [`tn3`,`PG`,`G3`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`G4`,`tn4`] strip_assume_tac) >>
  qpat_x_assum `s4 = _` kall_tac >>
  qabbrev_tac `done = bool_to_word (~(j < n))` >>
  qabbrev_tac `s5 = (update_var dv done s4) with vs_inst_idx := 5` >>
  `eval_operand (Var tv) s4 = SOME (bool_to_word (j < n))` by
    simp[Abbr `s4`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id+4) ISZERO [Var tv] [dv]) s4 =
     OK (update_var dv done s4)` by
    (drule step_ISZERO >> simp[Abbr `done`, arithmeticPropsTheory.bool_to_word_iszero]) >>
  `lookup_block s4.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s4.vs_inst_idx = SOME (mk_inst (id+4) ISZERO [Var tv] [dv]) /\
   ~s4.vs_halted /\ allocas_from lo s4 /\
   s5 = (update_var dv done s4) with vs_inst_idx := SUC s4.vs_inst_idx` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`, Abbr `s5`, update_var_def, allocas_from_def, arithmeticTheory.ADD1] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s4` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s3` mp_tac >>
     simp[Abbr `s4`, allocas_below_fmp_def, update_var_def]) >>
  drule_at (Pat `s5 = _`) finite_loop_test_op >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `get_instruction _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca ctx ==> allocas_below_fmp s4`)) >>
  disch_then (qspecl_then [`tn4`,`PG`,`G4`] mp_tac) >>
  (impl_tac >- simp[op_prov_def]) >>
  disch_then (qx_choosel_then [`G5`,`tn5`] strip_assume_tac) >>
  qpat_x_assum `s5 = _` kall_tac >>
  `lookup_block s5.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s5.vs_inst_idx = SOME (mk_inst (id+5) JNZ [Var dv;Label exit_lbl;Label body_lbl] []) /\
   ~s5.vs_halted /\ allocas_from lo s5 /\ eval_operand (Var dv) s5 = SOME done` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     simp[Abbr `s1`, Abbr `s2`, Abbr `s3`, Abbr `s4`, Abbr `s5`, update_var_def,
          allocas_from_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     first_assum ACCEPT_TAC) >>
  `t = jump_to (if done <> 0w then exit_lbl else body_lbl) s5` by
    (qpat_assum `t = _` (rewrite_tac o single) >>
     simp[Abbr `s5`, Abbr `s4`, Abbr `s3`, Abbr `s2`, Abbr `s1`, Abbr `done`,
          Abbr `iv`, Abbr `av`, Abbr `cv`, Abbr `tv`, Abbr `dv`, jump_to_def, update_var_def,
          abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          arithmeticPropsTheory.bool_to_word_neq_0w] >>
     Cases_on `j < n` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s5` by
    (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s4` mp_tac >>
     simp[Abbr `s5`, allocas_below_fmp_def, update_var_def]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s5,G5,tn5) [] (OK t,G5,tn5)` by
    (rpt gen_tac >> qpat_assum `t = jump_to (if done <> 0w then _ else _) s5` (rewrite_tac o single) >>
     irule fragGasOriginPtrLoopTheory.jnz_origin_ptr_path >>
     (metis_tac[])) >>
  `!x. lookup_var x t = lookup_var x s5` by
    (gen_tac >> qpat_assum `t = jump_to (if done <> 0w then _ else _) s5`
       (rewrite_tac o single) >> simp[jump_to_def, lookup_var_def]) >>
  `op_prov G5 (Var iv) = NONE /\ op_taint tn5 (Var iv) = {}` by
    (qpat_assum `!y. y <> dv ==> _` (qspec_then `iv` mp_tac) >>
     qpat_assum `!y. y <> tv ==> _` (qspec_then `iv` mp_tac) >>
     qpat_assum `op_prov G3 (Var iv) = NONE`
       (assume_tac o SRULE [op_prov_def]) >>
     simp[op_prov_def]) >>
  qexistsl [`G5`,`tn5`] >>
  simp[Abbr `iv`, IgnAsm `t = _`, IgnAsm `lookup_var _ t = _`] >>
  conj_tac
  >- (qx_gen_tac `x` >> disch_tac >>
      `x <> STRING #"%" (toString first) /\ x <> av /\ x <> cv /\ x <> tv /\ x <> dv` by
        (qpat_assum `!k. k < 5 ==> _` (fn th =>
           map_every (fn q => assume_tac (SRULE [] (Q.SPEC q th)))
             [`0`,`1`,`2`,`3`,`4`]) >>
         simp[Abbr `av`, Abbr `cv`, Abbr `tv`, Abbr `dv`]) >>
      qpat_assum `!y. y <> dv ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!y. y <> tv ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!y. y <> cv ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!y. y <> av ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!y. y <> STRING #"%" (toString first) ==> _` (qspec_then `x` mp_tac) >>
      simp[IgnAsm `t = _`]) >>
  rpt gen_tac >>
  map_every (fn edge =>
    qpat_assum edge (qspecl_then [`D`,`explicit`]
      (mp_then Any irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans)))
    [`!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`,
     `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) [] _`,
     `!D explicit. gas_origin_ptr_path _ (s2,G2,tn2) [] _`,
     `!D explicit. gas_origin_ptr_path _ (s3,G3,tn3) [] _`,
     `!D explicit. gas_origin_ptr_path _ (s4,G4,tn4) [] _`] >>
  first_assum MATCH_ACCEPT_TAC
QED

(* Read-only loop header, shared by the recursive and equal-count branches.
   Both simulations use the displayed jump endpoint. *)
Theorem finite_array_header_from_inv[local]:
  abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
    sites dstid live (Var source) hi src (Var output) B L xs p d outsz
    (Var ip) slot inst q hdr tv vs origin j s /\ j <= LENGTH vs /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid (Var ip) src MLOAD (Var source)
        first body_lbl exit_lbl|> /\
  start.cs_next_var <= first /\ first+5 <= ceiling.cs_next_var /\
  abi_decoder_operand_live first src /\
  abi_decoder_operand_live first (Var source) /\
  abi_decoder_operand_live first (Var output) /\
  abi_decoder_operand_live first (Var ip) /\
  LENGTH vs < dimword (:256) /\ LENGTH vs = abi_head_word (DROP p xs) /\ p+32 <= L /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ op_taint tn src = {} /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\ ptr_covers G tn ip s 32 /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  h = jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_position_header_state (Var source) first B p j (LENGTH vs) s) ==>
  ?G' tn'.
    abi_decode_sim ctx func s h /\
    abi_malformed_resource_post ctx func cenv cx es start.cs_next_var sites dstid s h /\
    abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
      sites dstid d outsz origin h /\
    fresh_vars_wrt ceiling h /\ ~h.vs_halted /\
    h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ h.vs_memory = s.vs_memory /\
    h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
    h.vs_accounts = s.vs_accounts /\ h.vs_transient = s.vs_transient /\
    h.vs_call_ctx = s.vs_call_ctx /\ h.vs_immutables = s.vs_immutables /\
    alloca_history func h /\ allocas_from lo h /\ lo <= h.vs_alloca_next /\
    abi_decode_ptr_window G' tn' h source (n2w B) L /\
    ptr_covers G' tn' output h outsz /\ ptr_covers G' tn' ip h 32 /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live first (Var x) ==>
      lookup_var x h = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    op_prov G' (Var (STRING #"%" (toString first))) = NONE /\
    op_taint tn' (Var (STRING #"%" (toString first))) = {} /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK h,G',tn')
Proof
  strip_tac >>
  qhdtm_assum `abi_valid_allocated_array_inv`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_array_inv_def]) >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w (LENGTH vs)` by
    (`mem_bytes_at B L (abi_decode_source MLOAD s) = xs` by
       simp[abi_decode_source_def] >>
     drule_all abi_checked_offset_load >> simp[]) >>
  `abi_decode_position_loop_ready hdr (Var ip) src MLOAD (Var source)
     B p (n2w slot) (LENGTH vs) j s` by
    simp[abi_decode_position_loop_ready_def, w2n_n2w] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `B+L <= s.vs_alloca_next /\ w2n (n2w slot:bytes32)+32 <= s.vs_alloca_next` by
    (`B+cap <= s.vs_alloca_next /\ slot+32 <= s.vs_alloca_next` by
       metis_tac[alloca_site_registered_below] >>
     simp[w2n_n2w] >> decide_tac) >>
  `!a. w2n (n2w slot:bytes32) <= a /\ a < w2n (n2w slot:bytes32)+32 ==>
       a NOTIN tn.t_mem` by simp[w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first)) /\
   Var source <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output, arithmeticTheory.LESS_EQ_REFL] >>
  `source <> STRING #"%" (toString first)` by gvs[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  drule_all finite_array_position_test_joint >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_sim ctx func s h` by
    (qpat_assum `h = jump_to _ _` (rewrite_tac o single) >>
     drule_all abi_malformed_position_header_sim >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es first sites dstid s h /\
   fresh_vars_wrt ceiling h` by
    (qpat_assum `h = jump_to _ _` (rewrite_tac o single) >>
     irule abi_malformed_header_resource >>
     simp[abi_decode_position_header_delta_def] >>
     conj_tac >- (qexists_tac `start` >> simp[]) >>
     qexists_tac `H` >> simp[]) >>
  `~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
   h.vs_inst_idx = 0 /\ h.vs_memory = s.vs_memory /\
   h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
   h.vs_accounts = s.vs_accounts /\ h.vs_transient = s.vs_transient /\
   h.vs_call_ctx = s.vs_call_ctx /\ h.vs_immutables = s.vs_immutables` by
    (qpat_assum `h = jump_to _ _` (rewrite_tac o single) >>
     simp[abi_decode_position_header_state_def, abi_decode_position_header_delta_def,
          jump_to_def, update_var_def]) >>
  `alloca_history func h /\ allocas_from lo h` by
    (conj_tac >- (irule alloca_history_jump >> simp[] >>
                  qexists_tac `s` >> simp[]) >>
     simp[allocas_from_def] >> fs[allocas_from_def]) >>
  `abi_valid_allocated_effect ctx func cenv cx es first sites dstid d outsz s h` by
    simp[abi_valid_allocated_effect_def, abi_valid_allocated_frame_def] >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz origin h` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `s` >>
     simp[] >> metis_tac[abi_valid_allocated_effect_weaken]) >>
  `!x. abi_decoder_operand_live first (Var x) ==>
     lookup_var x h = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. (!k. k < 5 ==> _) ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- (rpt strip_tac >>
       `Var x <> Var (STRING #"%" (toString (first+k)))` by
         metis_tac[abi_decoder_live_excludes_output, arithmeticTheory.LESS_EQ_ADD] >> gvs[])) >>
     simp[IgnAsm `h = jump_to _ _`]) >>
  `abi_decode_ptr_window G1 tn1 h source (n2w B) L` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >> qexistsl [`G`,`s`,`tn`] >>
     simp[IgnAsm `h = jump_to _ _`]) >>
  `ptr_covers G1 tn1 output h outsz /\ ptr_covers G1 tn1 ip h 32` by
    (conj_tac >> irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >>
     simp[IgnAsm `h = jump_to _ _`]) >>
  qexistsl [`G1`,`tn1`] >> simp[IgnAsm `h = jump_to _ _`] >>
  irule abi_malformed_resource_weaken >>
  qhdtm_assum `abi_malformed_resource_post` (irule_at Any) >> simp[]
QED

(* At the equal count the header jumps straight to the exit. Since it
   writes no memory, the robust initialized prefix is the whole array. *)
Theorem finite_array_exit_from_inv[local]:
  abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
    sites dstid live (Var source) hi src (Var output) B L xs p d outsz
    (Var ip) slot inst q hdr tv vs origin (LENGTH vs) s /\
  lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_position_header_insts hid (Var ip) src MLOAD (Var source)
        first body_lbl exit_lbl|> /\
  start.cs_next_var <= first /\ first+5 <= ceiling.cs_next_var /\
  abi_decoder_operand_live first src /\
  abi_decoder_operand_live first (Var source) /\
  abi_decoder_operand_live first (Var output) /\
  abi_decoder_operand_live first (Var ip) /\
  LENGTH vs < dimword (:256) /\ LENGTH vs = abi_head_word (DROP p xs) /\ p+32 <= L /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ op_taint tn src = {} /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\ ptr_covers G tn ip s 32 /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     mem_word_at d m = n2w (LENGTH vs)) /\
  (!k m. k < LENGTH vs /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) m) ==>
  ?h G' tn'.
    abi_decode_sim ctx func s h /\
    abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
      sites dstid d outsz origin h /\
    fresh_vars_wrt ceiling h /\ ~h.vs_halted /\
    h.vs_current_bb = exit_lbl /\ h.vs_inst_idx = 0 /\
    h.vs_memory = s.vs_memory /\ h.vs_allocas = s.vs_allocas /\
    h.vs_alloca_next = s.vs_alloca_next /\
    h.vs_accounts = s.vs_accounts /\ h.vs_transient = s.vs_transient /\
    h.vs_call_ctx = s.vs_call_ctx /\ h.vs_immutables = s.vs_immutables /\
    alloca_history func h /\ allocas_from lo h /\ lo <= h.vs_alloca_next /\
    abi_decode_ptr_window G' tn' h source (n2w B) L /\
    ptr_covers G' tn' output h outsz /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live first (Var x) ==>
      lookup_var x h = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!m. mem_agree_outside tn'.t_mem h.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d m) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK h,G',tn')
Proof
  strip_tac >>
  qabbrev_tac `h = jump_to exit_lbl
      (abi_decode_position_header_state (Var source) first B p
        (LENGTH vs) (LENGTH vs) s)` >>
  `LENGTH vs <= LENGTH vs /\
   h = jump_to (if LENGTH vs < LENGTH vs then body_lbl else exit_lbl)
      (abi_decode_position_header_state (Var source) first B p
        (LENGTH vs) (LENGTH vs) s)` by simp[Abbr `h`] >>
  drule_all (finite_array_header_from_inv |> Q.INST [`j` |-> `LENGTH (vs:value list)`]) >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  qexistsl [`h`,`G1`,`tn1`] >> simp[IgnAsm `h = jump_to _ _`] >>
  metis_tac[robust_dynarray_assemble]
QED

(* The MLOAD and scalar address arithmetic are common to both element
   layouts. The raw endpoint is supplied by the caller's successful run. *)
Theorem finite_array_setup_prefix_origin[local]:
  emit_op MLOAD [Var ip] st = (idx,c0) /\
  emit_op ADD [src;Lit 32w] c0 = (data,c1) /\
  emit_op MUL [idx;Lit (n2w stride)] c1 = (off,c2) /\
  emit_op ADD [data;off] c2 = (head,c3) /\
  run_inst_seq (emitted_insts st c3) s = OK t /\
  fn_has_code st c3 func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var ip s = SOME w /\ ptr_covers G tn ip s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  eval_operand src s = SOME p /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  ?G' tn'.
    eval_operand idx t = SOME (mload (w2n w) s) /\
    eval_operand data t = SOME (p + 32w) /\
    eval_operand head t = SOME (p + 32w + mload (w2n w) s * n2w stride) /\
    op_prov G' idx = NONE /\ op_taint tn' idx = {} /\
    op_prov G' data = NONE /\ op_taint tn' data = {} /\
    op_prov G' head = NONE /\ op_taint tn' head = {} /\
    (!x. idx = Var x ==> not_fresh_at c3 x) /\
    (!x. data = Var x ==> not_fresh_at c3 x) /\
    (!x. head = Var x ==> not_fresh_at c3 x) /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH c3.cs_current_insts),G',tn')
Proof
  strip_tac >>
  `inst_extends st c0 /\ same_blocks st c0 /\ st.cs_next_var <= c0.cs_next_var /\
   LENGTH (emitted_insts st c0) = 1` by
    metis_tac[inst_extends_emit_op, emit_op_same_blocks, ci_mono_emit_op,
              ci_mono_def, pairTheory.SND, emit_op_length] >>
  `inst_extends c0 c3 /\ same_blocks c0 c3 /\ c0.cs_next_var <= c3.cs_next_var /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c0 c3)` by
    metis_tac[scaled_address_prefix_structure] >>
  `emitted_insts st c3 = emitted_insts st c0 ++ emitted_insts c0 c3` by
    fs[inst_extends_def, emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts st c3) s = OK t` mp_tac >>
  simp[] >> disch_then (strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts st c0) s = OK r0` >>
  `cs_extends st c0 /\ cs_extends c0 c3` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`G0`,`tn0`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  `r0 = s with vs_vars := r0.vs_vars /\ eval_operand idx r0 = SOME (mload (w2n w) s)` by
    (qpat_assum `emit_op MLOAD _ st = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
         eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `!x. idx = Var x ==> not_fresh_at c0 x` by
    (qpat_assum `emit_op MLOAD _ st = _` (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `idx` >> simp[calldata_operand_live_not_fresh]) >>
  `eval_operand src r0 = SOME p /\ op_taint tn0 src = {} /\ op_prov G0 src = NONE` by
    (`r0.vs_labels = s.vs_labels` by
       (qpat_assum `r0 = s with vs_vars := _`
          (mp_tac o AP_TERM ``\s. s.vs_labels``) >> simp[]) >>
     drule_all old_operand_ghost_frame >> simp[]) >>
  `!x. not_fresh_at st x ==> not_fresh_at c0 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. not_fresh_at c0 x ==> not_fresh_at c3 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qabbrev_tac `s0 = r0 with vs_inst_idx := LENGTH c0.cs_current_insts` >>
  `run_inst_seq (emitted_insts c0 c3) s0 = OK (t with vs_inst_idx := s0.vs_inst_idx)` by
    simp[Abbr `s0`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `eval_operand src s0 = SOME p /\ eval_operand idx s0 = SOME (mload (w2n w) s) /\
   (!x. src = Var x ==> not_fresh_at c0 x)` by
    (conj_tac >- simp[Abbr `s0`] >> conj_tac >- simp[Abbr `s0`] >> metis_tac[]) >>
  drule_all clean_scaled_source_prefix_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`G3`,`tn3`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  suspend "frames_and_path"
QED

Resume finite_array_setup_prefix_origin[frames_and_path]:
  `inst_extends c0 c1 /\ inst_extends c1 c2 /\ inst_extends c2 c3` by
    metis_tac[inst_extends_emit_op] >>
  `emitted_insts c0 c3 =
     emitted_insts c0 c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    fs[inst_extends_def, emitted_insts_append, APPEND_ASSOC] >>
  `t = r0 with vs_vars := t.vs_vars` by
    (irule (cj 1 abi_malformed_setup_sequence_frame) >>
     qexistsl [`\x:string. F`, `emitted_insts c0 c3`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `emit_op ADD _ c0 = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MUL _ c1 = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op ADD _ c2 = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_assum `t = r0 with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `r0 = s with vs_vars := _`
       (mp_tac o AP_TERM ``\r. r with vs_vars := t.vs_vars``) >> simp[]) >>
  `!x. not_fresh_at c0 x ==>
      lookup_var x t = lookup_var x r0 /\ FLOOKUP G3 x = FLOOKUP G0 x /\
      op_taint tn3 (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `!x. not_fresh_at c0 x ==> lookup_var x (_ with vs_inst_idx := _) = _ /\ _`
       mp_tac >> simp[NoAsms, Abbr `s0`, blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G3 x = FLOOKUP G x /\
      op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (ntac 2 strip_tac >>
     map_every (fn a => qpat_assum a (qspec_then `x` mp_tac))
       [`!x. not_fresh_at c0 x ==> lookup_var x t = _ /\ _`,
        `!x. not_fresh_at st x ==> lookup_var x r0 = _ /\ _`] >> simp[]) >>
  `eval_operand idx t = SOME (mload (w2n w) s) /\
   op_prov G3 idx = NONE /\ op_taint tn3 idx = {}` by
    (`t.vs_labels = r0.vs_labels` by fs[Abbr `s0`] >>
     qpat_assum `!x. idx = Var x ==> not_fresh_at c0 x`
       (mp_then Any (drule_all_then mp_tac) old_operand_ghost_frame) >> simp[]) >>
  qpat_assum `eval_operand data (t with vs_inst_idx := _) = _`
    (assume_tac o REWRITE_RULE [eval_op_inst_idx]) >>
  qpat_assum `eval_operand head (t with vs_inst_idx := _) = _`
    (assume_tac o REWRITE_RULE [eval_op_inst_idx]) >>
  qexistsl [`G3`,`tn3`] >>
  simp[] >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s0,G0,tn0)` by
    (first_assum irule >> simp[]) >>
  `allocas_from lo s0 /\ ~s0.vs_halted /\ s0.vs_current_bb = c0.cs_current_bb /\
   s0.vs_inst_idx = LENGTH c0.cs_current_insts` by
    (simp[Abbr `s0`] >>
     qpat_assum `r0 = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def, same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (simp[Abbr `s0`] >>
     qpat_assum `r0 = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) []
     (OK (t with vs_inst_idx := LENGTH c3.cs_current_insts),G3,tn3)` by
    (qpat_assum `!D lower explicit ctx func. _ ==> gas_origin_ptr_path _ (s0,G0,tn0) [] _`
       (irule o SRULE []) >> simp[]) >>
  irule gas_origin_ptr_path_trans >> goal_assum drule >> simp[]
QED

Finalise finite_array_setup_prefix_origin

(* The setup head is shared by both the static and offset layouts. *)
Theorem finite_array_setup_head_origin[local]:
  abi_decode_array_head_setup (Var ip) src stride st = ((idx,data,head),ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  fn_has_code st ready func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var ip s = SOME w /\ ptr_covers G tn ip s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  eval_operand src s = SOME p /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) ==>
  ?G' tn'.
    eval_operand idx t = SOME (mload (w2n w) s) /\
    eval_operand data t = SOME (p + 32w) /\
    eval_operand head t = SOME (p + 32w + mload (w2n w) s * n2w stride) /\
    op_prov G' idx = NONE /\ op_taint tn' idx = {} /\
    op_prov G' data = NONE /\ op_taint tn' data = {} /\
    op_prov G' head = NONE /\ op_taint tn' head = {} /\
    (!x. idx = Var x ==> not_fresh_at ready x) /\
    (!x. data = Var x ==> not_fresh_at ready x) /\
    (!x. head = Var x ==> not_fresh_at ready x) /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')
Proof
  simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
       comp_bind_def, comp_return_def] >>
  Cases_on `emit_op MLOAD [Var ip] st` >> simp[] >>
  rename1 `emit_op MLOAD [Var ip] st = (i,c0)` >>
  Cases_on `emit_op ADD [src; Lit 32w] c0` >> simp[] >>
  rename1 `emit_op ADD [src; Lit 32w] c0 = (d,c1)` >>
  Cases_on `emit_op MUL [i; Lit (n2w stride)] c1` >> simp[] >>
  rename1 `emit_op MUL [i; Lit (n2w stride)] c1 = (o',c2)` >>
  Cases_on `emit_op ADD [d; o'] c2` >> simp[] >> strip_tac >> gvs[] >>
  irule finite_array_setup_prefix_origin >> goal_assum (drule_at Any) >> simp[]
  >> (metis_tac[])
QED

Theorem finite_array_head_code[local]:
  abi_decode_array_head_setup ip src stride st = (ops,ready) ==>
  inst_extends st ready /\ same_blocks st ready /\ st.cs_next_var <= ready.cs_next_var
Proof
  simp[abi_decode_array_head_setup_def, abi_decode_indexed_coordinates_def,
       comp_bind_def, comp_return_def] >>
  Cases_on `emit_op MLOAD [ip] st` >> simp[] >>
  rename1 `emit_op MLOAD [ip] st = (i,c0)` >>
  Cases_on `emit_op ADD [src; Lit 32w] c0` >> simp[] >>
  rename1 `emit_op ADD [src; Lit 32w] c0 = (d,c1)` >>
  Cases_on `emit_op MUL [i; Lit (n2w stride)] c1` >> simp[] >>
  rename1 `emit_op MUL [i; Lit (n2w stride)] c1 = (off,c2)` >>
  Cases_on `emit_op ADD [d; off] c2` >> simp[] >> strip_tac >> gvs[] >>
  `st.cs_next_var <= c0.cs_next_var /\ c0.cs_next_var <= c1.cs_next_var /\
   c1.cs_next_var <= c2.cs_next_var /\ c2.cs_next_var <= r.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `inst_extends st c0 /\ inst_extends c0 c1 /\ inst_extends c1 c2 /\ inst_extends c2 r` by
    metis_tac[inst_extends_emit_op] >>
  `same_blocks st c0 /\ same_blocks c0 c1 /\ same_blocks c1 c2 /\ same_blocks c2 r` by
    metis_tac[emit_op_same_blocks] >>
  simp[] >> conj_tac
  >- (irule inst_extends_trans >> qexists_tac `c2` >> simp[] >>
      irule inst_extends_trans >> qexists_tac `c1` >> simp[] >>
      irule inst_extends_trans >> qexists_tac `c0` >> simp[]) >>
  irule same_blocks_trans >> qexists_tac `c2` >> simp[] >>
  irule same_blocks_trans >> qexists_tac `c1` >> simp[] >>
  irule same_blocks_trans >> qexists_tac `c0` >> simp[]
QED

(* The child destination is certified at the endpoint of the supplied setup
   run; only the PC used for the second phase changes at the cut. *)
Theorem finite_array_static_setup_origin[local]:
  abi_decode_array_element_setup (Var ip) src (Var output) MLOAD base_op hi di
    abi_sz mem_sz st = (ops,ready) /\ ~dec_info_needs_offset di /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  fn_has_code st ready func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var ip s = SOME w /\ ptr_covers G tn ip s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = n2w j /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  eval_operand src s = SOME p /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  lookup_var output s = SOME (n2w d) /\ ptr_covers G tn output s outsz /\
  not_fresh_at st output /\ 32+j*mem_sz+mem_sz <= outsz /\
  d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256) ==>
  ?G' tn' child.
    SND (SND ops) = Var child /\ ptr_covers G' tn' child t mem_sz /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')
Proof
  strip_tac >> drule_all abi_array_static_element_setup_split >>
  disch_then (qx_choosel_then [`hops`,`mid`] strip_assume_tac) >>
  PairCases_on `hops` >> gvs[] >>
  drule finite_array_head_code >> strip_tac >>
  drule indexed_destination_structure >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid ready` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  `fn_has_code st mid func /\ fn_has_code mid ready func` by
    metis_tac[fn_has_code_split] >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    fs[inst_extends_def, emitted_insts_append] >>
  `run_inst_seq (emitted_insts st mid ++ emitted_insts mid ready) s = OK t` by
    (qpat_x_assum `emitted_insts st ready = _` (rewrite_tac o single o SYM) >> simp[]) >>
  drule run_inst_seq_append_ok >> disch_then (qx_choose_then `r0` strip_assume_tac) >>
  drule_all finite_array_setup_head_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G0`,`tn0`] strip_assume_tac)) >>
  `lookup_var output r0 = SOME (n2w d) /\ ptr_covers G0 tn0 output r0 outsz` by
    (conj_asm1_tac >- metis_tac[] >>
     irule ptr_covers_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qabbrev_tac `s0 = r0 with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `run_inst_seq (emitted_insts mid ready) s0 = OK (t with vs_inst_idx := s0.vs_inst_idx)` by
    simp[Abbr `s0`, run_inst_seq_inst_idx, exec_result_map_def] >>
  `lookup_var output s0 = SOME (n2w d) /\ ptr_covers G0 tn0 output s0 outsz /\
   eval_operand (FST ops) s0 = SOME (n2w j) /\ not_fresh_at mid output` by
    (simp[Abbr `s0`, blockPrefixEquivTheory.lookup_var_set_inst_idx,
          ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `32+j*mem_sz+mem_sz <= outsz /\ d+32+j*mem_sz < dimword (:256)` by simp[] >>
  drule_all indexed_destination_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`H`,`cx`,`ctx`,`PG`,`R`]
    (qx_choosel_then [`G1`,`tn1`,`child`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  `!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r0 /\
    FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x (_ with vs_inst_idx := _) = _ /\ _`
       mp_tac >> simp[NoAsms, Abbr `s0`, blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `t.vs_labels = r0.vs_labels` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     `t.vs_labels = s.vs_labels` by
       (qpat_assum `t = s with vs_vars := _` (mp_tac o AP_TERM ``\r. r.vs_labels``) >> simp[NoAsms]) >>
     qpat_assum `r0 = s with vs_vars := _` (mp_tac o AP_TERM ``\r. r.vs_labels``) >> simp[]) >>
  `op_prov G1 (FST ops) = NONE /\ op_taint tn1 (FST ops) = {} /\
   op_prov G1 (FST (SND ops)) = NONE /\ op_taint tn1 (FST (SND ops)) = {}` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r0 /\ _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (fn th =>
       map_every (fn opnd => qspec_then opnd mp_tac th) [`FST ops`,`FST (SND ops)`]) >> simp[]) >>
  `ptr_covers G1 tn1 child t mem_sz` by
    ((qpat_assum `ptr_covers G1 tn1 child (t with <|vs_inst_idx := _; vs_inst_idx := _|>) mem_sz`
       mp_tac >> simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >> (gvs[ghostPcTransportPtrTheory.ptr_covers_inst_idx]))) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (ntac 2 strip_tac >> `not_fresh_at mid x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     map_every (fn a => qpat_assum a (qspec_then `x` mp_tac))
       [`!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r0 /\ _`,
        `!x. not_fresh_at st x ==> lookup_var x r0 = lookup_var x s /\ _`] >> simp[]) >>
  qexistsl [`G1`,`tn1`,`child`] >> simp[] >>
  rpt gen_tac >>
  `allocas_from lo (r0 with vs_inst_idx := LENGTH mid.cs_current_insts) /\
   ~r0.vs_halted /\ r0.vs_current_bb = mid.cs_current_bb` by
    (qpat_assum `r0 = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def, same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp (r0 with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (qpat_assum `r0 = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (r0 with vs_inst_idx := LENGTH mid.cs_current_insts,G0,tn0) []
     (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G1,tn1)` by
    (qpat_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ (_,G0,tn0) [] _`
       (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
     simp[Abbr `s0`] >> gvs[]) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  simp[Abbr `s0`]
QED

(* The offset table is itself part of the registered source window. An
   actual successful address ADD selects a clean word of that table. *)
Theorem finite_array_offset_address_origin[local]:
  emit_op ADD [Var source; pos] sa = (addr,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G' tn' q.
    addr = Var q /\ abi_decode_ptr_window G' tn' t q (n2w (B+p)) 32 /\
    t = s with vs_vars := t.vs_vars /\
    w2n (n2w (B+p):bytes32) + 32 <= t.vs_alloca_next /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')
Proof
  strip_tac >>
  qhdtm_assum `abi_decode_ptr_window`
    (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
  `w2n (n2w B:bytes32) = B /\ w2n (n2w (B+p):bytes32) = B+p` by
    (`B < dimword (:256) /\ B+p < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
  `p+32 <= L /\ w2n (n2w B:bytes32)+p < dimword (:256)` by simp[] >>
  drule_all emit_ptr_offset_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`G1`,`tn1`,`q`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  `t = s with vs_vars := t.vs_vars` by
    (irule (cj 1 abi_malformed_setup_sequence_frame) >>
     qexistsl [`\x:string. F`,`emitted_insts sa sb`] >> simp[] >>
     qpat_assum `emit_op ADD _ sa = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def]) >>
  `B+(p+32) <= t.vs_alloca_next` by
    (qpat_assum `t = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[] >> decide_tac) >>
  `abi_decode_ptr_window G1 tn1 t q (n2w (B+p)) 32` by
    gvs[abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def] >>
  qexistsl [`G1`,`tn1`,`q`] >> simp[] >>
  rpt gen_tac >>
  qpat_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ _ [] _`
    (irule o SRULE []) >> simp[]
QED

Theorem finite_array_offset_load_origin[local]:
  emit_op ADD [Var source; pos] sa = (Var q,sb) /\
  emit_op MLOAD [Var q] sb = (off,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  fn_has_code sa sc func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G' tn'.
    eval_operand off t = SOME (mload (B+p) s) /\
    op_prov G' off = NONE /\ op_taint tn' off = {} /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')
Proof
  strip_tac >>
  `inst_extends sa sb /\ inst_extends sb sc /\ same_blocks sa sb /\ same_blocks sb sc /\
   sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[inst_extends_emit_op, emit_op_same_blocks, ci_mono_emit_op, ci_mono_def,
              pairTheory.SND] >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    fs[inst_extends_def, emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK t` mp_tac >>
  simp[] >> disch_then (qx_choose_then `r` strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  drule_all finite_array_offset_address_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`,`q1`] strip_assume_tac)) >>
  qpat_x_assum `Var q = Var q1` (SUBST_ALL_TAC o SYM o SRULE []) >>
  qabbrev_tac `s1 = r with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `run_inst_seq (emitted_insts sb sc) s1 = OK (t with vs_inst_idx := s1.vs_inst_idx)` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
       (qpat_assum `emit_op MLOAD _ sb = _`
          (mp_then Any (strip_assume_tac o CONJUNCT1) emitted_insts_emit_op) >>
        pop_assum SUBST1_TAC >> simp[NoAsms, mk_inst_def, is_terminator_def]) >>
     simp[IgnAsm `r = s with vs_vars := r.vs_vars`, Abbr `s1`,
          run_inst_seq_inst_idx, exec_result_map_def]) >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\ s1.vs_current_bb = sb.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sb.cs_current_insts /\
   w2n (n2w (B+p):bytes32)+32 <= s1.vs_alloca_next` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def, same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `abi_decode_ptr_window G1 tn1 s1 q (n2w (B+p)) 32` by
    (qpat_assum `abi_decode_ptr_window G1 tn1 r _ _ _` mp_tac >>
     simp[NoAsms, Abbr `s1`, abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
          blockPrefixEquivTheory.lookup_var_set_inst_idx, ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  qpat_assum `abi_decode_ptr_window _ _ s1 _ _ _`
    (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`G2`,`tn2`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  suspend "load_endpoint"
QED

Resume finite_array_offset_load_origin[load_endpoint]:
  qpat_assum `emit_op MLOAD _ sb = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `t = r with vs_vars := t.vs_vars /\ eval_operand off t = SOME (mload (B+p) s)` by
    (`w2n (n2w (B+p):bytes32) = B+p` by
       (`B+p < dimword (:256)` by decide_tac >> simp[w2n_n2w]) >>
     qpat_x_assum `run_inst_seq (emitted_insts sb sc) r = OK t` mp_tac >>
     qpat_assum `abi_decode_ptr_window G1 tn1 r _ _ _`
       (strip_assume_tac o REWRITE_RULE [abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def]) >>
     simp[IgnAsm `r = s with vs_vars := r.vs_vars`, run_inst_seq_def,
          step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def, eval_operand_def] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp[IgnAsm `r = s with vs_vars := r.vs_vars`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     simp[NoAsms, mload_def]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_assum `t = r with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `r = s with vs_vars := _`
       (mp_tac o AP_TERM ``\r. r with vs_vars := t.vs_vars``) >> simp[]) >>
  qexistsl [`G2`,`tn2`] >> simp[] >>
  conj_tac
  >- (ntac 2 strip_tac >>
      `not_fresh_at sb x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sb x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
      simp[NoAsms, Abbr `s1`, blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
      metis_tac[]) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  qpat_x_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ (s1,G1,tn1) [] _`
    (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
  simp[Abbr `s1`]
QED

Finalise finite_array_offset_load_origin

(* Specialize the scalar endpoint to ADD, also recording the ordinary
   result and the stronger variables-only physical frame needed at a cut. *)
Theorem finite_array_scalar_add_origin[local]:
  emit_op ADD [left;right] sa = (out,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_prov G left = NONE /\ op_prov G right = NONE /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?G' tn'.
    eval_operand out t = SOME (a + b) /\ t = s with vs_vars := t.vs_vars /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')
Proof
  strip_tac >>
  drule_all (SRULE [] (Q.SPEC `ADD` emit_scalar_binop_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ctx`,`PG`,`ARB`]
    (qx_choosel_then [`H`,`u`] strip_assume_tac)) >>
  `eval_operand out t = SOME (a+b) /\ t = s with vs_vars := t.vs_vars` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
         eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qexistsl [`H`,`u`] >> simp[] >> rpt gen_tac >>
  qpat_x_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >> simp[]
QED

(* The unguarded memory offset calculation, on the actual three-op run. *)
Theorem finite_array_pointer_sentinel_origin[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) pos data (Lit 0w) sz sa = (out,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  fn_has_code sa sc func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  eval_operand data s = SOME a /\ op_prov G data = NONE /\ op_taint tn data = {} /\
  (!x. data = Var x ==> not_fresh_at sa x) /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G' tn'.
    eval_operand out t = SOME (a + mload (B+p) s) /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')
Proof
  simp[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_op ADD [Var source; pos] sa` >> simp[] >>
  rename1 `emit_op ADD [Var source; pos] sa = (addr,sb)` >>
  Cases_on `emit_op MLOAD [addr] sb` >> simp[] >>
  rename1 `emit_op MLOAD [addr] sb = (off,sd)` >>
  Cases_on `emit_op ADD [data; off] sd` >> simp[] >> strip_tac >>
  `?j. addr = Var j` by metis_tac[emitted_insts_emit_op] >> gvs[] >>
  rename1 `emit_op ADD [data; off] sd = (out,sc)` >>
  `inst_extends sa sd /\ inst_extends sd sc /\ same_blocks sa sd /\ same_blocks sd sc /\
   sa.cs_next_var <= sd.cs_next_var` by
    (`inst_extends sa sb /\ inst_extends sb sd /\ same_blocks sa sb /\ same_blocks sb sd /\
      sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sd.cs_next_var` by
       metis_tac[inst_extends_emit_op, emit_op_same_blocks, ci_mono_emit_op, ci_mono_def,
                 pairTheory.SND] >>
     metis_tac[inst_extends_trans,same_blocks_trans,inst_extends_emit_op,emit_op_same_blocks,
               arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends sa sd /\ cs_extends sd sc` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sd ++ emitted_insts sd sc` by
    fs[inst_extends_def, emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK t` mp_tac >>
  simp[] >> disch_then (qx_choose_then `r` strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  drule_all finite_array_offset_load_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  suspend "add_endpoint"
QED

Resume finite_array_pointer_sentinel_origin[add_endpoint]:
  `eval_operand data r = SOME a /\ op_prov G1 data = NONE /\ op_taint tn1 data = {}` by
    (`r.vs_labels = s.vs_labels` by
       (qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
     drule_all old_operand_ghost_frame >> simp[]) >>
  qabbrev_tac `s1 = r with vs_inst_idx := LENGTH sd.cs_current_insts` >>
  `run_inst_seq (emitted_insts sd sc) s1 = OK (t with vs_inst_idx := s1.vs_inst_idx)` by
    (drule emit_op_run_pc >> simp[NoAsms, is_terminator_def] >>
     simp[Abbr `s1`, IgnAsm `r = s with vs_vars := r.vs_vars`, exec_result_map_def]) >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\ s1.vs_current_bb = sd.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sd.cs_current_insts` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def, same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `eval_operand data s1 = SOME a /\ eval_operand off s1 = SOME (mload (B+p) s)` by
    simp[Abbr `s1`, eval_operand_def, blockPrefixEquivTheory.lookup_var_set_inst_idx,
         AllCaseEqs()] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all finite_array_scalar_add_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G2`,`tn2`] strip_assume_tac)) >>
  suspend "compose"
QED

Resume finite_array_pointer_sentinel_origin[compose]:
  `t = r with vs_vars := t.vs_vars` by
    (qpat_assum `emit_op ADD [data; off] sd = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts sd sc) r = OK t` mp_tac >>
     simp[IgnAsm `r = s with vs_vars := r.vs_vars`, run_inst_seq_def,
          step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
     disch_then (SUBST1_TAC o SYM) >> simp[NoAsms,update_var_def]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_assum `t = r with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `r = s with vs_vars := _`
       (mp_tac o AP_TERM ``\r. r with vs_vars := t.vs_vars``) >> simp[]) >>
  qpat_assum `eval_operand out (t with vs_inst_idx := _) = _`
    (assume_tac o REWRITE_RULE [ghostPcTransportPtrTheory.eval_operand_inst_idx]) >>
  qexistsl [`G2`,`tn2`] >> simp[] >>
  conj_tac
  >- (ntac 2 strip_tac >>
      `not_fresh_at sd x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at sd x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
      simp[NoAsms, Abbr `s1`, blockPrefixEquivTheory.lookup_var_set_inst_idx] >>
      metis_tac[]) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) [] _`
    (qspecl_then [`D`,`explicit`] mp_tac) >> simp[NoAsms]
QED

Finalise finite_array_pointer_sentinel_origin

(* The bounded offset check is straight-line scalar code: one certificate
   protects all old registers and suffices for the actual successful run. *)
Theorem finite_array_pointer_guard_code[local]:
  (do bad <- emit_op LT [child_src;data];
      ok <- emit_op ISZERO [bad];
      emit_void ASSERT [ok];
      eend <- emit_op ADD [child_src;Lit (n2w sz)];
      compile_abi_decode_range_check child_src eend hi
   od) sa = ((),sb) ==>
  inst_extends sa sb /\ same_blocks sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?A. bodyPtrBopScalarSeq$bop_scalar_seq {x | not_fresh_at sa x} {child_src;data;hi;Lit (n2w sz)}
        (emitted_insts sa sb) A
Proof
  simp[abiEncoderTheory.compile_abi_decode_range_check_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       loweringShapeRulesTheory.emit_op_eq, loweringShapeRulesTheory.emit_void_eq] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[inst_extends_def, same_blocks_def, emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND] >>
  `!n. sa.cs_next_var <= n ==> ~not_fresh_at sa (STRING #"%" (toString n))` by
    (simp[not_fresh_at_def] >> metis_tac[]) >>
  ntac 10
    (once_rewrite_tac [CONJUNCT2 bodyPtrBopScalarSeqTheory.bop_scalar_seq_def] >>
     simp[mk_inst_def])
QED

Theorem finite_array_pointer_guard_origin[local]:
  (do bad <- emit_op LT [child_src;data];
      ok <- emit_op ISZERO [bad];
      emit_void ASSERT [ok];
      eend <- emit_op ADD [child_src;Lit (n2w sz)];
      compile_abi_decode_range_check child_src eend hi
   od) sa = ((),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  (!op. MEM op [child_src;data;hi] ==> op_prov G op = NONE /\ op_taint tn op = {}) ==>
  ?G' tn'.
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')
Proof
  strip_tac >> drule finite_array_pointer_guard_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     qpat_x_assum `_.bb_instructions = _` (PURE_ONCE_REWRITE_TAC o single) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[]) >>
  `!op. op IN {child_src;data;hi;Lit (n2w sz)} ==>
        op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[] >> rpt strip_tac >> gvs[op_prov_def,op_taint_def] >> metis_tac[]) >>
  drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame >> strip_tac >>
  drule_all bodyFullBopWordSuccessTheory.bop_word_scalar_success_joint >>
  disch_then (qspecl_then [`ARB`,`PG`] (qx_choosel_then [`H`,`u`] strip_assume_tac)) >>
  qexistsl [`H`,`u`] >> simp[] >> conj_tac
  >- (simp[lookup_var_def, op_taint_def] >> metis_tac[]) >>
  rpt gen_tac >> irule finite_array_empty_path_explicit >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    fs[inst_extends_def] >> simp[] >> metis_tac[]
QED

Theorem finite_array_pointer_bounded_origin[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) pos data hi sz sa = (out,sc) /\
  hi <> Lit 0w /\ run_inst_seq (emitted_insts sa sc) s = OK t /\
  fn_has_code sa sc func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_prov G pos = NONE /\ op_taint tn pos = {} /\
  eval_operand data s = SOME a /\ op_prov G data = NONE /\ op_taint tn data = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  (!x. data = Var x \/ hi = Var x ==> not_fresh_at sa x) /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G' tn'.
    eval_operand out t = SOME (a + mload (B+p) s) /\
    op_prov G' out = NONE /\ op_taint tn' out = {} /\
    t = s with vs_vars := t.vs_vars /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ hi _ sa = _` mp_tac >>
  simp[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_op ADD [Var source;pos] sa` >> simp[] >>
  rename1 `emit_op ADD [Var source;pos] sa = (addr,sb)` >>
  Cases_on `emit_op MLOAD [addr] sb` >> simp[] >>
  rename1 `emit_op MLOAD [addr] sb = (off,sd)` >>
  Cases_on `emit_op ADD [data;off] sd` >> simp[] >>
  rename1 `emit_op ADD [data;off] sd = (child_src,sm)` >>
  Cases_on `(do bad <- emit_op LT [child_src;data];
                ok <- emit_op ISZERO [bad];
                emit_void ASSERT [ok];
                eend <- emit_op ADD [child_src;Lit (n2w sz)];
                compile_abi_decode_range_check child_src eend hi
             od) sm` >>
  first_assum (assume_tac o SRULE [comp_bind_def, comp_ignore_bind_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  `compile_abi_decode_dyn_elem_ptr MLOAD (Var source) pos data (Lit 0w) sz sa = (child_src,sm)` by
    simp[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def,
         abiEncoderTheory.compile_abi_dec_addr_def,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  `inst_extends sa sm /\ same_blocks sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (`inst_extends sa sb /\ inst_extends sb sd /\ inst_extends sd sm /\
      same_blocks sa sb /\ same_blocks sb sd /\ same_blocks sd sm /\
      sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sd.cs_next_var /\
      sd.cs_next_var <= sm.cs_next_var` by
        metis_tac[inst_extends_emit_op,emit_op_same_blocks,ci_mono_emit_op,ci_mono_def,pairTheory.SND] >>
     metis_tac[inst_extends_trans,same_blocks_trans,arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "guard_cut"
QED

Resume finite_array_pointer_bounded_origin[guard_cut]:
  rename1 `run_inst_seq (emitted_insts sa sc) s = OK t` >>
  drule finite_array_pointer_guard_code >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sc` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sm ++ emitted_insts sm sc` by
    fs[inst_extends_def, emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts sa sc) s = OK t` mp_tac >>
  simp[] >> disch_then (qx_choose_then `r` strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  `!x. data = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all finite_array_pointer_sentinel_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  `r.vs_labels = s.vs_labels` by
    (qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  `!op. MEM op [child_src;data;hi] ==> op_prov G1 op = NONE /\ op_taint tn1 op = {}` by
    (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[old_operand_ghost_frame]) >>
  qabbrev_tac `s1 = r with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  qabbrev_tac `t1 = t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `run_inst_seq (emitted_insts sm sc) s1 = OK t1` by
    (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >> strip_tac >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sc)` by
       fs[EVERY_MEM] >> simp[Abbr `s1`,Abbr `t1`,run_inst_seq_inst_idx,exec_result_map_def]) >>
  `allocas_from lo s1 /\ ~s1.vs_halted /\ s1.vs_current_bb = sm.cs_current_bb /\
   s1.vs_inst_idx = LENGTH sm.cs_current_insts` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def,same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1` by
    (simp[Abbr `s1`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all finite_array_pointer_guard_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G2`,`tn2`] strip_assume_tac)) >>
  suspend "compose"
QED

Resume finite_array_pointer_bounded_origin[compose]:
  `t = r with vs_vars := t.vs_vars` by
    (qpat_assum `run_inst_seq (emitted_insts sm sc) r = OK t`
       (mp_then Any mp_tac bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_runtime_frame) >>
     disch_then drule >> simp[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_assum `t = r with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `r = s with vs_vars := _`
       (mp_tac o AP_TERM ``\r. r with vs_vars := t.vs_vars``) >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x r /\
     FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x t1 = _ /\ _` mp_tac >>
     simp[NoAsms,Abbr `s1`,Abbr `t1`,blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `!x. child_src = Var x ==> not_fresh_at sm x` by
    (drule abi_decoder_operand_live_emit >> Cases_on `child_src` >>
     simp[calldata_operand_live_not_fresh]) >>
  `t.vs_labels = r.vs_labels` by
    (qpat_assum `t = r with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  `eval_operand child_src t = SOME (a+mload (B+p) s) /\
    op_prov G2 child_src = NONE /\ op_taint tn2 child_src = {}` by
    (drule_all old_operand_ghost_frame >> simp[]) >>
  qexistsl [`G2`,`tn2`] >> simp[] >> conj_tac
  >- (ntac 2 strip_tac >> `not_fresh_at sm x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      map_every (fn a => qpat_assum a (qspec_then `x` mp_tac))
        [`!x. not_fresh_at sm x ==> lookup_var x t = _ /\ _`,
         `!x. not_fresh_at sa x ==> lookup_var x r = _ /\ _`] >> metis_tac[]) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) [] _`
    (qspecl_then [`D`,`explicit`] mp_tac) >> simp[NoAsms,Abbr `t1`]
QED

Finalise finite_array_pointer_bounded_origin

(* The offset phase is an in-block extension, independent of its operands. *)
Theorem finite_array_offset_code[local]:
  compile_abi_decode_dyn_elem_ptr MLOAD (Var source) pos data hi sz st = (out,ready) /\
  hi <> Lit 0w ==>
  inst_extends st ready /\ same_blocks st ready /\ st.cs_next_var <= ready.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (drule abi_array_pointer_reentry_opcodes >>
     simp[EVERY_MEM] >> disch_tac >> qx_gen_tac `i` >> disch_tac >>
     first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  pop_assum (fn th => rewrite_tac [th]) >>
  qpat_x_assum `compile_abi_decode_dyn_elem_ptr _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def,
       abiEncoderTheory.compile_abi_dec_addr_def,
       abiEncoderTheory.compile_abi_decode_range_check_def,
       comp_bind_def,comp_ignore_bind_def,comp_return_def,
       loweringShapeRulesTheory.emit_op_eq,loweringShapeRulesTheory.emit_void_eq] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >>
  simp[inst_extends_def,same_blocks_def,emitted_insts_def,rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem finite_array_offset_source_origin[local]:
  abi_decode_array_source_setup (Var ip) src MLOAD (Var source) hi abi_sz st = ((idx,child_src),ready) /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  fn_has_code st ready func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var ip s = SOME w /\ ptr_covers G tn ip s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = n2w j /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  eval_operand src s = SOME (n2w p) /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\ hi <> Lit 0w /\
  (!x. src = Var x \/ hi = Var x ==> not_fresh_at st x) /\ not_fresh_at st source /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  p+32+j*abi_sz+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G' tn'.
    eval_operand idx t = SOME (n2w j) /\
    eval_operand child_src t = SOME (n2w (p+32) + mload (B+(p+32+j*abi_sz)) s) /\
    op_prov G' idx = NONE /\ op_taint tn' idx = {} /\
    op_prov G' child_src = NONE /\ op_taint tn' child_src = {} /\
    t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |> /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')
Proof
  strip_tac >> drule abi_decode_array_source_setup_split >>
  disch_then (qx_choosel_then [`ops`,`mid`] strip_assume_tac) >>
  PairCases_on `ops` >> fs[] >>
  qpat_x_assum `idx = _` (SUBST_ALL_TAC o SYM) >>
  drule finite_array_head_code >> strip_tac >>
  drule_all finite_array_offset_code >> strip_tac >>
  `cs_extends st mid /\ cs_extends mid ready` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def,same_blocks_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    fs[inst_extends_def,emitted_insts_append] >>
  qpat_x_assum `run_inst_seq (emitted_insts st ready) s = OK t` mp_tac >>
  simp[] >> disch_then (qx_choose_then `r` strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  `!x. src = Var x ==> not_fresh_at st x` by metis_tac[] >>
  drule_all finite_array_setup_head_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G0`,`tn0`] strip_assume_tac)) >>
  suspend "pointer_cut"
QED

Resume finite_array_offset_source_origin[pointer_cut]:
  qabbrev_tac `s0 = r with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  qabbrev_tac `t0 = t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `run_inst_seq (emitted_insts mid ready) s0 = OK t0` by
    simp[Abbr `s0`,Abbr `t0`,run_inst_seq_inst_idx,exec_result_map_def] >>
  `r.vs_labels = s.vs_labels` by
    (qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  `op_prov G0 hi = NONE /\ op_taint tn0 hi = {}` by
    (`!x. hi = Var x ==> not_fresh_at st x` by metis_tac[] >>
     drule_all (Q.SPEC `hi` (Q.GEN `op` (SPEC_ALL old_operand_ghost_frame))) >> simp[]) >>
  `abi_decode_ptr_window G0 tn0 r source (n2w B) L` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `abi_decode_ptr_window G0 tn0 s0 source (n2w B) L` by
    (qpat_assum `abi_decode_ptr_window G0 tn0 r source _ _` mp_tac >>
     simp[NoAsms,Abbr `s0`,abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_def,
          blockPrefixEquivTheory.lookup_var_set_inst_idx,ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  `allocas_from lo s0 /\ ~s0.vs_halted /\ s0.vs_current_bb = mid.cs_current_bb /\
   s0.vs_inst_idx = LENGTH mid.cs_current_insts /\ s0.vs_memory = s.vs_memory /\
   B+L <= s0.vs_alloca_next` by
    (simp[Abbr `s0`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def,same_blocks_def] >> first_assum ACCEPT_TAC) >>
  rename1 `compile_abi_decode_dyn_elem_ptr MLOAD (Var source) head data hi abi_sz mid = _` >>
  `eval_operand head s0 = SOME (n2w (p+32+j*abi_sz)) /\
   eval_operand data s0 = SOME (n2w (p+32))` by
    simp[Abbr `s0`,word_add_n2w,word_mul_n2w] >>
  `!x. data = Var x \/ hi = Var x ==> not_fresh_at mid x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(p+32+j*abi_sz)+32 <= L` by simp[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (simp[Abbr `s0`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  drule_all finite_array_pointer_bounded_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G1`,`tn1`] strip_assume_tac)) >>
  suspend "join"
QED

Resume finite_array_offset_source_origin[join]:
  `!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r /\
     FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x t0 = _ /\ _` mp_tac >>
     simp[NoAsms,Abbr `s0`,Abbr `t0`,blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `t.vs_labels = r.vs_labels` by
    (qpat_assum `t0 = s0 with vs_vars := _` (mp_tac o AP_TERM ``\v. v.vs_labels``) >>
     simp[Abbr `s0`,Abbr `t0`]) >>
  `eval_operand idx t = SOME (n2w j) /\ op_prov G1 idx = NONE /\ op_taint tn1 idx = {}` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x t = _ /\ _`
      (mp_then Any (qspec_then `idx` mp_tac) old_operand_ghost_frame) >> simp[]) >>
  `eval_operand child_src t = SOME (n2w (p+32) + mload (B+(p+32+j*abi_sz)) s)` by
    (qpat_x_assum `eval_operand child_src t0 = _` mp_tac >>
     simp[Abbr `t0`,mload_def]) >>
  `t = s with <| vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx |>` by
    (qpat_assum `t0 = s0 with vs_vars := _` mp_tac >>
     simp[NoAsms,Abbr `t0`,Abbr `s0`] >>
     qpat_assum `r = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >>
     disch_then (mp_tac o AP_TERM ``\v. v with vs_inst_idx := t.vs_inst_idx``) >> simp[]) >>
  qexistsl [`G1`,`tn1`] >> simp[] >> conj_tac
  >- (ntac 2 strip_tac >> `not_fresh_at mid x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      map_every (fn a => qpat_assum a (qspec_then `x` mp_tac))
        [`!x. not_fresh_at mid x ==> lookup_var x t = _ /\ _`,
         `!x. not_fresh_at st x ==> lookup_var x r = _ /\ _`] >> simp[]) >>
  rpt gen_tac >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
    (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s0,G0,tn0) [] _`
    (qspecl_then [`D`,`explicit`] mp_tac) >> simp[NoAsms,Abbr `t0`,Abbr `s0`]
QED

Finalise finite_array_offset_source_origin

Theorem finite_array_offset_setup_origin[local]:
  abi_decode_array_element_setup (Var ip) src (Var output) MLOAD (Var source) hi di
    abi_sz mem_sz st = (ops,ready) /\ dec_info_needs_offset di /\
  run_inst_seq (emitted_insts st ready) s = OK t /\
  fn_has_code st ready func /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_var ip s = SOME w /\ ptr_covers G tn ip s 32 /\
  w2n w + 32 <= s.vs_alloca_next /\ mload (w2n w) s = n2w j /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem) /\
  eval_operand src s = SOME (n2w p) /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\ hi <> Lit 0w /\
  (!x. src = Var x \/ hi = Var x ==> not_fresh_at st x) /\ not_fresh_at st source /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  p+32+j*abi_sz+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  lookup_var output s = SOME (n2w d) /\ ptr_covers G tn output s outsz /\
  not_fresh_at st output /\ 32+j*mem_sz+mem_sz <= outsz /\
  d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256) ==>
  ?G' tn' child.
    SND (SND ops) = Var child /\ ptr_covers G' tn' child t mem_sz /\
    eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (p+32) + mload (B+(p+32+j*abi_sz)) s) /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at st x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH ready.cs_current_insts),G',tn')
Proof
  strip_tac >> drule_all abi_decode_dynamic_element_setup_split >>
  disch_then (qx_choosel_then [`srcops`,`mid`] strip_assume_tac) >>
  drule abi_decode_array_source_setup_counters >> strip_tac >>
  drule abi_decode_array_source_setup_split >>
  disch_then (qx_choosel_then [`hops`,`head`] strip_assume_tac) >>
  PairCases_on `srcops` >> fs[] >>
  drule finite_array_head_code >> strip_tac >>
  drule_all finite_array_offset_code >> strip_tac >>
  drule indexed_destination_structure >> strip_tac >>
  `inst_extends st mid /\ same_blocks st mid` by metis_tac[inst_extends_trans,same_blocks_trans] >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  map_every (fn p => qpat_x_assum p kall_tac)
    [`inst_extends st head`,`inst_extends head mid`,`same_blocks st head`,`same_blocks head mid`] >>
  `cs_extends st mid /\ cs_extends mid ready` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def,same_blocks_def]) >>
  `fn_has_code st mid func /\ fn_has_code mid ready func` by metis_tac[fn_has_code_split] >>
  `emitted_insts st ready = emitted_insts st mid ++ emitted_insts mid ready` by
    fs[inst_extends_def,emitted_insts_append] >>
  `t.vs_labels = s.vs_labels` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     qpat_assum `t = s with vs_vars := _` (PURE_ONCE_REWRITE_TAC o single) >> simp[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts st ready) s = OK t` mp_tac >>
  simp[] >> disch_then (qx_choose_then `r0` strip_assume_tac o MATCH_MP run_inst_seq_append_ok) >>
  `p+32+j*abi_sz+32 <= L` by simp[] >>
  drule_all finite_array_offset_source_origin >>
  disch_then (qspec_then `PG` (qx_choosel_then [`G0`,`tn0`] strip_assume_tac)) >>
  suspend "destination"
QED

Resume finite_array_offset_setup_origin[destination]:
  `lookup_var output r0 = SOME (n2w d) /\ ptr_covers G0 tn0 output r0 outsz` by
    (conj_asm1_tac >- metis_tac[] >>
     irule ptr_covers_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qabbrev_tac `s0 = r0 with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `run_inst_seq (emitted_insts mid ready) s0 = OK (t with vs_inst_idx := s0.vs_inst_idx)` by
    simp[Abbr `s0`,run_inst_seq_inst_idx,exec_result_map_def] >>
  `lookup_var output s0 = SOME (n2w d) /\ ptr_covers G0 tn0 output s0 outsz /\
   eval_operand (FST hops) s0 = SOME (n2w j) /\ not_fresh_at mid output` by
    (simp[Abbr `s0`,blockPrefixEquivTheory.lookup_var_set_inst_idx,
          ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. FST hops = Var x ==> not_fresh_at mid x` by
    (rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  `32+j*mem_sz+mem_sz <= outsz /\ d+32+j*mem_sz < dimword (:256)` by simp[] >>
  qpat_x_assum `run_inst_seq (emitted_insts mid ready) r0 = OK t` kall_tac >>
  drule_all indexed_destination_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`H`,`cx`,`ctx`,`PG`,`R`]
    (qx_choosel_then [`G1`,`tn1`,`child`] strip_assume_tac)) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  suspend "compose"
QED

Resume finite_array_offset_setup_origin[compose]:
  `!x. not_fresh_at mid x ==> lookup_var x t = lookup_var x r0 /\
     FLOOKUP G1 x = FLOOKUP G0 x /\ op_taint tn1 (Var x) = op_taint tn0 (Var x)` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x (_ with vs_inst_idx := _) = _ /\ _`
       mp_tac >> simp[NoAsms,Abbr `s0`,blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `t.vs_labels = r0.vs_labels` by
    (qpat_assum `r0 = s with <|vs_vars := _; vs_inst_idx := _|>`
       (mp_tac o AP_TERM ``\v. v.vs_labels``) >> simp[]) >>
  `eval_operand (FST hops) t = SOME (n2w j) /\
   eval_operand srcops1 t = SOME (n2w (p+32) + mload (B+(p+32+j*abi_sz)) s) /\
   op_prov G1 (FST hops) = NONE /\ op_taint tn1 (FST hops) = {} /\
   op_prov G1 srcops1 = NONE /\ op_taint tn1 srcops1 = {}` by
    (qpat_assum `!x. not_fresh_at mid x ==> lookup_var x t = _ /\ _`
       (mp_then Any mp_tac old_operand_ghost_frame) >>
     disch_then (fn th => map_every (fn opnd => qspec_then opnd mp_tac th)
       [`FST hops`,`srcops1`]) >>
     `!x. srcops1 = Var x ==> not_fresh_at mid x` by
       metis_tac[calldata_operand_live_not_fresh] >> simp[]) >>
  `ptr_covers G1 tn1 child t mem_sz` by
    (qpat_assum `ptr_covers G1 tn1 child (_ with <|vs_inst_idx := _; vs_inst_idx := _|>) mem_sz`
       mp_tac >> simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx] >>
     gvs[ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s /\
     FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (ntac 2 strip_tac >> `not_fresh_at mid x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     map_every (fn a => qpat_assum a (qspec_then `x` mp_tac))
       [`!x. not_fresh_at mid x ==> lookup_var x t = _ /\ _`,
        `!x. not_fresh_at st x ==> lookup_var x r0 = _ /\ _`] >> simp[]) >>
  qexistsl [`G1`,`tn1`,`child`] >> simp[] >> rpt gen_tac >>
  `allocas_from lo s0 /\ ~s0.vs_halted /\ s0.vs_current_bb = mid.cs_current_bb /\
   s0.vs_inst_idx = LENGTH mid.cs_current_insts` by
    (simp[Abbr `s0`] >>
     qpat_assum `r0 = s with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     fs[allocas_from_def,same_blocks_def] >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (simp[Abbr `s0`] >>
     qpat_assum `r0 = s with <|vs_vars := _; vs_inst_idx := _|>`
       (PURE_ONCE_REWRITE_TAC o single) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     simp[NoAsms, allocas_below_fmp_def] >> metis_tac[]) >>
  qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] _`
     (qspecl_then [`D`,`explicit`] (mp_then Any irule gas_origin_ptr_path_trans)) >>
  qpat_assum `!D lower explicit ctx' func. _ ==> gas_origin_ptr_path _ (s0,G0,tn0) [] _`
     (qspecl_then [`D`,`lo`,`explicit`,`ctx`,`func`] mp_tac) >>
  simp[Abbr `s0`] >> gvs[]
QED

Finalise finite_array_offset_setup_origin

(* The raw endpoint carries the new child pointer; normalize its cursor
   before composing with the child. The source and the parent pointers
   are still the ones at the setup entry. *)
Theorem finite_array_setup_child_transport[local]:
  abi_decode_array_element_setup (Var ip) src (Var output) MLOAD (Var source) hi di
    abi_sz mem_sz st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK a /\
  b = a with vs_inst_idx := LENGTH ready.cs_current_insts /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  alloca_inv s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ptr_covers G tn output s outsz /\ ptr_covers G tn ip s 32 /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  not_fresh_at st output /\ not_fresh_at st ip /\ not_fresh_at st source /\
  (!x. src = Var x \/ hi = Var x ==> not_fresh_at st x) /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  ptr_covers G' tn' child a mem_sz /\ tn'.t_mem = tn.t_mem /\
  (!x. not_fresh_at st x ==> lookup_var x a = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ptr_covers G' tn' child b mem_sz /\
  ptr_covers G' tn' output b outsz /\ ptr_covers G' tn' ip b 32 /\
  abi_decode_ptr_window G' tn' b source (n2w B) L /\
  op_prov G' hi = NONE /\ op_taint tn' hi = {} /\
  b.vs_memory = s.vs_memory /\ b.vs_allocas = s.vs_allocas /\
  b.vs_alloca_next = s.vs_alloca_next /\
  b.vs_accounts = s.vs_accounts /\ b.vs_transient = s.vs_transient /\
  b.vs_call_ctx = s.vs_call_ctx /\ b.vs_immutables = s.vs_immutables /\
  alloca_history func b /\ allocas_from lo b /\ lo <= b.vs_alloca_next /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    lookup_var x b = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `ready.cs_current_bb = st.cs_current_bb /\
   isPREFIX st.cs_current_insts ready.cs_current_insts /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    (`abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
     Cases_on `dec_info_needs_offset di` >>
     imp_res_tac abi_decode_static_element_setup_shape >>
     imp_res_tac abi_decode_dynamic_element_setup_shape >> fs[EVERY_MEM]) >>
  `alloca_history func b` by
    (drule_all entryDecoderHistoryFrameTheory.entry_straight_line_alloca_history >> simp[]) >>
  `b = s with <|vs_vars := a.vs_vars; vs_inst_idx := LENGTH ready.cs_current_insts|>` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     qpat_assum `b = a with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     qpat_assum `a = s with vs_vars := _` (pure_once_rewrite_tac o single) >>
     simp[]) >>
  `allocas_from lo b /\ lo <= b.vs_alloca_next` by
    (qpat_assum `b = s with <|vs_vars := _; vs_inst_idx := _|>` (pure_once_rewrite_tac o single) >>
     simp[allocas_from_def] >> fs[allocas_from_def] >> metis_tac[]) >>
  `!x. not_fresh_at st x ==> lookup_var x b = lookup_var x s /\
     FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x a = _ /\ _` mp_tac >>
     qpat_assum `b = a with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     simp[blockPrefixEquivTheory.lookup_var_set_inst_idx]) >>
  `ptr_covers G' tn' output b outsz /\ ptr_covers G' tn' ip b 32` by
    (conj_tac >> irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >> metis_tac[]) >>
  `abi_decode_ptr_window G' tn' b source (n2w B) L` by
    (irule abiDecodePtrMemberFrameTheory.abi_decode_ptr_window_frame >> qexistsl [`G`,`s`,`tn`] >> metis_tac[]) >>
  `op_prov G' hi = NONE /\ op_taint tn' hi = {}` by
    (Cases_on `hi` >> fs[op_prov_def,op_taint_def] >> metis_tac[]) >>
  `ptr_covers G' tn' child b mem_sz` by
    (qpat_assum `b = a with vs_inst_idx := _` (pure_once_rewrite_tac o single) >>
     simp[ghostPcTransportPtrTheory.ptr_covers_inst_idx]) >>
  `!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
     lookup_var x b = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[calldata_operand_live_not_fresh] >>
  simp[IgnAsm `b = a with vs_inst_idx := _`,IgnAsm `b = s with <|vs_vars := _; vs_inst_idx := _|>`]
  >> qpat_assum `b = s with <|vs_vars := _; vs_inst_idx := _|>` (pure_once_rewrite_tac o single)
  >> simp[]
QED

(* Recover the joint entry from the same setup run as the physical child
   entry. The extra cursor update affects neither operand nor ghost. *)
Theorem finite_array_setup_child_joint[local]:
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    (Var source) hi src (Var output) B L xs p d outsz s /\
  abi_decode_array_element_setup (Var ip) src (Var output) MLOAD (Var source) hi di
    abi_sz mem_sz st = (ops,ready) /\
  run_inst_seq (emitted_insts st ready) s = OK a /\
  b = a with vs_inst_idx := LENGTH ready.cs_current_insts /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  ~s.vs_halted /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ alloca_history func s /\
  lookup_var ip s = SOME (n2w slot) /\ ptr_covers G tn ip s 32 /\
  slot < dimword (:256) /\ FLOOKUP s.vs_allocas counter = SOME (slot,32) /\ mload slot s = n2w j /\
  (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn.t_mem) /\
  op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  abi_decoder_operand_live st.cs_next_var (Var ip) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\
  (dec_info_needs_offset di ==> p+32+j*abi_sz+32 <= L) /\
  32+j*mem_sz+mem_sz <= outsz ==>
  ?G' tn' child.
    SND (SND ops) = Var child /\ ptr_covers G' tn' child b mem_sz /\
    ptr_covers G' tn' output b outsz /\ ptr_covers G' tn' ip b 32 /\
    abi_decode_ptr_window G' tn' b source (n2w B) L /\
    op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
    op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
    op_prov G' hi = NONE /\ op_taint tn' hi = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    b.vs_memory = s.vs_memory /\ b.vs_allocas = s.vs_allocas /\
    b.vs_alloca_next = s.vs_alloca_next /\
    b.vs_accounts = s.vs_accounts /\ b.vs_transient = s.vs_transient /\
    b.vs_call_ctx = s.vs_call_ctx /\ b.vs_immutables = s.vs_immutables /\
    alloca_history func b /\ allocas_from lo b /\ lo <= b.vs_alloca_next /\
    (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      lookup_var x b = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK b,G',tn')
Proof
  strip_tac >>
  qhdtm_assum `abi_malformed_entry`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_malformed_entry_def]) >>
  qhdtm_assum `abi_malformed_allocated_window`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_allocated_window_def]) >>
  `alloca_inv s` by metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `B+L <= s.vs_alloca_next /\ slot+32 <= s.vs_alloca_next` by
    (`B+cap <= s.vs_alloca_next /\ slot+32 <= s.vs_alloca_next` by
       metis_tac[alloca_site_registered_below] >> decide_tac) >>
  `lookup_var output s = SOME (n2w d)` by fs[eval_operand_def] >>
  `!x. src = Var x \/ hi = Var x ==> not_fresh_at st x` by
    (fs[EVERY_DEF] >> metis_tac[calldata_operand_live_not_fresh]) >>
  `not_fresh_at st output /\ not_fresh_at st source /\ not_fresh_at st ip` by
    fs[EVERY_DEF,calldata_operand_live_not_fresh] >>
  `w2n (n2w slot:bytes32)+32 <= s.vs_alloca_next /\
   mload (w2n (n2w slot:bytes32)) s = n2w j /\
   (!i. w2n (n2w slot:bytes32) <= i /\ i < w2n (n2w slot:bytes32)+32 ==>
      i NOTIN tn.t_mem)` by simp[w2n_n2w] >>
  `d+32+j*mem_sz < dimword (:256) /\ mem_sz < dimword (:256)` by decide_tac >>
  `?G' tn' child.
      SND (SND ops) = Var child /\ ptr_covers G' tn' child a mem_sz /\
      op_prov G' (FST ops) = NONE /\ op_taint tn' (FST ops) = {} /\
      op_prov G' (FST (SND ops)) = NONE /\ op_taint tn' (FST (SND ops)) = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at st x ==> lookup_var x a = lookup_var x s /\
        FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
      !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK b,G',tn')` by
    (Cases_on `dec_info_needs_offset di`
     >- (`p+32+j*abi_sz+32 <= L` by simp[] >>
         drule_all finite_array_offset_setup_origin >>
         disch_then (qspec_then `PG` (qx_choosel_then [`GA`,`tnA`,`childA`] strip_assume_tac)) >>
         qexistsl [`GA`,`tnA`,`childA`] >> simp[]) >>
     `!x. src = Var x ==> not_fresh_at st x` by metis_tac[] >>
     drule_all finite_array_static_setup_origin >>
     disch_then (qspec_then `PG` (qx_choosel_then [`G'`,`tn'`,`child`] strip_assume_tac)) >>
     qexistsl [`G'`,`tn'`,`child`] >> simp[]) >>
  suspend "transport"
QED

Resume finite_array_setup_child_joint[transport]:
  drule_all finite_array_setup_child_transport >> strip_tac >>
  qexistsl [`G'`,`tn'`,`child`] >> simp[IgnAsm `b = a with vs_inst_idx := _`]
QED

Finalise finite_array_setup_child_joint

(* The table entry and the child payload have separate bounds. *)
Theorem finite_array_child_position[local]:
  abi_decoder_coherent ce env sf ty tv /\
  di = type_to_abi_dec_info sf ce ty /\
  abi_sz = abi_member_head_size (vyper_to_abi_type env ty) /\
  LENGTH xs = L /\ j < LENGTH vs /\ p+32+LENGTH vs*abi_sz <= L /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
    (DROP (p+32) xs) (DROP (p+32) xs) /\
  abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
    (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs /\
  q = p+32+(if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz) ==>
  q <= L /\ vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP q xs)) = SOME (EL j vs) /\
  (is_dynamic (vyper_to_abi_type env ty) \/ q+static_length (vyper_to_abi_type env ty) <= L) /\
  (dec_info_needs_offset di ==> p+32+j*abi_sz+32 <= L /\ q+abi_sz <= L)
Proof
  strip_tac >>
  `q <= L /\ vyper_decode_valid_enc (vyper_to_abi_type env ty) (DROP q xs) /\
   abi_to_vyper env ty (dec (vyper_to_abi_type env ty) (DROP q xs)) = SOME (EL j vs) /\
   (is_dynamic (vyper_to_abi_type env ty) \/ q+static_length (vyper_to_abi_type env ty) <= L)` by
    metis_tac[abi_valid_allocated_array_child_position] >>
  simp[IgnAsm `q = _`] >> strip_tac >>
  `is_dynamic (vyper_to_abi_type env ty) /\
   (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    metis_tac[abi_decoder_needs_offset_iff, abi_decoder_coherent_dynamic,
       abi_decoder_nonempty_readable_head] >>
  `abi_sz = 32` by simp[abi_member_head_size_def] >>
  `SUC j*abi_sz <= LENGTH vs*abi_sz` by
    (irule LESS_MONO_MULT2 >> decide_tac) >>
  `32 <= LENGTH (DROP q xs)` by metis_tac[abi_valid_dynamic_head_min] >>
  qpat_x_assum `SUC j*abi_sz <= _` mp_tac >>
  qpat_x_assum `32 <= LENGTH (DROP q xs)` mp_tac >>
  gvs[LENGTH_DROP, MULT_CLAUSES, abi_member_head_size_def, IgnAsm `q = _`] >> decide_tac
QED

Theorem finite_array_physical_setup[local]:
  abi_malformed_entry H ctx func cenv cx es setup sites dstid live
    base_op hi src dst B L xs p d outsz h /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  eval_operand ip h = SOME (n2w slot) /\ mload slot h = n2w j /\ slot < dimword (:256) /\
  abi_decoder_operand_live setup.cs_next_var ip /\
  q = p+32+(if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz) /\
  q <= L /\ (dec_info_needs_offset di ==> p+32+j*abi_sz+32 <= L /\ q+abi_sz <= L) /\
  setup.cs_next_var <= child.cs_next_var /\ child.cs_next_var <= ceiling.cs_next_var /\
  fresh_vars_wrt ceiling h /\ d+32+j*mem_sz+childsz <= d+outsz ==>
  ?a. run_inst_seq (emitted_insts setup child) h = OK a /\
    abi_malformed_entry H ctx func cenv cx es child sites dstid live
      base_op hi (FST (SND ops)) (SND (SND ops)) B L xs q (d+32+j*mem_sz) childsz a /\
    abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h a /\
    eval_operand (FST ops) a = SOME (n2w j) /\ eval_operand ip a = SOME (n2w slot) /\
    fresh_vars_wrt ceiling a /\ a.vs_memory = h.vs_memory
Proof
  strip_tac >>
  `mload (w2n (n2w slot:bytes32)) h = n2w j` by simp[w2n_n2w] >>
  Cases_on `dec_info_needs_offset di`
  >- (`q = p+32+abi_head_word (DROP (p+32+j*abi_sz) xs)` by
        (qpat_assum `q = _` mp_tac >> simp_tac bool_ss [] >> metis_tac[]) >>
      `p+32+j*abi_sz+32 <= L /\ p+32+abi_head_word (DROP (p+32+j*abi_sz) xs)+abi_sz <= L` by
        metis_tac[] >>
      `abi_head_word (DROP (p+32+j*abi_sz) xs) = abi_head_word (DROP (p+32+j*abi_sz) xs)` by REFL_TAC >>
      drule_all abi_valid_allocated_dynamic_setup >> strip_tac >>
      goal_assum (drule_at Any) >> gvs[]) >>
  `eval_operand src h = SOME (n2w p) /\ eval_operand dst h = SOME (n2w d) /\
   abi_decoder_operand_live setup.cs_next_var src /\
   abi_decoder_operand_live setup.cs_next_var dst` by
    fs[abi_malformed_entry_def, EVERY_DEF] >>
  drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts setup child) h = OK a` >>
  `stmt_state_rel H ctx func cenv cx es h /\ local_ptrs_reserved cenv setup` by
    fs[abi_malformed_entry_def] >>
  `abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h a` by
    (first_assum (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) irule abi_malformed_setup_resource) >>
     qhdtm_assum `abi_decode_array_element_setup` (irule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv child` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `setup` >> simp[]) >>
  qexists_tac `a` >> simp[] >>
  irule abi_malformed_child_entry >>
  qhdtm_assum `abi_malformed_entry` (irule_at Any) >>
  qhdtm_assum `abi_malformed_resource_post` (irule_at Any) >>
  `d+outsz < dimword (:256) /\ B+L < dimword (:256)` by
    fs[abi_malformed_entry_def, abi_malformed_destination_def, abi_malformed_allocated_window_def] >>
  `abi_decoder_operand_live child.cs_next_var base_op /\
   abi_decoder_operand_live child.cs_next_var hi` by
    (fs[abi_malformed_entry_def, EVERY_DEF] >> conj_tac >>
     irule abi_decoder_operand_live_mono >> qexists_tac `setup.cs_next_var` >> simp[]) >>
  fs[] >> decide_tac
QED

Theorem finite_array_physical_child_entry[local]:
  abi_malformed_entry H ctx func cenv cx es setup sites dstid live
    base_op hi src dst B L xs p d outsz h /\
  abi_decoder_coherent ce env sf ty tv /\ di = type_to_abi_dec_info sf ce ty /\
  abi_sz = abi_member_head_size (vyper_to_abi_type env ty) /\
  LENGTH xs = L /\ j < LENGTH vs /\ p+32+LENGTH vs*abi_sz <= L /\
  vyper_decode_valid_enc_tuple (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
    (DROP (p+32) xs) (DROP (p+32) xs) /\
  abi_to_vyper_list env (REPLICATE (LENGTH vs) ty)
    (abi_decode_members (REPLICATE (LENGTH vs) (vyper_to_abi_type env ty))
      (DROP (p+32) xs) (DROP (p+32) xs)) = SOME vs /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di abi_sz mem_sz setup = (ops,child) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi di child = ((),child_end) /\
  fn_has_code setup child func /\ fn_has_code child child_end func /\ fn_inst_ids_distinct func /\
  abi_malformed_scratch_sites child child_end func SUBSET sites /\
  eval_operand ip h = SOME (n2w slot) /\ mload slot h = n2w j /\ slot < dimword (:256) /\
  abi_decoder_operand_live setup.cs_next_var ip /\
  setup.cs_next_var <= child.cs_next_var /\ child.cs_next_var <= ceiling.cs_next_var /\
  child_end.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling h /\
  ~h.vs_halted /\ h.vs_current_bb = setup.cs_current_bb /\ h.vs_inst_idx = LENGTH setup.cs_current_insts /\
  d+32+j*mem_sz+type_memory_bytes ce ty <= d+outsz ==>
  ?a b q. run_inst_seq (emitted_insts setup child) h = OK a /\
    b = a with vs_inst_idx := LENGTH child.cs_current_insts /\
    abi_valid_allocated_entry H ce env sf ty tv (EL j vs) ctx func cenv cx es
      child child_end base_op hi (FST (SND ops)) (SND (SND ops)) B L xs q
      (d+32+j*mem_sz) dstid live ceiling b /\
    abi_malformed_resource_post ctx func cenv cx es setup.cs_next_var sites dstid h b /\
    abi_decode_sim ctx func h b /\ eval_operand (FST ops) b = SOME (n2w j) /\
    eval_operand ip b = SOME (n2w slot) /\
    (dec_info_needs_offset di ==> p+32+j*abi_sz+32 <= L)
Proof
  strip_tac >>
  qabbrev_tac `q = p+32+(if dec_info_needs_offset di then
    abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz)` >>
  `q = p+32+(if dec_info_needs_offset di then
     abi_head_word (DROP (p+32+j*abi_sz) xs) else j*abi_sz)` by simp[Abbr `q`] >>
  drule_all finite_array_child_position >> strip_tac >>
  drule_all finite_array_physical_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts setup child) h = OK a` >>
  `child.cs_blocks = setup.cs_blocks /\ child.cs_current_bb = setup.cs_current_bb /\
   isPREFIX setup.cs_current_insts child.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts setup child)` by
    (`abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
     Cases_on `dec_info_needs_offset di` >>
     metis_tac[abi_decode_static_element_setup_shape, abi_decode_dynamic_element_setup_shape]) >>
  `inst_extends setup child` by
    metis_tac[inst_extends_def, rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def,
              rich_listTheory.DROP_LENGTH_APPEND] >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` (qx_choose_then `b` strip_assume_tac)) >>
  `~a.vs_halted` by
    (drule_all abi_malformed_setup_frame >> strip_tac >>
     qpat_assum `a = _ with vs_vars := _`
       (mp_tac o AP_TERM ``\s. s.vs_halted``) >> simp[]) >>
  `abi_malformed_entry H ctx func cenv cx es child
     (abi_malformed_scratch_sites child child_end func) dstid live base_op hi
     (FST (SND ops)) (SND (SND ops)) B L xs q (d+32+j*mem_sz) (type_memory_bytes ce ty) a` by
    (qpat_assum `abi_malformed_entry _ _ _ _ _ _ child sites _ _ _ _ _ _ _ _ _ _ _ _ a` mp_tac >>
     qpat_assum `_ SUBSET sites` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [abi_malformed_entry_def, SUBSET_DEF] >> metis_tac[]) >>
  `a.vs_current_bb = child.cs_current_bb` by
    (qpat_assum `b.vs_current_bb = _` mp_tac >>
     qpat_assum `b = a with vs_inst_idx := _` SUBST1_TAC >> simp_tac (srw_ss()) []) >>
  `abi_decode_sim ctx func h (a with vs_inst_idx := LENGTH child.cs_current_insts)` by metis_tac[] >>
  qexistsl [`a`,`b`,`q`] >>
  qpat_x_assum `q = _` kall_tac >>
  pure_rewrite_tac[abi_valid_allocated_entry_def] >>
  qpat_assum `b = a with vs_inst_idx := _` SUBST1_TAC >>
  simp_tac (srw_ss()) [abi_malformed_entry_inst_idx, abi_malformed_resource_post_inst_idx,
    abiEncoderPathPropsTheory.fresh_vars_wrt_inst_idx, ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  metis_tac[]
QED

(* The coherent induction hypothesis is used at the normalized child PC.
   The live parent operands are recovered at its chosen finishing state. *)
local
val C = ``\ce env sf ty tv.
 !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
 abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
   st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
 !G tn PG lo.
 ~ctx_has_dalloca ctx /\
 abi_decode_ptr_window G tn s source (n2w B) L /\
 ptr_covers G tn output s (type_memory_bytes ce ty) /\
 op_prov G pos = NONE /\ op_prov G hi = NONE /\
 op_taint tn pos = {} /\ op_taint tn hi = {} /\
 allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
 ?u G' tn'.
   abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
     d (type_memory_bytes ce ty) s u /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
   (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK u,G',tn')) /\
   ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
   abi_decode_ptr_window G' tn' u source (n2w B) L /\
   (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
      val_in_memory tv v d mem) /\
   (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
   tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
      ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
      (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
   alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next``;
in
Theorem finite_array_decode_child_joint[local]:
  (^C) ce env sf ty tv /\
  abi_valid_allocated_entry H ce env sf ty tv v ctx func cenv cx es
    child child_end (Var source) hi pos (Var child_out) B L xs q cd dstid live ceiling b /\
  ~ctx_has_dalloca ctx /\ abi_decode_ptr_window G tn b source (n2w B) L /\
  ptr_covers G tn child_out b (type_memory_bytes ce ty) /\
  op_prov G pos = NONE /\ op_taint tn pos = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  allocas_from lo b /\ lo <= b.vs_alloca_next /\ alloca_history func b /\
  ptr_covers G tn output b outsz /\ ptr_covers G tn ip b 32 /\
  abi_decoder_operand_live child.cs_next_var (Var output) /\
  abi_decoder_operand_live child.cs_next_var (Var ip) /\
  abi_decoder_operand_live child.cs_next_var (Var iv) /\
  op_prov G (Var iv) = NONE /\ op_taint tn (Var iv) = {} ==>
  ?u G' tn'.
    abi_valid_allocated_post tv v ctx func cenv cx es child child_end ceiling dstid
      cd (type_memory_bytes ce ty) b u /\
    u.vs_accounts = b.vs_accounts /\ u.vs_transient = b.vs_transient /\
    u.vs_call_ctx = b.vs_call_ctx /\ u.vs_immutables = b.vs_immutables /\
    ptr_covers G' tn' output u outsz /\ ptr_covers G' tn' ip u 32 /\
    op_prov G' (Var iv) = NONE /\ op_taint tn' (Var iv) = {} /\
    abi_decode_ptr_window G' tn' u source (n2w B) L /\
    (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
       val_in_memory tv v cd mem) /\
    (!x. abi_decoder_operand_live child.cs_next_var (Var x) ==>
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!a. ~(cd <= a /\ a < cd+type_memory_bytes ce ty) /\
       ~abi_malformed_site_range (abi_malformed_scratch_sites child child_end func) b u a 1 ==>
       (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (b,G,tn) [] (OK u,G',tn')
Proof
  CONV_TAC (LAND_CONV (DEPTH_CONV BETA_CONV)) >>
  strip_tac >>
  qpat_x_assum `!v ctx. _` drule >>
  disch_then (qspecl_then [`G`,`tn`,`PG`,`lo`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`u`,`G1`,`tn1`] strip_assume_tac) >>
  `!x w. abi_decoder_operand_live child.cs_next_var (Var x) /\
         lookup_var x b = SOME w ==> lookup_var x u = SOME w` by
    (map_every qx_gen_tac [`x`,`w`] >>
     qhdtm_assum `abi_valid_allocated_post`
       (strip_assume_tac o REWRITE_RULE [abi_valid_allocated_post_def]) >>
     qhdtm_assum `abi_malformed_resource_post`
       (mp_tac o List.last o CONJUNCTS o
        REWRITE_RULE [abi_malformed_resource_post_def]) >>
     disch_then (qspecl_then [`Var x`,`w`] mp_tac) >>
     simp[eval_operand_def]) >>
  `!p n. ptr_covers G tn p b n /\ abi_decoder_operand_live child.cs_next_var (Var p) ==>
         ptr_covers G1 tn1 p u n` by
    (map_every qx_gen_tac [`p`,`n`] >> strip_tac >>
     `lookup_var p u = lookup_var p b` by
       (qpat_assum `ptr_covers G tn p b n`
          (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
        simp[]) >>
     irule ptr_covers_frame >>
     qpat_assum `ptr_covers G tn p b n` (irule_at Any) >>
     qpat_assum `!x. abi_decoder_operand_live child.cs_next_var (Var x) ==> _`
       (qspec_then `p` mp_tac) >> simp[]) >>
  `ptr_covers G1 tn1 output u outsz /\ ptr_covers G1 tn1 ip u 32` by
    (conj_tac >>
     qpat_assum `!p n. _ ==> ptr_covers G1 tn1 p u n` irule >> simp[]) >>
  `op_prov G1 (Var iv) = NONE /\ op_taint tn1 (Var iv) = {}` by
    (qpat_assum `op_prov G (Var iv) = NONE`
       (assume_tac o SIMP_RULE (srw_ss()) [op_prov_def]) >>
     qpat_assum `!x. abi_decoder_operand_live child.cs_next_var (Var x) ==> _`
       (qspec_then `iv` mp_tac) >> simp[op_prov_def]) >>
  qexistsl [`u`,`G1`,`tn1`] >> simp[]
QED
end

Theorem abi_valid_allocated_finite_loop_joint:
  abi_decoder_coherent ce env sf ty tv /\
  ((
    \ce env sf ty tv.
     !v ctx func cenv cx es st en source hi pos output B L xs p d dstid live ceiling s H0.
     abi_valid_allocated_entry H0 ce env sf ty tv v ctx func cenv cx es
       st en (Var source) hi pos (Var output) B L xs p d dstid live ceiling s ==>
     !G tn PG lo.
     ~ctx_has_dalloca ctx /\
     abi_decode_ptr_window G tn s source (n2w B) L /\
     ptr_covers G tn output s (type_memory_bytes ce ty) /\
     op_prov G pos = NONE /\ op_prov G hi = NONE /\
     op_taint tn pos = {} /\ op_taint tn hi = {} /\
     allocas_from lo s /\ lo <= s.vs_alloca_next /\ alloca_history func s ==>
     ?u G' tn'.
       abi_valid_allocated_post tv v ctx func cenv cx es st en ceiling dstid
         d (type_memory_bytes ce ty) s u /\
       u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
       u.vs_call_ctx = s.vs_call_ctx /\ u.vs_immutables = s.vs_immutables /\
       (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
         (s,G,tn) [] (OK u,G',tn')) /\
       ptr_covers G' tn' output u (type_memory_bytes ce ty) /\
       abi_decode_ptr_window G' tn' u source (n2w B) L /\
       (!mem. mem_agree_outside tn'.t_mem u.vs_memory mem ==>
          val_in_memory tv v d mem) /\
       (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
          FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
       tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
       (!a. ~(d <= a /\ a < d+type_memory_bytes ce ty) /\
          ~abi_malformed_site_range (abi_malformed_scratch_sites st en func) s u a 1 ==>
          (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
       alloca_history func u /\ allocas_from lo u /\ lo <= u.vs_alloca_next) ce env sf ty tv) /\
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray di abi_sz mem_sz dyn maxn /\
  (dyn \/ dec_info_needs_clamp di) /\
  abi_decode_array_loop_init (Var output) src MLOAD (Var source) hi maxn abi_sz
    start = ((Var ip,cnt),loop_st) /\
  compile_abi_decode_dyn_loop (Var output) src MLOAD (Var source) hi
    di abi_sz mem_sz (Var ip) cnt loop_st = ((),en) /\
  abi_decoder_operand_live loop_st.cs_next_var (Var ip) /\
  hdr = fresh_label_output "dec_dyn_hdr" loop_st.cs_next_label /\
  inst = mk_inst (loop_st.cs_next_id-2) ALLOCA [Lit 32w] [q] /\
  fn_has_code start en func /\ fn_inst_ids_distinct func /\
  en.cs_next_var <= ceiling.cs_next_var /\
  abi_malformed_scratch_sites start en func SUBSET sites /\
  abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
    sites dstid live (Var source) hi src (Var output) B L xs p d outsz
    (Var ip) slot inst q hdr tv vs origin j s /\
  abi_valid_allocated_entry H ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) ctx func cenv cx es
    start en (Var source) hi src (Var output) B L xs p d dstid live ceiling origin /\
  outsz = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  LENGTH vs = abi_head_word (DROP p xs) /\ LENGTH vs <= maxn /\
  maxn < dimword (:256) /\ j <= LENGTH vs /\ p+32+LENGTH vs*abi_sz <= L /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  alloca_history func s /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  op_prov G hi = NONE /\ op_taint tn hi = {} /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  ptr_covers G tn output s outsz /\ ptr_covers G tn ip s 32 /\
  (!a. slot <= a /\ a < slot+32 ==> a NOTIN tn.t_mem) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     mem_word_at d m = n2w (LENGTH vs)) /\
  (!k m. k < j /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) m) ==>
  ?h G' tn'.
    abi_decode_sim ctx func s h /\
    abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
      sites dstid d outsz origin h /\
    fresh_vars_wrt ceiling h /\ ~h.vs_halted /\
    h.vs_current_bb = en.cs_current_bb /\ h.vs_inst_idx = 0 /\
    h.vs_accounts = s.vs_accounts /\ h.vs_transient = s.vs_transient /\
    h.vs_call_ctx = s.vs_call_ctx /\ h.vs_immutables = s.vs_immutables /\
    alloca_history func h /\ allocas_from lo h /\ lo <= h.vs_alloca_next /\
    abi_decode_ptr_window G' tn' h source (n2w B) L /\
    ptr_covers G' tn' output h outsz /\
    (!a. ~(d <= a /\ a < d+outsz) /\
         ~abi_malformed_site_range sites s h a 1 ==>
         (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. abi_decoder_operand_live start.cs_next_var (Var x) ==>
      (!w. lookup_var x s = SOME w ==> lookup_var x h = SOME w) /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!m. mem_agree_outside tn'.t_mem h.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d m) /\
    !D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK h,G',tn')
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderArrayInitTheory.abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abiDecoderRecursiveArrayTheory.abi_decoder_recursive_loop_end >> strip_tac >>
  `fn_has_code loop_st en func` by
    (`cs_extends start loop_st` by (irule cs_extends_same_block >> simp[]) >>
     drule_all fn_has_code_split >> simp[]) >>
  drule abiDecoderLoopEmitTheory.abi_decode_dyn_loop_trace >>
  disch_then (qx_choosel_then [`labels`,`setup`,`ops`,`child`,`child_end`] strip_assume_tac) >>
  drule_all abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_phase_lookups >> strip_tac >>
  drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_prefix_facts >>
  simp[abi_decode_position_header_delta_def] >> strip_tac >>
  `FST labels = hdr /\ SND (SND labels) = en.cs_current_bb` by
    (qpat_assum `abi_decode_loop_prefix _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [abiDecoderLoopEmitTheory.abi_decode_loop_prefix_shape,
                       pairTheory.PAIR_EQ] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT1) >> simp[]) >>
  drule_all abiDecoderLoopCodeTheory.abi_decoder_loop_phase_containment >> strip_tac >>
  drule_all abiDecoderArraySetupCodeTheory.abi_decoder_array_body_code >> strip_tac >>
  drule abiDecoderArraySetupCodeTheory.abi_decoder_array_setup_head >> strip_tac >>
  `en.cs_next_var = child_end.cs_next_var + 1` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [] >> strip_tac >>
     drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_suffix_facts >> simp[]) >>
  `loop_st.cs_next_var+5 <= ceiling.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live start.cs_next_var src /\
   abi_decoder_operand_live start.cs_next_var (Var source) /\
   abi_decoder_operand_live start.cs_next_var (Var output)` by
    (qhdtm_assum `abi_valid_allocated_entry`
       (mp_tac o cj 5 o REWRITE_RULE [abi_valid_allocated_entry_def]) >>
     simp_tac bool_ss [abi_malformed_entry_def,EVERY_DEF] >>
     disch_then (map_every assume_tac o CONJUNCTS) >> simp[]) >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var (Var source) /\
   abi_decoder_operand_live loop_st.cs_next_var (Var output)` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `start.cs_next_var` >> simp[]) >>
  `LENGTH vs < dimword (:256) /\ p+32 <= L` by decide_tac >>
  `lookup_block hdr func.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions := abi_decode_position_header_insts
      (loop_st.cs_next_id+1) (Var ip) src MLOAD (Var source)
      loop_st.cs_next_var setup.cs_current_bb en.cs_current_bb|>` by
    (qpat_assum `FST labels = hdr` (SUBST1_TAC o SYM) >>
     qpat_assum `SND (SND labels) = en.cs_current_bb` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!k m. k < j /\ _ ==> _` mp_tac >>
  qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _` mp_tac >>
  qpat_x_assum `!a. slot <= a /\ _ ==> a NOTIN tn.t_mem` mp_tac >>
  qpat_x_assum `ptr_covers G tn ip s 32` mp_tac >>
  qpat_x_assum `ptr_covers G tn output s outsz` mp_tac >>
  qpat_x_assum `abi_decode_ptr_window G tn s source _ L` mp_tac >>
  qpat_x_assum `op_taint tn hi = {}` mp_tac >>
  qpat_x_assum `op_prov G hi = NONE` mp_tac >>
  qpat_x_assum `op_taint tn src = {}` mp_tac >>
  qpat_x_assum `op_prov G src = NONE` mp_tac >>
  qpat_x_assum `alloca_history func s` mp_tac >>
  qpat_x_assum `lo <= s.vs_alloca_next` mp_tac >>
  qpat_x_assum `allocas_from lo s` mp_tac >>
  qpat_x_assum `j <= LENGTH vs` mp_tac >>
  qhdtm_x_assum `abi_valid_allocated_array_inv` mp_tac >>
  map_every qid_spec_tac [`tn`,`G`,`s`,`j`] >>
  completeInduct_on `LENGTH vs-j` >> rpt strip_tac >>
  Cases_on `j = LENGTH vs`
  >- suspend "exit" >>
  suspend "iterate"
QED

Resume abi_valid_allocated_finite_loop_joint[exit]:
  qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
  qpat_x_assum `lookup_block (FST labels) _ = SOME _` kall_tac >>
  drule_all finite_array_exit_from_inv >>
  disch_then (qspecl_then [`maxn`,`PG`]
    (qx_choosel_then [`h`,`G1`,`tn1`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`h`,`G1`,`tn1`] >>
  qpat_x_assum `outsz = type_memory_bytes _ _` SUBST_ALL_TAC >> simp[] >>
  qx_gen_tac `x` >> disch_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var (Var x)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >> simp[]) >>
  simp[]
QED

Resume abi_valid_allocated_finite_loop_joint[iterate]:
  `j < LENGTH vs` by decide_tac >>
  qabbrev_tac `a0 = jump_to (if j < LENGTH vs then setup.cs_current_bb else en.cs_current_bb)
     (abi_decode_position_header_state (Var source) loop_st.cs_next_var B p j (LENGTH vs) s)` >>
  `a0 = jump_to (if j < LENGTH vs then setup.cs_current_bb else en.cs_current_bb)
     (abi_decode_position_header_state (Var source) loop_st.cs_next_var B p j (LENGTH vs) s)` by
    simp[Abbr `a0`] >>
  qpat_x_assum `lookup_block (FST labels) _ = SOME _` kall_tac >>
  drule_all finite_array_header_from_inv >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`G0`,`tn0`] (map_every assume_tac o CONJUNCTS))) >>
  `child_end.cs_next_id <= en.cs_next_id` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [] >> strip_tac >>
     drule abiDecoderRecursiveLoopLayoutTheory.abi_decoder_loop_suffix_facts >> simp[]) >>
  `abi_malformed_scratch_sites child child_end func SUBSET
     abi_malformed_scratch_sites start en func` by
    (irule abi_malformed_scratch_sites_nested >> decide_tac) >>
  `abi_malformed_scratch_sites child child_end func SUBSET sites` by
    metis_tac[SUBSET_TRANS] >>
  qhdtm_assum `abi_valid_allocated_array_inv`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_array_inv_def]) >>
  `start.cs_next_var <= setup.cs_next_var /\ child_end.cs_next_var <= ceiling.cs_next_var` by
    decide_tac >>
  `local_ptrs_reserved cenv setup` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `start` >>
     fs[abi_malformed_entry_def]) >>
  `abi_malformed_entry H ctx func cenv cx es setup sites dstid live
     (Var source) hi src (Var output) B L xs p d outsz a0` by
    (irule abi_malformed_aggregate_reentry >>
     qpat_assum `abi_malformed_entry _ _ _ _ _ _ start _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >> simp[]) >>
  `abi_decoder_operand_live setup.cs_next_var (Var ip)` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `loop_st.cs_next_var` >> simp[]) >>
  `lookup_var ip a0 = SOME (n2w slot) /\ mload slot a0 = n2w j` by
    fs[eval_operand_def,mload_def] >>
  `eval_operand (Var ip) a0 = SOME (n2w slot) /\
   a0.vs_current_bb = setup.cs_current_bb /\ a0.vs_inst_idx = LENGTH setup.cs_current_insts /\
   child.cs_next_var <= ceiling.cs_next_var` by (simp[eval_operand_def] >> decide_tac) >>
  `abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
   vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) (DROP p xs) /\
   abi_to_vyper env (ArrayT ty (Dynamic maxn))
     (dec (Array NONE (vyper_to_abi_type env ty)) (DROP p xs)) =
       SOME (ArrayV (DynArrayV vs))` by
    (qhdtm_assum `abi_valid_allocated_entry` mp_tac >>
     rewrite_tac[abi_valid_allocated_entry_def,cj 3 vyperABITheory.vyper_to_abi_type_def] >>
     strip_tac >> simp[]) >>
  `di = type_to_abi_dec_info sf ce ty /\
   abi_sz = abi_member_head_size (vyper_to_abi_type env ty) /\
   mem_sz = type_memory_bytes ce ty /\ mem_sz = type_memory_size tv` by
    (qpat_assum `abi_decoder_coherent ce env sf ty tv`
       (mp_tac o MATCH_MP abiDecoderCoherenceTheory.abi_decoder_coherent_header) >>
     qpat_assum `type_to_abi_dec_info _ _ (ArrayT _ _) = _` mp_tac >>
     simp_tac (srw_ss()) [cj 3 exprLoweringTheory.type_to_abi_dec_info_def,
                         abiDecoderCoherenceTheory.abi_decoder_header_def] >> metis_tac[]) >>
  `LENGTH xs = L` by
    (`mem_bytes_at B L s.vs_memory = xs` by
       fs[abi_malformed_entry_def,abi_malformed_allocated_window_def] >>
     metis_tac[valueEncodingPropsTheory.LENGTH_mem_bytes_at]) >>
  drule_all abi_valid_allocated_array_source_view >>
  disch_then (qx_choose_then `payload` strip_assume_tac) >>
  `payload = vs` by
    (qpat_assum `ArrayV (DynArrayV vs) = ArrayV (DynArrayV payload)` mp_tac >> simp[]) >>
  qpat_x_assum `payload = vs` SUBST_ALL_TAC >>
  `32+LENGTH vs*type_memory_size tv <= outsz /\
   (!k. k < LENGTH vs ==> d+32+k*type_memory_size tv+type_memory_size tv <= d+outsz)` by
    (irule abi_valid_allocated_array_output_bounds >>
     qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _` (irule_at Any) >> simp[]) >>
  `d+32+j*mem_sz+type_memory_bytes ce ty <= d+outsz` by
    (qpat_assum `!k. k < LENGTH vs ==> d+32+k*type_memory_size tv+type_memory_size tv <= d+outsz`
       (qspec_then `j` (drule_then mp_tac)) >>
     qpat_assum `mem_sz = type_memory_size tv` SUBST1_TAC >>
     qpat_assum `mem_sz = type_memory_bytes ce ty` (SUBST1_TAC o SYM) >>
     qpat_assum `mem_sz = type_memory_size tv` SUBST1_TAC >>
     simp_tac bool_ss []) >>
  drule_all finite_array_physical_child_entry >>
  disch_then (qx_choosel_then [`a`,`b`,`childpos`] (map_every assume_tac o CONJUNCTS)) >>
  `FLOOKUP a0.vs_allocas inst.inst_id = SOME (slot,32) /\
   (!i. slot <= i /\ i < slot+32 ==> i NOTIN tn0.t_mem)` by
    (conj_tac
     >- (qpat_assum `a0.vs_allocas = s.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `tn0.t_mem = tn.t_mem` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `abi_decoder_operand_live loop_st.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `start.cs_next_var` >>
     simp_tac bool_ss [] >>
     qpat_assum `abi_malformed_entry _ _ _ _ _ _ start _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_malformed_entry_def,EVERY_DEF] >> strip_tac >>
     asm_simp_tac bool_ss []) >>
  `!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
     op_prov G0 op = op_prov G op /\ op_taint tn0 op = op_taint tn op` by
    (Cases >> TRY (rename1 `abi_decoder_operand_live _ (Var x) ==> _` >>
       qpat_assum `!x. abi_decoder_operand_live loop_st.cs_next_var (Var x) ==> _`
         (qspec_then `x` mp_tac) >> simp[op_prov_def] >> NO_TAC) >>
     simp[op_prov_def,op_taint_def]) >>
  `op_prov G0 src = NONE /\ op_taint tn0 src = {} /\
   op_prov G0 hi = NONE /\ op_taint tn0 hi = {}` by
    (qpat_assum `!op. abi_decoder_operand_live loop_st.cs_next_var op ==> _`
       (fn th => map_every (fn q => qspec_then q mp_tac th) [`src`,`hi`]) >>
     asm_simp_tac bool_ss []) >>
  `32+j*mem_sz+mem_sz <= outsz` by
    (qpat_assum `d+32+j*mem_sz+type_memory_bytes ce ty <= d+outsz` mp_tac >>
     qpat_assum `mem_sz = type_memory_bytes ce ty` (SUBST1_TAC o SYM) >>
     simp_tac bool_ss [GSYM ADD_ASSOC,LE_ADD_LCANCEL]) >>
  drule_all finite_array_setup_child_joint >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`GB`,`tnB`,`outB`] (map_every assume_tac o CONJUNCTS))) >>
  `abi_valid_allocated_entry H ce env sf ty tv (EL j vs) ctx func cenv cx es
     child child_end (Var source) hi (FST (SND ops)) (Var outB) B L xs childpos
     (d+32+j*mem_sz) dstid live ceiling b` by
    (qpat_assum `SND (SND ops) = Var outB` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `ptr_covers GB tnB outB b (type_memory_bytes ce ty)` by
    (qpat_assum `mem_sz = type_memory_bytes ce ty` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `loop_st.cs_next_var <= child.cs_next_var` by
    (qpat_assum `setup.cs_next_var <= child.cs_next_var` mp_tac >>
     qpat_assum `setup.cs_next_var = loop_st.cs_next_var + 5` SUBST1_TAC >>
     simp_tac arith_ss []) >>
  `abi_decoder_operand_live child.cs_next_var (Var output) /\
   abi_decoder_operand_live child.cs_next_var (Var ip)` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `loop_st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live child.cs_next_var (Var (STRING #"%" (toString setup.cs_next_var))) /\
   op_prov GB (Var (STRING #"%" (toString setup.cs_next_var))) = NONE /\
   op_taint tnB (Var (STRING #"%" (toString setup.cs_next_var))) = {}` by
    (qpat_assum `FST ops = Var _` (SUBST1_TAC o SYM) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (* Match the enclosing destination before the other coverage premises. *)
  qpat_assum `ptr_covers GB tnB output b outsz`
    (mp_then (Pos (el 13)) drule_all finite_array_decode_child_joint) >>
  disch_then (qspec_then `PG`
    (qx_choosel_then [`u`,`GU`,`tnU`] (map_every assume_tac o CONJUNCTS))) >>
  qhdtm_assum `abi_valid_allocated_post`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_allocated_post_def]) >>
  `FLOOKUP b.vs_allocas inst.inst_id = SOME (slot,32)` by
    (qpat_assum `b.vs_allocas = a0.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm (qx_choose_then `cap` strip_assume_tac))
    `?cap. FLOOKUP b.vs_allocas live = SOME (B,cap) /\ L <= cap /\
           B+L < dimword (:256) /\ live <> inst.inst_id`
  >- (qpat_assum `b.vs_allocas = a0.vs_allocas` SUBST1_TAC >>
      qpat_assum `abi_malformed_entry _ _ _ _ _ _ setup sites _ live _ _ _ _ B L xs _ _ _ a0`
        (mp_tac o REWRITE_RULE [abi_malformed_entry_def,abi_malformed_allocated_window_def]) >>
      strip_tac >> qexists_tac `cap` >> simp_tac bool_ss [] >> metis_tac[]) >>
  `eval_operand (Var (STRING #"%" (toString setup.cs_next_var))) b = SOME (n2w j)` by
    (qpat_assum `FST ops = Var _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
     op <> Var (STRING #"%" (toString child_end.cs_next_var))` by
    (rpt strip_tac >>
     `loop_st.cs_next_var <= child_end.cs_next_var` by
       metis_tac[LESS_EQ_TRANS] >>
     metis_tac[abi_decoder_live_excludes_output]) >>
  qmatch_asmsub_abbrev_tac `lookup_block hdr func.fn_blocks = SOME hdr_bb` >>
  `phi_prefix_length hdr_bb.bb_instructions = 0` by
    simp[Abbr `hdr_bb`,abi_decode_position_header_insts_def,phi_prefix_length_def,mk_inst_def] >>
  qmatch_asmsub_abbrev_tac `lookup_block child_end.cs_current_bb func.fn_blocks = SOME tail_bb` >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME tail_bb /\
   tail_bb.bb_instructions = child_end.cs_current_insts ++
     abi_decode_backedge_insts child_end.cs_next_id (STRING #"%" (toString setup.cs_next_var))
       (STRING #"%" (toString child_end.cs_next_var)) (Var ip) hdr` by
    simp[Abbr `tail_bb`] >>
  qabbrev_tac `t = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString child_end.cs_next_var)) (n2w (SUC j)) u))` >>
  `t = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString child_end.cs_next_var)) (n2w (SUC j)) u))` by
    simp[Abbr `t`] >>
  `ip <> STRING #"%" (toString child_end.cs_next_var) /\
   source <> STRING #"%" (toString child_end.cs_next_var) /\
   output <> STRING #"%" (toString child_end.cs_next_var)` by
    (rpt conj_tac >> qpat_assum `!op. abi_decoder_operand_live loop_st.cs_next_var op ==> _`
       (fn th => irule (SIMP_RULE (srw_ss()) [] (Q.SPEC `Var x` th))) >> simp[]) >>
  drule_all finite_array_child_backedge >>
  disch_then (qspec_then `PG` mp_tac) >>
  disch_then (qx_choosel_then [`Gstep`,`tnT`] (map_every assume_tac o CONJUNCTS)) >>
  `eval_operand (Var (STRING #"%" (toString setup.cs_next_var))) u = SOME (n2w j) /\
   eval_operand (Var ip) u = SOME (n2w slot)` by
    (qpat_assum `abi_malformed_resource_post _ _ _ _ _ child.cs_next_var _ _ b u`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     metis_tac[]) >>
  `abi_decode_sim ctx func u t` by
    (`Var ip <> Var (STRING #"%" (toString child_end.cs_next_var))` by simp[] >>
     qpat_assum `eval_operand (Var (STRING #"%" _)) u = SOME (n2w j)`
       (mp_then (Pos (el 7)) drule_all abi_decode_backedge_sim) >>
     qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     disch_then (qspec_then `ctx` mp_tac) >>
     `w2n (n2w slot:bytes32) = slot` by simp[w2n_n2w] >>
     qpat_assum `w2n (n2w slot:bytes32) = slot` (rewrite_tac o single)) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz s a0` by
    (pure_rewrite_tac[abi_valid_allocated_effect_def,abi_valid_allocated_frame_def] >>
     qpat_assum `a0.vs_memory = s.vs_memory` SUBST1_TAC >>
     qpat_assum `a0.vs_allocas = s.vs_allocas` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> simp_tac bool_ss []) >>
  `abi_valid_allocated_effect ctx func cenv cx es setup.cs_next_var
     sites dstid d outsz a0 b` by
    (pure_rewrite_tac[abi_valid_allocated_effect_def,abi_valid_allocated_frame_def] >>
     qpat_assum `b.vs_memory = a0.vs_memory` SUBST1_TAC >>
     qpat_assum `b.vs_allocas = a0.vs_allocas` SUBST1_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> simp_tac bool_ss []) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz a0 b` by
    (irule abi_valid_allocated_effect_weaken >>
     qpat_assum `abi_valid_allocated_effect _ _ _ _ _ setup.cs_next_var _ _ _ _ a0 b`
       (irule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz b u` by
    (pure_rewrite_tac[abi_valid_allocated_effect_def] >> conj_tac
     >- (irule abi_malformed_resource_weaken >>
         qpat_assum `abi_malformed_resource_post _ _ _ _ _ child.cs_next_var _ _ b u`
           (irule_at Any) >> conj_tac
         >- (irule LESS_EQ_TRANS >> qexists_tac `setup.cs_next_var` >>
             conj_tac >> first_assum ACCEPT_TAC) >>
         first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_valid_allocated_frame_weaken >>
     qpat_assum `abi_valid_allocated_frame _ _ _ b u` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp_tac arith_ss [])) >>
  `abi_valid_allocated_effect ctx func cenv cx es start.cs_next_var
     sites dstid d outsz s u` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `a0` >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule abi_valid_allocated_effect_trans >> qexists_tac `b` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `EVERY (val_wf tv) vs` by
    (`value_has_type (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))` by
       (irule (cj 1 abi_to_vyper_well_typed) >>
        qpat_assum `abi_to_vyper env (ArrayT _ _) _ = SOME (ArrayV _)` (irule_at Any) >>
        qpat_assum `abi_decoder_coherent _ _ _ (ArrayT _ _) _`
          (mp_tac o MATCH_MP abi_decoder_coherent_header) >>
        simp_tac bool_ss [abi_decoder_header_def]) >>
     pop_assum mp_tac >>
     simp_tac bool_ss [value_has_type_def, all_have_type_EVERY, EVERY_MEM] >>
     metis_tac[cj 1 value_has_type_val_wf]) >>
  `alloca_inv b` by
    (qpat_assum `abi_valid_allocated_entry H ce env sf ty tv (EL j vs) ctx func cenv cx es child child_end _ _ _ _ B L xs childpos _ dstid live ceiling b`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_entry_def,abi_malformed_entry_def]) >>
     drule_then (fn th => ACCEPT_TAC (CONJUNCT2 th)) stmt_state_rel_local_ptrs_alloca) >>
  `abi_valid_allocated_array_prefix tv vs j d b` by
    (pure_rewrite_tac[abi_valid_allocated_array_prefix_def] >>
     map_every (fn p => qpat_assum p SUBST1_TAC)
       [`b.vs_memory = a0.vs_memory`,`a0.vs_memory = s.vs_memory`] >>
     qpat_assum `abi_valid_allocated_array_prefix tv vs j d s`
       (ACCEPT_TAC o PURE_REWRITE_RULE [abi_valid_allocated_array_prefix_def])) >>
  `abi_valid_allocated_array_prefix tv vs (SUC j) d u` by
    (irule abi_valid_allocated_array_child_prefix >>
     qpat_assum `abi_valid_allocated_array_prefix tv vs j d b` (irule_at Any) >>
     qpat_assum `mem_sz = type_memory_size tv` (SUBST1_TAC o SYM) >>
     qpat_assum `abi_valid_allocated_frame (abi_malformed_scratch_sites child child_end func) _ _ b u`
       (irule_at Any) >>
     qpat_assum `abi_malformed_entry H ctx func cenv cx es start sites dstid live _ _ _ _ B L xs p d outsz s`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_entry_def,abi_malformed_destination_def]) >>
     map_every (fn p => qpat_assum p SUBST1_TAC)
       [`b.vs_allocas = a0.vs_allocas`,`a0.vs_allocas = s.vs_allocas`] >>
     qpat_assum `FLOOKUP s.vs_allocas dstid = SOME _` (irule_at Any) >>
     `dstid NOTIN abi_malformed_scratch_sites child child_end func` by
       (qpat_assum `abi_malformed_scratch_sites child child_end func SUBSET sites`
          (mp_tac o PURE_REWRITE_RULE [SUBSET_DEF]) >>
        qpat_assum `dstid NOTIN sites` mp_tac >> metis_tac[]) >>
     `d + (j * mem_sz + 32) <= b' + sz` by
       (qpat_assum `!k. k < LENGTH vs ==> d + 32 + k * type_memory_size tv + _ <= _`
          (qspec_then `j` mp_tac) >>
        qpat_assum `mem_sz = type_memory_size tv` (SUBST1_TAC o SYM) >>
        qpat_assum `j < LENGTH vs` mp_tac >>
        qpat_assum `d + outsz <= b' + sz` mp_tac >>
        simp_tac arith_ss []) >>
     rpt conj_tac >> FIRST_PROVE
       [first_assum ACCEPT_TAC,
        qpat_assum `d + (j * mem_sz + 32) <= b' + sz` mp_tac >>
          simp_tac arith_ss [],
        qpat_assum `val_in_memory tv (EL j vs) _ u.vs_memory` mp_tac >>
          simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]]) >>
  `32 + SUC j * type_memory_size tv <= outsz` by
    (qpat_assum `!k. k < LENGTH vs ==> d + 32 + k * type_memory_size tv + _ <= _`
       (qspec_then `j` mp_tac) >>
     qpat_assum `j < LENGTH vs` mp_tac >> simp_tac arith_ss [MULT]) >>
  `start.cs_next_var <= child_end.cs_next_var /\ child_end.cs_next_var < ceiling.cs_next_var` by
    (conj_tac >- metis_tac[LESS_EQ_TRANS] >>
     qpat_assum `en.cs_next_var = child_end.cs_next_var + 1` mp_tac >>
     qpat_assum `en.cs_next_var <= ceiling.cs_next_var` mp_tac >>
     simp_tac arith_ss []) >>
  `abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
     sites dstid live (Var source) hi src (Var output) B L xs p d outsz
     (Var ip) slot inst q hdr tv vs origin (SUC j) t` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     irule abi_valid_allocated_array_backedge_advance >>
     qpat_assum `abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
       sites dstid live (Var source) hi src (Var output) B L xs p d outsz
       (Var ip) slot inst q hdr tv vs origin j s` (irule_at Any) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `ip <> STRING #"%" _` mp_tac >> simp_tac (srw_ss()) []))) >>
  `?dst_base dst_cap. FLOOKUP b.vs_allocas dstid = SOME (dst_base,dst_cap) /\
              dst_base <= d /\ d + outsz <= dst_base+dst_cap /\ dstid NOTIN sites` by
    (qpat_assum `abi_malformed_entry H ctx func cenv cx es start sites dstid live _ _ _ _ B L xs p d outsz s`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_entry_def,abi_malformed_destination_def]) >>
     map_every (fn p => qpat_assum p SUBST1_TAC)
       [`b.vs_allocas = a0.vs_allocas`,`a0.vs_allocas = s.vs_allocas`] >>
     goal_assum (drule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `FLOOKUP u.vs_allocas dstid = SOME (dst_base,dst_cap) /\
   FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32) /\ alloca_inv u` by
    (qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ b u`
       (strip_assume_tac o PURE_REWRITE_RULE[abi_malformed_resource_post_def]) >>
     rpt conj_tac >> FIRST_PROVE
       [first_x_assum irule >> first_assum ACCEPT_TAC,
        drule_then ACCEPT_TAC abi_malformed_resource_post_alloca_inv]) >>
  `!a. d <= a /\ a < d+outsz ==> a < slot \/ slot+32 <= a` by
    (qx_gen_tac `byte` >> strip_tac >> spose_not_then strip_assume_tac >>
     `dst_base <= byte /\ byte < dst_base+dst_cap /\ slot <= byte /\ byte < slot+32` by
       (qpat_assum `dst_base <= d` mp_tac >> qpat_assum `d+outsz <= dst_base+dst_cap` mp_tac >>
        qpat_assum `d <= byte` mp_tac >> qpat_assum `byte < d+outsz` mp_tac >>
        qpat_assum `~(byte < slot)` mp_tac >> qpat_assum `~(slot+32 <= byte)` mp_tac >>
        simp_tac arith_ss []) >>
     `dstid = inst.inst_id` by
       (irule (cj 1 frameActivationSeparationTheory.alloca_inv_byte_unique) >>
        qpat_assum `FLOOKUP u.vs_allocas dstid = SOME (dst_base,dst_cap)` (irule_at Any) >>
        qpat_assum `FLOOKUP u.vs_allocas inst.inst_id = SOME (slot,32)` (irule_at Any) >>
        qexists_tac `byte` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
       sites dstid live (Var source) hi src (Var output) B L xs p d outsz
       (Var ip) slot inst q hdr tv vs origin j s`
       (strip_assume_tac o PURE_REWRITE_RULE[abi_valid_allocated_array_inv_def]) >>
     qpat_assum `inst.inst_id IN sites` mp_tac >>
     qpat_assum `dstid NOTIN sites` mp_tac >>
     qpat_assum `dstid = inst.inst_id` SUBST1_TAC >> simp_tac bool_ss []) >>
  `!byte. d <= byte /\ byte < d+32+j*mem_sz ==>
          ~(d+32+j*mem_sz <= byte /\ byte < d+32+j*mem_sz+type_memory_bytes ce ty) /\
          ~abi_malformed_site_range (abi_malformed_scratch_sites child child_end func) b u byte 1` by
    (qx_gen_tac `byte` >> strip_tac >> conj_tac >-
       (qpat_assum `byte < d+32+j*mem_sz` mp_tac >> simp_tac arith_ss []) >>
     strip_tac >>
     `dstid NOTIN abi_malformed_scratch_sites child child_end func` by
       (qpat_assum `abi_malformed_scratch_sites child child_end func SUBSET sites`
          (mp_tac o PURE_REWRITE_RULE[SUBSET_DEF]) >>
        qpat_assum `dstid NOTIN sites` mp_tac >> metis_tac[]) >>
     `dst_cap <= dst_cap` by simp[] >>
     `dst_base+dst_cap <= byte \/ byte+1 <= dst_base` by
       (irule abiMalformedSiteFrameTheory.abi_malformed_site_range_protected >>
        qpat_assum `FLOOKUP b.vs_allocas dstid = SOME (dst_base,dst_cap)` (irule_at Any) >>
        qpat_assum `abi_malformed_site_range (abi_malformed_scratch_sites child child_end func) b u byte 1` (irule_at Any) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     FIRST [qpat_assum `dst_base+dst_cap <= byte` mp_tac,
            qpat_assum `byte+1 <= dst_base` mp_tac] >>
     map_every (fn p => qpat_assum p mp_tac)
       [`dst_base <= d`,
        `d+outsz <= dst_base+dst_cap`, `d <= byte`, `byte < d+32+j*mem_sz`,
        `32 + SUC j * type_memory_size tv <= outsz`] >>
     qpat_assum `mem_sz = type_memory_size tv` (SUBST1_TAC o SYM) >>
     simp_tac arith_ss [MULT]) >>
  `!byte. d <= byte /\ byte < d+outsz ==>
     mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 u.vs_memory /\
     (byte IN tnT.t_mem <=> byte IN tnU.t_mem)` by
    (qx_gen_tac `byte` >> strip_tac >>
     Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac) `byte < slot \/ slot+32 <= byte`
     >- (qpat_assum `!a. d <= a /\ _ ==> a < slot \/ _`
           (qspec_then `byte` mp_tac) >> asm_simp_tac bool_ss []) >>
     conj_tac >-
       (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
        simp_tac (srw_ss()) [jump_to_def] >>
        drule abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside >>
        simp_tac (srw_ss()) [update_var_def]) >>
     qpat_assum `!i. i < slot \/ _ ==> (i IN tnT.t_mem <=> _)`
       (qspec_then `byte` mp_tac) >> asm_simp_tac bool_ss []) >>
  `!byte. d <= byte /\ byte < d+32+j*mem_sz ==>
     mem_bytes_at byte 1 u.vs_memory = mem_bytes_at byte 1 s.vs_memory /\
     (byte IN tnU.t_mem <=> byte IN tn.t_mem)` by
    (qx_gen_tac `byte` >> strip_tac >>
     qpat_assum `!i. d <= i /\ i < d+32+j*mem_sz ==> _`
       (qspec_then `byte` mp_tac) >>
     (impl_tac >- asm_simp_tac bool_ss []) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >-
       (map_every (fn p => qpat_assum p (SUBST1_TAC o SYM))
          [`a0.vs_memory = s.vs_memory`,`b.vs_memory = a0.vs_memory`] >>
        irule abi_valid_allocated_frame_slice >>
        qpat_assum `abi_valid_allocated_frame _ _ _ b u` (irule_at Any) >>
        `!i. byte <= i /\ i < byte+1 ==> i = byte` by simp_tac arith_ss [] >>
        gen_tac >> strip_tac >>
        qpat_assum `!i. byte <= i /\ i < byte+1 ==> _` drule_all >>
        disch_then SUBST1_TAC >> conj_tac >> first_assum ACCEPT_TAC) >>
     map_every (fn p => qpat_assum p (SUBST1_TAC o SYM))
       [`tn0.t_mem = tn.t_mem`,`tnB.t_mem = tn0.t_mem`] >>
     qpat_assum `!a. _ /\ ~abi_malformed_site_range _ b u a 1 ==> _`
       (qspec_then `byte` irule) >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!byte. d <= byte /\ byte < d+32+j*mem_sz ==>
     mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 s.vs_memory /\
     (byte IN tnT.t_mem <=> byte IN tn.t_mem)` by
    (qx_gen_tac `byte` >> strip_tac >>
     `byte < d+outsz` by
       (map_every (fn p => qpat_assum p mp_tac)
          [`byte < d+32+j*mem_sz`,`32 + SUC j * type_memory_size tv <= outsz`] >>
        qpat_assum `mem_sz = type_memory_size tv` (SUBST1_TAC o SYM) >>
        simp_tac arith_ss [MULT]) >>
     MAP_EVERY (fn p => qpat_assum p (qspec_then `byte` mp_tac) >>
       (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
       disch_then (map_every assume_tac o CONJUNCTS))
       [`!i. d <= i /\ i < d+outsz ==> _`,
        `!i. d <= i /\ i < d+32+j*mem_sz ==>
           mem_bytes_at i 1 u.vs_memory = _ /\ _`] >>
     conj_tac >- metis_tac[] >>
     qpat_assum `(byte IN tnT.t_mem) = _` (SUBST1_TAC) >> first_assum ACCEPT_TAC) >>
  `!byte. d <= byte /\ byte < d+32 ==> byte NOTIN tnT.t_mem` by
    (drule representationCleanPtrTheory.robust_mem_word_at_clean >>
     disch_then (fn th => qx_gen_tac `byte` >> strip_tac >> qspec_then `byte` mp_tac th) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `!i. d <= i /\ i < d+32+j*mem_sz ==>
         mem_bytes_at i 1 t.vs_memory = _ /\ _` (qspec_then `byte` mp_tac) >>
     (impl_tac >- (qpat_assum `byte < d+32` mp_tac >>
        qpat_assum `d <= byte` mp_tac >> simp_tac arith_ss [])) >>
     simp_tac bool_ss []) >>
  `!m. mem_agree_outside tnT.t_mem t.vs_memory m ==>
     mem_word_at d m = n2w (LENGTH vs)` by
    (qx_gen_tac `m` >> disch_tac >>
     `mem_bytes_at d 32 m = mem_bytes_at d 32 t.vs_memory` by
       (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
        qpat_assum `mem_agree_outside tnT.t_mem t.vs_memory m`
          (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.mem_agree_outside_def]) >>
        qpat_assum `!i. d <= i /\ _ ==> i NOTIN tnT.t_mem` mp_tac >> metis_tac[]) >>
     qpat_assum `abi_valid_allocated_array_inv H ctx func cenv cx es start ceiling
        sites dstid live (Var source) hi src (Var output) B L xs p d outsz
        (Var ip) slot inst q hdr tv vs origin (SUC j) t`
       (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT1 o CONJUNCT2 o
        PURE_REWRITE_RULE [abi_valid_allocated_array_inv_def,abi_valid_allocated_array_prefix_def]) >>
     qpat_assum `mem_bytes_at d 32 m = _` (fn th =>
       simp_tac bool_ss [abiStaticAggregatePropsTheory.mem_word_at_bytes,th])) >>
  `!k tm before.
     k < LENGTH vs /\
     (!byte. d+32+k*type_memory_size tv <= byte /\
             byte < d+32+k*type_memory_size tv+type_memory_size tv ==>
        mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 before /\
        (byte IN tnT.t_mem <=> byte IN tm)) /\
     (!m. mem_agree_outside tm before m ==>
          val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) m) ==>
     !m. mem_agree_outside tnT.t_mem t.vs_memory m ==>
         val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) m` by
    (map_every qx_gen_tac [`k`,`tm`,`before`] >> strip_tac >>
     `val_wf tv (EL k vs)` by
       (qpat_assum `EVERY (val_wf tv) vs` mp_tac >>
        rewrite_tac[EVERY_EL] >> disch_then irule >> first_assum ACCEPT_TAC) >>
     qx_gen_tac `m` >> disch_tac >>
     irule robustCopyTransportPtrTheory.robust_val_in_memory_copy_transport >>
     qpat_assum `mem_agree_outside tnT.t_mem t.vs_memory m` (irule_at Any) >>
     qexistsl [`tm`,`d+32+k*type_memory_size tv`,`type_memory_size tv`,`before`] >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- (qx_gen_tac `i` >> disch_tac >>
         qpat_assum `!byte. _ ==> mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 before /\ _`
           (qspec_then `d+32+k*type_memory_size tv+i` mp_tac) >>
         qpat_assum `i < type_memory_size tv` mp_tac >> simp_tac arith_ss [])
     >- (irule exprSimPropsTheory.val_footprint_le >> first_assum ACCEPT_TAC) >>
     irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
     qx_gen_tac `byte` >> strip_tac >>
     qpat_assum `!byte. _ ==> mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 before /\ _`
       (qspec_then `byte` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
  `!k m. k < SUC j /\ mem_agree_outside tnT.t_mem t.vs_memory m ==>
     val_in_memory tv (EL k vs) (d+32+k*type_memory_size tv) m` by
    (map_every qx_gen_tac [`k`,`m`] >> strip_tac >>
     Cases_on `k < j` >-
       (`SUC k * type_memory_size tv <= j * type_memory_size tv` by
          (simp_tac bool_ss [LE_MULT_RCANCEL] >>
           qpat_assum `k < j` mp_tac >> simp_tac arith_ss []) >>
        qpat_assum `!k tm before. _ ==> !m. mem_agree_outside tnT.t_mem t.vs_memory m ==> _`
          (qspecl_then [`k`,`tn.t_mem`,`s.vs_memory`] mp_tac) >>
        (impl_tac >-
          (conj_tac >-
             (map_every (fn p => qpat_assum p mp_tac)
               [`k < j`,`j < LENGTH vs`] >> simp_tac arith_ss []) >>
           conj_tac >-
             (qx_gen_tac `byte` >> strip_tac >>
              qpat_assum `!byte. d <= byte /\ byte < d+32+j*mem_sz ==>
                  mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 s.vs_memory /\ _`
                (qspec_then `byte` irule) >>
              map_every (fn p => qpat_assum p mp_tac)
                [`SUC k * type_memory_size tv <= j * type_memory_size tv`,
                 `byte < d+32+k*type_memory_size tv+type_memory_size tv`,
                 `d+32+k*type_memory_size tv <= byte`] >>
              qpat_assum `mem_sz = type_memory_size tv` SUBST1_TAC >>
              simp_tac bool_ss [MULT] >>
              map_every qabbrev_tac [`ki = k*type_memory_size tv`,
                `ji = j*type_memory_size tv`,`sz = type_memory_size tv`] >>
              simp_tac arith_ss []) >>
           qx_gen_tac `mem` >> disch_tac >>
           qpat_assum `!k m. k < j /\ mem_agree_outside tn.t_mem s.vs_memory m ==> _`
             (qspecl_then [`k`,`mem`] irule) >> conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then (qspec_then `m` irule) >> first_assum ACCEPT_TAC) >>
     `k = j` by (map_every (fn p => qpat_assum p mp_tac)
       [`~(k < j)`,`k < SUC j`] >> simp_tac arith_ss []) >>
     qpat_assum `k = j` SUBST1_TAC >>
     qpat_assum `!k tm before. _ ==> !m. mem_agree_outside tnT.t_mem t.vs_memory m ==> _`
       (qspecl_then [`j`,`tnU.t_mem`,`u.vs_memory`] mp_tac) >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >-
          (qx_gen_tac `byte` >> strip_tac >>
           qpat_assum `!byte. d <= byte /\ byte < d+outsz ==>
             mem_bytes_at byte 1 t.vs_memory = mem_bytes_at byte 1 u.vs_memory /\ _`
             (qspec_then `byte` irule) >>
           map_every (fn p => qpat_assum p mp_tac)
             [`32 + SUC j * type_memory_size tv <= outsz`,
              `byte < d+32+j*type_memory_size tv+type_memory_size tv`,
              `d+32+j*type_memory_size tv <= byte`] >> simp_tac arith_ss [MULT]) >>
        qpat_assum `mem_sz = type_memory_size tv` (SUBST1_TAC o SYM) >>
        first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `m` irule) >> first_assum ACCEPT_TAC) >>
  `!x. abi_decoder_operand_live loop_st.cs_next_var (Var x) ==>
     FLOOKUP Gstep x = FLOOKUP G0 x /\
     op_taint tnT (Var x) = op_taint tn0 (Var x)` by
    (qx_gen_tac `x` >> disch_tac >>
     `abi_decoder_operand_live setup.cs_next_var (Var x)` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `loop_st.cs_next_var` >> simp[]) >>
     `abi_decoder_operand_live child.cs_next_var (Var x)` by
       (irule abi_decoder_operand_live_mono >>
        qexists_tac `loop_st.cs_next_var` >> simp[]) >>
     `x <> STRING #"%" (toString child_end.cs_next_var)` by
       (qpat_assum `!op. abi_decoder_operand_live loop_st.cs_next_var op ==> op <> _`
          (qspec_then `Var x` mp_tac) >> simp[]) >>
     qpat_assum `!x. _ ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. _ ==> FLOOKUP GU x = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `!x. _ ==> lookup_var x b = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
      op_prov Gstep op = op_prov G op /\ op_taint tnT op = op_taint tn op` by
    (qx_gen_tac `op` >> disch_tac >>
     qpat_assum `!op. _ ==> op_prov G0 op = _ /\ _`
       (qspec_then `op` mp_tac) >>
     Cases_on `op` >> simp[op_prov_def,op_taint_def] >>
     qpat_assum `!x. _ ==> FLOOKUP Gstep x = _ /\ _` mp_tac >>
     simp[op_taint_def]) >>
  `op_prov Gstep src = NONE /\ op_taint tnT src = {} /\
   op_prov Gstep hi = NONE /\ op_taint tnT hi = {}` by
    (qpat_assum `!op. _ ==> op_prov Gstep op = _ /\ _`
       (fn th => qspec_then `src` mp_tac th >> qspec_then `hi` mp_tac th) >> simp[]) >>
  `LENGTH vs - SUC j < v` by
    (map_every (fn p => qpat_assum p mp_tac)
       [`v = LENGTH vs - j`,`j < LENGTH vs`] >> simp_tac arith_ss []) >>
  `SUC j <= LENGTH vs` by
    (qpat_assum `j < LENGTH vs` mp_tac >> simp_tac arith_ss []) >>
  qpat_assum `!m. m < v ==> _` (qspec_then `LENGTH vs - SUC j` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`vs`,`SUC j`] mp_tac) >>
  (impl_tac >- REFL_TAC) >>
  ntac 5 (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`t`,`Gstep`,`tnT`] mp_tac) >>
  ntac 15 (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `h` (qx_choose_then `GH` (qx_choose_then `tnH` strip_assume_tac))) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK h,GH,tnH)` by
    (map_every qx_gen_tac [`D`,`explicit`] >>
     map_every (fn p =>
       irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
       qpat_assum p (qspecl_then [`D`,`explicit`] (irule_at Any)))
       [`!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK a0,G0,tn0)`,
        `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a0,G0,tn0) [] (OK b,GB,tnB)`,
        `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (b,GB,tnB) [] (OK u,GU,tnU)`,
        `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,GU,tnU) [] (OK t,Gstep,tnT)`] >>
     qpat_assum `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gstep,tnT) [] (OK h,GH,tnH)`
       (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  qexistsl_tac [`h`,`GH`,`tnH`] >>
  `t.vs_accounts = u.vs_accounts /\ t.vs_transient = u.vs_transient /\
   t.vs_call_ctx = u.vs_call_ctx /\ t.vs_immutables = u.vs_immutables` by
    (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
     simp[NoAsms,jump_to_def,mstore_def,update_var_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists_tac `a0` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists_tac `b` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists_tac `u` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      irule abiDecoderLoopTheory.abi_decode_sim_trans >> qexists_tac `t` >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  TRY (goal_term (fn tm =>
    if boolSyntax.is_eq tm then asm_simp_tac bool_ss [] >> NO_TAC else NO_TAC)) >>
  all_tac >-
    (`t.vs_alloca_next <= h.vs_alloca_next` by
       (qpat_assum `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gstep,tnT) [] (OK h,GH,tnH)`
          (mp_tac o SPEC_ALL) >>
        disch_then (mp_tac o CONJUNCT2 o MATCH_MP gas_origin_ptr_path_projections) >>
        disch_then (mp_tac o MATCH_MP fragGasPathPtrTheory.gas_path_ptr_erase) >>
        disch_then (mp_tac o MATCH_MP bodyMemBopRestWordPathTheory.rest_word_path_frontier) >>
        simp_tac bool_ss []) >>
     `t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next` by
       (qpat_assum `t = jump_to _ _` SUBST1_TAC >>
        simp[NoAsms,jump_to_def,mstore_def,update_var_def]) >>
     `b.vs_allocas = s.vs_allocas /\ b.vs_alloca_next = s.vs_alloca_next` by
       (conj_tac
        >- (qpat_assum `b.vs_allocas = a0.vs_allocas` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
        qpat_assum `b.vs_alloca_next = a0.vs_alloca_next` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
     `s.vs_alloca_next <= t.vs_alloca_next` by
       (qpat_assum `t.vs_alloca_next = u.vs_alloca_next` SUBST1_TAC >>
        qpat_assum `b.vs_alloca_next = s.vs_alloca_next` (SUBST1_TAC o SYM) >>
        qpat_assum `abi_malformed_resource_post _ _ _ _ _ child.cs_next_var _ _ b u`
          (mp_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >> simp_tac bool_ss []) >>
     `alloca_inv t` by
       (rewrite_tac[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def] >>
        map_every (fn p => qpat_assum p SUBST1_TAC)
          [`t.vs_allocas = u.vs_allocas`,`t.vs_alloca_next = u.vs_alloca_next`] >>
        qpat_assum `alloca_inv u` (mp_tac o PURE_REWRITE_RULE
          [alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def]) >>
        simp_tac bool_ss []) >>
     `!id base size. FLOOKUP t.vs_allocas id = SOME (base,size) ==>
        FLOOKUP s.vs_allocas id = SOME (base,size) \/ s.vs_alloca_next <= base` by
       (qpat_assum `t.vs_allocas = u.vs_allocas` SUBST1_TAC >>
        qpat_assum `abi_valid_allocated_effect _ _ _ _ _ _ _ _ _ _ s u`
          (mp_tac o PURE_REWRITE_RULE [abi_valid_allocated_effect_def]) >> simp_tac bool_ss []) >>
     qx_gen_tac `byte` >> disch_then (CONJUNCTS_THEN assume_tac) >>
     `~abi_malformed_site_range sites t h byte 1` by
       (strip_tac >>
        qpat_x_assum `abi_malformed_site_range sites t h byte 1`
          (DISJ_CASES_THEN2 (qx_choosel_then [`site_id`,`site_base`,`site_sz`] strip_assume_tac)
            strip_assume_tac o PURE_REWRITE_RULE [abiMalformedSiteFrameTheory.abi_malformed_site_range_def]) >>
        qpat_x_assum `~abi_malformed_site_range sites s h byte 1` mp_tac >>
        simp_tac bool_ss [] >>
        rewrite_tac[abiMalformedSiteFrameTheory.abi_malformed_site_range_def]
        >- (`site_base+site_sz <= t.vs_alloca_next` by
              (irule alloca_site_registered_below >> conj_tac
               >- first_assum ACCEPT_TAC >>
               qexists_tac `site_id` >> first_assum ACCEPT_TAC) >>
            qpat_assum `!id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==> _`
              (qspecl_then [`site_id`,`site_base`,`site_sz`] mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
            >- (disj1_tac >> qexistsl_tac [`site_id`,`site_base`,`site_sz`] >>
                conj_tac >- first_assum ACCEPT_TAC >>
                conj_tac >- first_assum ACCEPT_TAC >>
                conj_tac >> first_assum ACCEPT_TAC) >>
            disj2_tac >>
            map_every (fn p => qpat_assum p mp_tac)
              [`s.vs_alloca_next <= site_base`,`site_base <= byte`, `byte + 1 <= site_base+site_sz`,
               `site_base+site_sz <= t.vs_alloca_next`,`t.vs_alloca_next <= h.vs_alloca_next`] >>
            simp_tac arith_ss []) >>
        disj2_tac >>
        map_every (fn p => qpat_assum p mp_tac)
          [`s.vs_alloca_next <= t.vs_alloca_next`, `t.vs_alloca_next <= byte`,
           `byte+1 <= h.vs_alloca_next`] >> simp_tac arith_ss []) >>
     `~abi_malformed_site_range (abi_malformed_scratch_sites child child_end func) b u byte 1` by
       (qpat_assum `~abi_malformed_site_range sites s h byte 1` mp_tac >>
        qpat_assum `abi_malformed_scratch_sites child child_end func SUBSET sites` mp_tac >>
        qpat_assum `t.vs_alloca_next <= h.vs_alloca_next` mp_tac >>
        simp_tac bool_ss [abiMalformedSiteFrameTheory.abi_malformed_site_range_def,SUBSET_DEF] >>
        map_every (fn p => qpat_assum p SUBST1_TAC)
          [`b.vs_allocas = s.vs_allocas`,`b.vs_alloca_next = s.vs_alloca_next`] >>
        qpat_assum `t.vs_alloca_next = u.vs_alloca_next` (SUBST1_TAC o SYM) >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        disch_tac >> disch_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
        conj_tac >- metis_tac[] >>
        map_every (fn p => qpat_assum p mp_tac)
          [`t.vs_alloca_next <= h.vs_alloca_next`,
           `~(s.vs_alloca_next <= byte) \/ ~(byte+1 <= h.vs_alloca_next)`] >>
        numLib.ARITH_TAC) >>
     `byte < slot \/ slot+32 <= byte` by
       (spose_not_then strip_assume_tac >>
        qpat_x_assum `~abi_malformed_site_range sites s h byte 1` mp_tac >>
        simp_tac bool_ss [abiMalformedSiteFrameTheory.abi_malformed_site_range_def] >>
        disj1_tac >> qexistsl_tac [`inst.inst_id`,`slot`,`32`] >>
        map_every (fn p => qpat_assum p mp_tac)
          [`inst.inst_id IN sites`,`FLOOKUP s.vs_allocas inst.inst_id = SOME (slot,32)`,
           `~(byte < slot)`, `~(slot+32 <= byte)`] >>
        simp_tac arith_ss []) >>
     `~(d+32+j*mem_sz <= byte /\ byte < d+32+j*mem_sz+type_memory_bytes ce ty)` by
       (map_every (fn p => qpat_assum p mp_tac)
         [`d+32+j*mem_sz+type_memory_bytes ce ty <= d+outsz`,
          `~(d <= byte) \/ ~(byte < d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)))`] >>
        qpat_assum `outsz = _` SUBST1_TAC >> simp_tac arith_ss []) >>
     qpat_assum `!a. _ /\ ~abi_malformed_site_range sites t h a 1 ==> _`
       (qspec_then `byte` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `!a. _ /\ ~abi_malformed_site_range _ b u a 1 ==> _`
       (qspec_then `byte` mp_tac) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `!a. a < slot \/ _ ==> (a IN tnT.t_mem <=> _)`
       (qspec_then `byte` mp_tac) >>
     (impl_tac >- asm_simp_tac bool_ss []) >>
     map_every (fn p => qpat_assum p SUBST1_TAC)
       [`tnB.t_mem = tn0.t_mem`,`tn0.t_mem = tn.t_mem`] >>
     tautLib.TAUT_TAC) >>
  qx_gen_tac `x` >> disch_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var (Var x)` by
    (irule abi_decoder_operand_live_mono >>
     qexists_tac `start.cs_next_var` >> simp[]) >>
  `x <> STRING #"%" (toString child_end.cs_next_var)` by
    (qpat_assum `!op. abi_decoder_operand_live loop_st.cs_next_var op ==> op <> _`
       (qspec_then `Var x` mp_tac) >> simp[]) >>
  qpat_assum `!x. abi_decoder_operand_live start.cs_next_var (Var x) ==>
    (!w. lookup_var x t = SOME w ==> lookup_var x h = SOME w) /\
    FLOOKUP GH x = FLOOKUP Gstep x /\ op_taint tnH (Var x) = op_taint tnT (Var x)`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!op. abi_decoder_operand_live loop_st.cs_next_var op ==>
    op_prov Gstep op = op_prov G op /\ op_taint tnT op = op_taint tn op`
    (qspec_then `Var x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [op_prov_def] >> strip_tac >>
  `lookup_var x t = lookup_var x u` by
    (qpat_assum `!x. _ ==> lookup_var x t = lookup_var x u /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  simp[] >> qx_gen_tac `w` >> disch_tac >>
  `eval_operand (Var x) u = SOME w` by
    (qpat_assum `abi_valid_allocated_effect _ _ _ _ _ _ _ _ _ _ s u`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_valid_allocated_effect_def]) >>
     qpat_assum `abi_malformed_resource_post _ _ _ _ _ start.cs_next_var _ _ s u`
       (mp_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     disch_then (fn th => irule (List.last (CONJUNCTS th))) >> simp[eval_operand_def]) >>
  qpat_assum `!w. lookup_var x t = SOME w ==> lookup_var x h = SOME w`
    (qspec_then `w` irule) >>
  qpat_assum `lookup_var x t = lookup_var x u` SUBST1_TAC >>
  qpat_assum `eval_operand (Var x) u = SOME w`
    (ACCEPT_TAC o REWRITE_RULE [eval_operand_def])
QED

Finalise abi_valid_allocated_finite_loop_joint
