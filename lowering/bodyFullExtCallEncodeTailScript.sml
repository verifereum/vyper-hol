(* Finish packing a direct ABI request from its encoded length. *)
Theory bodyFullExtCallEncodeTail
Ancestors
  abiEncoderWindowSequence abiEncoderWindowPhase abiEncoderWindowJoint abiEncoderWindowJointPhases abiEncoderSourceRobust abiEncoderSourceInvoke
  abiEncoderWindowContract abiEncoderRegisteredEffect abiEncoderCounters
  entryDecodeStructure reasonCopySourcePtr assignTuplePtrCopyLen
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic exprSimAbiEncodeStateTransport
  exprSimAbiEncodeSiteResources
  abiEncoderProps abiAllocationHistory bodyFullAttributeAdd bodyFullPathHistory
  allocaHistory localPtrsProps allocaSiteResource memoryReadProps
  fragGasOriginPtrLoop fragGasOriginPtr loweringShapeRules loweringShapeDefs
  exprLoweringProps fragExec logAbiPrefixPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun compileEnv emitHelper emitHelperProps
  venomExecSemantics venomInst venomState venomMemDefs contractABI valueEncoding vyperABI
  words arithmetic list pred_set finite_map

(* Arithmetic changes only the result variable and the instruction index. *)
Theorem extcall_tail_add[local]:
  !k p. emit_op ADD [left; Lit (n2w k)] a = (out,b) /\ fn_has_code a b func /\
  eval_operand left s = SOME (n2w p) /\ op_taint tn left = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  !G PG. ?q t G' tn'. out = Var q /\ not_fresh_at b q /\
    lookup_var q t = SOME (n2w (p + k)) /\ op_taint tn' out = {} /\
    FLOOKUP G' q = op_prov G left /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_initial_fmp = s.vs_initial_fmp /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame func s t /\
    (alloca_inv s /\ alloca_room ctx func s ==> window_phase ctx func a b {} [] s t) /\
    (!ids outs. abi_encoder_registered_effect ids outs s t) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> drule emit_op_facts >> strip_tac >>
  `out' = STRING #"%" (toString a.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  qabbrev_tac `inst = mk_inst a.cs_next_id ADD [left; Lit (n2w k)] [out']` >>
  qabbrev_tac `u = update_var out' (n2w (p + k)) s` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G inst u` >>
  qabbrev_tac `tn1 = step_taint inst s u tn` >>
  `out = Var out' /\
   (!D l explicit. allocas_from l s ==>
      gas_origin_ptr_path (D,l,explicit,ctx,func,PG) (s,G,tn) []
        (OK v,G1,tn1)) /\
   FLOOKUP G1 out' = op_prov G left /\ op_taint tn1 out = {} /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
   (!x. x <> out' ==> FLOOKUP G1 x = FLOOKUP G x /\
     op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (irule attribute_add_full_frame >>
     simp[Abbr `inst`, Abbr `u`, Abbr `v`, Abbr `G1`, Abbr `tn1`, word_add_n2w] >>
     qexists_tac `n2w k` >> simp[word_add_n2w] >>
     qexistsl [`a`, `b`] >> simp[]) >>
  `alloca_inv s /\ alloca_room ctx func s ==> window_phase ctx func a b {} [] s v` by
    (strip_tac >>
     `eval_operand (Lit (n2w k)) s = SOME (n2w k)` by simp[eval_operand_def] >>
     drule_all window_emit_add_pure >> strip_tac >>
     rename1 `window_pure_seq a b s raw` >>
     `raw = u` by
       (drule_then (assume_tac o cj 1) emitted_insts_emit_op >>
        qpat_assum `window_pure_seq a b s raw`
          (mp_tac o cj 1 o REWRITE_RULE [window_pure_seq_def, window_seq_def]) >>
        simp[Abbr `u`, Abbr `inst`, run_inst_seq_def, step_inst_base_opcode_eqs,
             mk_inst_def, exec_pure2_def, eval_operands_def, word_add_n2w]) >>
     `LENGTH b.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     qpat_assum `window_pure_seq a b s raw`
       (mp_then (Pos hd) (qspecl_then [`[]`,`{}`,`func`,`ctx`] mp_tac)
         window_pure_seq_phase) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `raw = u` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `LENGTH b.cs_current_insts = SUC s.vs_inst_idx`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qunabbrev_tac `v` >> REWRITE_TAC []) >>
  qexistsl [`out'`, `v`, `G1`, `tn1`] >>
  simp[Abbr `v`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
       abi_encode_exec_frame_def, abi_encode_semantic_obs_def,
       pending_alloca_size_def, abi_encoder_registered_effect_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* A covered offset within the shared buffer, before or after encoding. *)
Theorem extcall_tail_offset[local]:
  emit_op ADD [Var root;Lit (n2w k)] a = (dst,b) /\
  fn_has_code a b fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  lookup_var root s = SOME (n2w p) /\
  ptr_covers G tn root s capacity /\ k+n <= capacity /\
  p+k < dimword (:256) ==>
  !explicit PG. ?x t G' tn'. dst = Var x /\
    lookup_var x t = SOME (n2w (p+k)) /\ ptr_covers G' tn' x t n /\
    not_fresh_at b x /\ a.cs_next_var <= b.cs_next_var /\
    a.cs_next_id <= b.cs_next_id /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame fn s t /\
    (alloca_inv s /\ alloca_room ctx fn s ==> window_phase ctx fn a b {} [] s t) /\
    (!ids outs. abi_encoder_registered_effect ids outs s t) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!y. not_fresh_at a y ==>
      lookup_var y t = lookup_var y s /\ FLOOKUP G' y = FLOOKUP G y /\
      op_taint tn' (Var y) = op_taint tn (Var y))
Proof
  strip_tac >>
  rpt gen_tac >>
  `eval_operand (Var root) s = SOME (n2w p) /\ op_taint tn (Var root) = {}` by
    (rewrite_tac[eval_operand_def] >> metis_tac[ptr_covers_def]) >>
  drule_all extcall_tail_add >>
  disch_then (qspecl_then [`G`, `PG`] (qx_choose_then `x` (qx_choose_then `t`
    (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))))) >>
  drule emit_op_facts >> strip_tac >>
  `a.cs_next_id <= b.cs_next_id` by
    (drule emit_op_next_id >> decide_tac) >>
  `ptr_covers G tn root s (k+n)` by metis_tac[ptr_covers_mono] >>
  `p < dimword (:256)` by decide_tac >>
  `w2n (n2w p : 256 word) = p` by simp[w2n_n2w, LESS_MOD] >>
  `FLOOKUP G' x = FLOOKUP G root` by gs[op_prov_def] >>
  `ptr_covers G' tn' x t n` by
    (irule ptr_covers_offset_transport >>
     conj_tac >- metis_tac[] >>
     qexistsl [`G`, `k`, `root`, `s`, `tn`, `n2w p`] >>
     asm_rewrite_tac[word_add_n2w]) >>
  `out = x` by metis_tac[operand_11] >>
  qexistsl [`x`, `t`, `G'`, `tn'`] >> asm_rewrite_tac[] >> decide_tac
QED

(* The request suffix reads the encoded length and the root buffer pointer.
   Both additions preserve the complete selector and payload window. *)
Theorem extcall_encoded_request_suffix:
  emit_op ADD [alen;Lit 4w] a = (len,b) /\
  emit_op ADD [Var root;Lit 28w] b = (off,c) /\
  fn_has_code a b fn /\ fn_has_code b c fn /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand alen s = SOME (n2w (LENGTH bs)) /\ op_taint tn alen = {} /\
  not_fresh_at a root /\ lookup_var root s = SOME (n2w p) /\
  ptr_covers G tn root s capacity /\ 32 + LENGTH bs <= capacity /\
  p + capacity <= s.vs_alloca_next /\ alloca_inv s /\ alloca_room ctx fn s /\
  allocas_from lo s /\ ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  read_memory (p + 28) 4 s = selector /\ read_memory (p + 32) (LENGTH bs) s = bs /\
  (!i. p + 28 <= i /\ i < p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) ==>
  !explicit PG. ?x y t G' tn'.
    off = Var x /\ len = Var y /\ not_fresh_at c x /\ not_fresh_at c y /\
    eval_operand off t = SOME (n2w (p + 28)) /\
    eval_operand len t = SOME (n2w (4 + LENGTH bs)) /\
    ptr_covers G' tn' x t (4 + LENGTH bs) /\
    ptr_covers G' tn' root t capacity /\
    op_taint tn' off = {} /\ op_taint tn' len = {} /\
    read_memory (p + 28) (4 + LENGTH bs) t = selector ++ bs /\
    (!i. p + 28 <= i /\ i < p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_memory = s.vs_memory /\ t.vs_labels = s.vs_labels /\
    abi_encode_exec_frame fn s t /\ window_phase ctx fn a c {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = c.cs_current_bb /\
    t.vs_inst_idx = LENGTH c.cs_current_insts /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. not_fresh_at a z ==>
      lookup_var z t = lookup_var z s /\ FLOOKUP G' z = FLOOKUP G z /\
      op_taint tn' (Var z) = op_taint tn (Var z))
Proof
  strip_tac >> rpt gen_tac >>
  drule_all (Q.SPECL [`4`, `LENGTH bs`] extcall_tail_add) >>
  disch_then (qspecl_then [`G`,`PG`]
    (qx_choose_then `y` (qx_choose_then `u`
      (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))))) >>
  `lookup_var root u = SOME (n2w p) /\
    ptr_covers Gu tu root u capacity` by metis_tac[ptr_covers_lookup_frame] >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo s` (assume_tac o REWRITE_RULE [allocas_from_def]) >>
     qpat_assum `u.vs_allocas = s.vs_allocas` (fn th => PURE_REWRITE_TAC [allocas_from_def,th]) >>
     first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `28 + (4 + LENGTH bs) <= capacity /\ p + 28 < dimword (:256)` by decide_tac >>
  `allocas_below_fmp u = allocas_below_fmp s` by
    (qpat_assum `abi_encode_exec_frame fn s u`
       (assume_tac o cj 2 o REWRITE_RULE [abi_encode_exec_frame_def]) >>
     simp[allocas_below_fmp_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `allocas_below_fmp u = allocas_below_fmp s` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`k` |-> `28`, `n` |-> `4 + LENGTH (bs:word8 list)`, `a` |-> `b`,
    `b` |-> `c`, `dst` |-> `off`, `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`]
    extcall_tail_offset) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `x` (qx_choose_then `t`
      (qx_choose_then `G'` (qx_choose_then `tn'` strip_assume_tac))))) >>
  `a.cs_next_var <= b.cs_next_var` by
    (qpat_assum `emit_op ADD [alen; Lit 4w] a = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     decide_tac) >>
  `not_fresh_at b root` by metis_tac[not_fresh_at_mono] >>
  `read_memory (p + 28) (4 + LENGTH bs) s = selector ++ bs` by
    (once_rewrite_tac[read_memory_split] >> simp[ADD_ASSOC]) >>
  `not_fresh_at c y` by metis_tac[not_fresh_at_mono] >>
  `op_taint tu (Var y) = {}` by metis_tac[] >>
  `lookup_var y t = SOME (n2w (4 + LENGTH bs)) /\ op_taint tn' (Var y) = {}` by
    (qpat_assum `!z. not_fresh_at b z ==> _` (qspec_then `y` mp_tac) >>
     simp[AC ADD_COMM ADD_ASSOC]) >>
  `ptr_covers G' tn' root t capacity` by metis_tac[ptr_covers_lookup_frame] >>
  `op_taint tn' (Var x) = {}` by fs[ptr_covers_def] >>
  `abi_encode_exec_frame fn s t` by metis_tac[abi_encode_exec_frame_trans] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK t,G',tn')` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> metis_tac[]) >>
  `!z. not_fresh_at a z ==>
    lookup_var z t = lookup_var z s /\ FLOOKUP G' z = FLOOKUP G z /\
    op_taint tn' (Var z) = op_taint tn (Var z)` by
    (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  `window_phase ctx fn a b {} [] s u` by metis_tac[] >>
  `alloca_inv u /\ alloca_room ctx fn u` by metis_tac[window_phase_resources] >>
  `window_phase ctx fn a c {} [] s t` by
    (irule window_phase_chain >>
     qexistsl_tac [`{}`,`[]`,`b`,`{}`,`[]`,`u`] >>
     asm_simp_tac (srw_ss()) [] >> metis_tac[]) >>
  qexistsl_tac [`x`,`y`,`t`,`G'`,`tn'`] >>
  fs[eval_operand_def, read_memory_eq_mem_bytes_at]
QED
