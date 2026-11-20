Theory bodyFullAbiDecodeWordCasesObserved
Ancestors
  bodyFullAbiDecodeFiniteObserved bodyFullAbiDecodeInputOrigin
  bodyFullAbiDecodeLeafCases bodyFullAbiDecodeRelativeLoadExact
  bodyFullAbiDecodeOwnedWordStoreObserved
  abiDecoderReentry abiDecoderCoherence abiDecoderWordTyped
  exprSimAbiDecodeChildBounds externalEntryShape calldataClampPtr
  bodyPtrBopScalarOutcome stateRelProj stateFrame
  fragExec fragGasPath fragGasOriginPtrLoop
  abiEncoder exprLoweringProps emitHelperProps loweringShapeRules
  venomInst venomExecSemantics venomState venomMemDefs freshWrites ptrDiscipline
  bodyPtrDefs compileEnv loweringStateRelDefs valueEncodingProps
  finite_map list rich_list pred_set words combin pair

(* Same owned-state quotation as the finite constructor contracts. *)
val owned_decoder_state = ``\st s G tn.
  alloca_history fn s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\
  abi_decode_ptr_window G tn s input input_word (LENGTH input_bytes) /\
  mem_bytes_at (w2n input_word) (LENGTH input_bytes) s.vs_memory = input_bytes /\
  w2n input_word + LENGTH input_bytes <= s.vs_alloca_next /\
  FLOOKUP s.vs_allocas output_id = SOME (output_base,output_cap) /\
  lookup_var output s = SOME (n2w output_base) /\ ptr_covers G tn output s output_cap /\
  output_base + output_cap < dimword (:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < origin.cs_next_id ==> off+sz <= s.vs_alloca_next) /\
  (!name b sz. local_region ce es0.scopes s0 name b sz ==>
      b+sz <= s.vs_alloca_next) /\
  EVERY (\(aid,p,b,k,bytes).
    aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) /\
    lookup_var p s = SOME (n2w b) /\ ptr_covers G tn p s k /\
    op_taint tn (Var p) = {} /\ k = LENGTH bytes /\
    mem_bytes_at b k s.vs_memory = bytes /\ b+k <= s.vs_alloca_next) live /\
  EVERY (\(a,bytes). mem_bytes_at a (LENGTH bytes) s.vs_memory = bytes) protected /\
  (!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\
    ghost_inv_at (DF H) lo delta ce cx es G tn s /\
    ghost_kept_at lo ce es0 origin G0 tn0 s0 G tn) /\
  (?inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [output] /\ inst.inst_id = output_id) /\
  not_local_ptr ce es.scopes output /\ lo <= output_base /\
  (!name b k. local_region ce es.scopes s name b k ==>
    output_base+output_cap <= b \/ b+k <= output_base) /\
  output_id < st.cs_next_id /\ not_fresh_at st output /\
  origin.cs_next_var <= st.cs_next_var /\
  EVERY (\(aid:num,p:string,b:num,k:num,bytes:word8 list). not_fresh_at st p) live``;

val input_origin = ``\s.
  ((?aid ib isz. aid < output_id /\
     FLOOKUP s.vs_allocas aid = SOME (ib,isz) /\ ib <= w2n (input_word:256 word) /\
     w2n input_word + LENGTH (input_bytes:word8 list) <= ib + isz) \/
   (?name ib isz. local_region ce es.scopes s name ib isz /\
     ib <= w2n input_word /\ w2n input_word + LENGTH input_bytes <= ib + isz))``;

Triviality owned_decoder_allocas_below_fmp:
  (^owned_decoder_state) st s G tn /\ (?H. V H) ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp s
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. V H` (qx_choose_then `world` assume_tac) >>
  qpat_assum `!H. V H ==> stmt_state_rel H ctx fn ce cx es s /\ _`
    (qspec_then `world` (fn rel => qpat_assum `V world`
      (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
       CONJUNCT1 o MP rel)))
QED

Theorem abi_decode_owned_word_store_observed[local]:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (^owned_decoder_state) sa s G tn /\ (?H. V H) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  lookup_var dst s = SOME dw /\ ptr_covers G tn dst s 32 /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  output_base <= w2n dw /\ w2n dw+32 <= output_base+output_cap /\
  w2n dw+32 <= s.vs_alloca_next /\
  (w2n input_word + LENGTH input_bytes <= w2n dw \/ w2n dw+32 <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). b+k <= w2n dw \/ w2n dw+32 <= b) live /\
  EVERY (\(b,bytes). b+LENGTH bytes <= w2n dw \/ w2n dw+32 <= b) protected /\
  (^input_origin) s ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 (OK t)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (^owned_decoder_state) sb t Gf tnf /\ (^input_origin) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem SUBSET tn.t_mem /\
    (!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tnf.t_mem) /\
    (!tv v. type_memory_size tv = 32 /\ val_wf tv v /\
       val_in_memory tv v (w2n dw) t.vs_memory ==>
       !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         val_in_memory tv v (w2n dw) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `(^owned_decoder_state) sa s G tn` (fn owned =>
    qpat_assum `?H. V H` (fn world =>
      assume_tac (MATCH_MP owned_decoder_allocas_below_fmp (CONJ owned world)) >>
      map_every assume_tac (CONJUNCTS (BETA_RULE owned)))) >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  mp_tac (BETA_RULE
    bodyFullAbiDecodeOwnedWordStoreObservedTheory.abi_decode_owned_word_store_observed_exact) >>
  (impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]])) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (assume_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)))) >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> first_assum ACCEPT_TAC
QED

(* RelativeLoadExact supplies the physical run. This only interprets that
   run in a code-compatible observer, without using its ghost invariants. *)
Theorem abi_decode_relative_load_observer[local]:
  compile_abi_dec_addr (Var input) pos sa = (addr,sb) /\
  emit_op MLOAD [addr] sb = (v,sc) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sc) s = OK u /\
  t = (u with vs_inst_idx := LENGTH sc.cs_current_insts) ==>
  !obs. fn_has_code sa sc obs ==> gas_path ctx obs s 0 (OK t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emit_op ADD [Var input;pos] sa = (addr,sb)` by
    fs[compile_abi_dec_addr_def] >>
  drule_all inst_extends_emit_op >> strip_tac >>
  `inst_extends sb sc` by metis_tac[inst_extends_emit_op] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc` by
    metis_tac[inst_extends_def, inst_extends_trans] >>
  `sc.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sc) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sc)) = 0` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def,is_terminator_def]) >>
  qpat_assum `t = _` SUBST1_TAC >>
  metis_tac[abi_decode_finite_success_observed]
QED

val observed_clamp_boundary = ``!value clamp sa sb fn ctx s w G tn lo explicit PG.
  compile_abi_clamp_basetype value clamp sa = ((),sb) /\
  fn_has_code sa sb fn /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand value s = SOME w /\ op_prov G value = NONE /\
  op_taint tn value = {} /\ abi_decoder_operand_live sa.cs_next_var value /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?r Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,Gf,tnf)) /\
    (!obs. fn_has_code sa sb obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = Abort Revert_abort t) \/
     (?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       eval_operand value t = SOME w /\
       op_prov Gf value = NONE /\ op_taint tnf value = {} /\
       t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
       tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
       tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
       (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tnf (Var x) = op_taint tn (Var x))))``;

val guarded_observed_pre = ``\start finish dst src opc base_op hi info env sf ty tv d s G tn.
  abi_decoder_coherent ce env sf ty tv /\ info = type_to_abi_dec_info sf ce ty /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes /\
     ((?clamp. info = DecPrimWord clamp) ==>
       off + abi_member_head_size (vyper_to_abi_type env ty) <= h)) /\
  compile_abi_decode_to_buf dst src opc base_op hi info start = ((),finish) /\
  opc = MLOAD /\ fn_has_code start finish fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce start /\ (?H. V H) /\
  w2n input_word+LENGTH input_bytes < dimword (:256) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at origin x) /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ eval_operand dst s = SOME (n2w d) /\
  (?p. dst = Var p /\ ptr_covers G tn p s (d-d+type_memory_size tv) /\
       FLOOKUP G p = SOME (output_base,output_cap)) /\ base_op = Var input /\
  (?off h. eval_operand src s = SOME (n2w off) /\ eval_operand hi s = SOME (n2w h) /\
     off < dimword (:256) /\ h <= LENGTH input_bytes) /\ hi <> Lit 0w /\
  op_prov G src = NONE /\ op_prov G hi = NONE /\
  op_taint tn dst = {} /\ op_taint tn src = {} /\
  op_taint tn base_op = {} /\ op_taint tn hi = {} /\
  abi_decoder_operand_live start.cs_next_var dst /\
  abi_decoder_operand_live start.cs_next_var src /\
  abi_decoder_operand_live start.cs_next_var base_op /\
  abi_decoder_operand_live start.cs_next_var hi /\
  output_base <= d /\ d <= d /\ d+type_memory_size tv <= output_base+output_cap /\
  (w2n input_word+LENGTH input_bytes <= d \/ d+type_memory_size tv <= w2n input_word) /\
  EVERY (\(aid,p,b,k,bytes). aid < start.cs_next_id /\
    (b+k <= d \/ d+type_memory_size tv <= b)) live /\
  EVERY (\(a,bytes). a+LENGTH bytes <= d \/ d+type_memory_size tv <= a) protected /\
  (^owned_decoder_state) start s G tn /\
  EVERY (\(a,bytes). output_base <= a /\ a+LENGTH bytes <= output_base+output_cap) protected /\
  (^input_origin) s``;

val guarded_observed_post = ``\start finish s G tn tv d.
  ?r G' tn'.
    (!H. V H ==> gas_origin_ptr_path
      (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) [] (r,G',tn')) /\
    (!obs. fn_has_code start finish obs ==> gas_path ctx obs s 0 r) /\
    ((?t. r = OK t /\ ~t.vs_halted /\
       t.vs_current_bb = finish.cs_current_bb /\
       t.vs_inst_idx = LENGTH finish.cs_current_insts /\
       (^owned_decoder_state) finish t G' tn' /\
       (!x. not_fresh_at start x ==>
         lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
       (^input_origin) t /\
       (!i. output_base <= i /\ i < output_base+output_cap /\ i IN tn'.t_mem ==>
         i IN tn.t_mem) /\
       (!v. val_wf tv v /\ val_in_memory tv v d t.vs_memory ==>
         !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
           val_in_memory tv v d mem)) \/
     (?t. r = Abort Revert_abort t))``;

Theorem abi_decode_word_case_observed_conditional:
  (^observed_clamp_boundary) ==>
  !dst src opc base_op hi clamp env sf ty tv live protected start finish s G tn d.
    (^guarded_observed_pre) start finish dst src opc base_op hi (DecPrimWord clamp)
      env sf ty tv d s G tn ==>
    (^guarded_observed_post) start finish s G tn tv d
Proof
  disch_tac >> rpt gen_tac >>
  qabbrev_tac `OS = (^owned_decoder_state)` >>
  qabbrev_tac `IO = (^input_origin)` >>
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?off h. _ /\ _ /\ _ /\ _ /\ _`
    (qx_choose_then `off` (qx_choose_then `h` (map_every assume_tac o CONJUNCTS))) >>
  `off + abi_member_head_size (vyper_to_abi_type env ty) <= h` by
    (qpat_assum `(?clamp'. _) ==> _` mp_tac >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def,compile_abi_decode_static_def,
       comp_bind_def,comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `type_to_abi_dec_info sf ce ty = DecPrimWord clamp` by simp[Once EQ_SYM_EQ] >>
  drule_all exprSimAbiDecodeChildBoundsTheory.abi_decode_scalar_member_head >>
  strip_tac >>
  drule abiDecoderWordTypedTheory.abi_decoder_primitive_cases >>
  disch_then drule >> disch_then (assume_tac o cj 2) >>
  `type_memory_size tv = 32 /\ abi_member_head_size (vyper_to_abi_type env ty) = 32` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     simp[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  rename1 `compile_abi_clamp_basetype val_op clamp cs'' = (ignored,clamped)` >>
  `ignored = ()` by (Cases_on `ignored` >> simp[]) >>
  qpat_x_assum `ignored = ()` SUBST_ALL_TAC >>
  `cs_extends start cs' /\ cs_extends cs' cs'' /\
   cs_extends cs'' clamped /\ cs_extends clamped finish'` by
    metis_tac[externalEntryShapeTheory.compile_abi_dec_addr_labels,
      externalEntryShapeTheory.emit_op_labels,
      externalEntryShapeTheory.compile_abi_clamp_basetype_labels,
      externalEntryShapeTheory.emit_void_labels, pairTheory.SND] >>
  `cs_extends start cs'' /\ cs_extends cs'' finish'` by metis_tac[cs_extends_trans] >>
  `fn_has_code start cs'' fn /\ fn_has_code cs'' finish' fn` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `off + 32 <= LENGTH input_bytes` by decide_tac >>
  `allocas_from lo s /\ origin.cs_next_var <= start.cs_next_var` by
    (fs[Abbr `OS`] >> metis_tac[ghost_inv_at_def]) >>
  qpat_x_assum `base_op = Var input` SUBST_ALL_TAC >>
  `not_fresh_at start input` by
    ((qpat_assum `abi_decoder_operand_live start.cs_next_var (Var input)` mp_tac >>
     simp[abiDecoderReentryTheory.abi_decoder_operand_live_def,
          abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def] >> (gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def, abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]))) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at start x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_assum `Abbrev (OS = _)` (fn ab =>
    qpat_assum `OS start s G tn` (fn owned =>
      qpat_assum `?H. V H` (fn world =>
        assume_tac (MATCH_MP (PURE_REWRITE_RULE
          [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)]
          owned_decoder_allocas_below_fmp) (CONJ owned world))))) >>
  qpat_assum `Abbrev (OS = _)` (fn th =>
    drule_all (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
      abi_decode_owned_relative_load_exact)) >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  `!obs. fn_has_code start cs'' obs ==> gas_path ctx obs s 0 (OK t)` by
    (qx_gen_tac `obs` >> disch_tac >>
     qpat_x_assum `fn_has_code start cs'' fn` kall_tac >>
     drule_all abi_decode_relative_load_observer >>
     disch_then (qspec_then `ctx` ACCEPT_TAC)) >>
  `fn_has_code cs'' clamped fn /\ fn_has_code clamped finish' fn` by
    (irule (SIMP_RULE (srw_ss()) [] (Q.SPECL [`cs''`,`clamped`,`finish'`,`fn`]
      fragExecTheory.fn_has_code_split)) >> simp[]) >>
  `abi_decoder_operand_live cs''.cs_next_var val_op` by
    (irule abiDecoderReentryTheory.abi_decoder_operand_live_emit >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (conj_tac
     >- (qpat_assum `t.vs_allocas = s.vs_allocas` (fn th =>
           rewrite_tac[ptrDisciplineTheory.allocas_from_def, th]) >>
         qpat_assum `allocas_from lo s`
           (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def])) >>
     qpat_assum `t.vs_alloca_next = s.vs_alloca_next` (fn th => rewrite_tac[th]) >>
     qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS start s G tn`
         (ACCEPT_TAC o cj 2 o BETA_RULE o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]))) >>
  qpat_assum `Abbrev (OS = _)` (fn ab =>
    qpat_assum `OS cs'' t Gf tnf` (fn owned =>
      qpat_assum `?H. V H` (fn world =>
        assume_tac (MATCH_MP (PURE_REWRITE_RULE
          [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] ab)]
          owned_decoder_allocas_below_fmp) (CONJ owned world))))) >>
  qpat_x_assum `!value clamp sa sb fn ctx s w G tn lo explicit PG. _` drule_all >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `cr` (qx_choose_then `CG` (qx_choose_then `CT` strip_assume_tac))))
  >- suspend "clamp_revert"
  >> suspend "clamp_success"
QED
Resume abi_decode_word_case_observed_conditional[clamp_revert]:
  qexistsl_tac [`cr`,`CG`,`CT`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `fn_has_code start cs'' obs /\ fn_has_code cs'' clamped obs` by
        metis_tac[fragExecTheory.fn_has_code_split] >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `t` >> simp[]) >>
  disj2_tac >> metis_tac[]
QED
Resume abi_decode_word_case_observed_conditional[clamp_success]:
  `start.cs_next_var <= cs''.cs_next_var` by
    (`emit_op ADD [Var input;src] start = (src_addr,cs')` by
       fs[compile_abi_dec_addr_def] >>
     qpat_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     qpat_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emit_op_facts) >>
     decide_tac) >>
  `cs''.cs_next_var <= clamped.cs_next_var /\ cs''.cs_next_id <= clamped.cs_next_id` by
    (mp_tac (Q.SPECL [`val_op`,`clamp`,`cs''`] ci_mono_compile_abi_clamp_basetype) >>
     simp[ci_mono_def]) >>
  `start.cs_next_var <= clamped.cs_next_var` by decide_tac >>
  `?B. bop_scalar_seq {} UNIV (emitted_insts cs'' clamped) B /\
       clamped.cs_current_insts = cs''.cs_current_insts ++ emitted_insts cs'' clamped /\
       same_blocks cs'' clamped` by
    (drule calldataClampPtrTheory.abi_decode_clamp_scalar >>
     disch_then (qspecl_then [`{}`,`UNIV`] mp_tac) >> simp[] >>
     strip_tac >> qexists_tac `UNIV` >> asm_rewrite_tac[]) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cs'' clamped)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule_all bodyPtrBopScalarOutcomeTheory.bop_scalar_seq_outputs >> simp[]) >>
  `alloca_history fn t` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS cs'' t Gf tnf`
         (ACCEPT_TAC o CONJUNCT1 o BETA_RULE o
          PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab]))) >>
  `alloca_history fn t'` by
    (irule bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_no_alloca_endpoint_history_lower >>
     qexistsl_tac [`t`,`cs''`,`clamped`] >> simp[same_blocks_def,IS_PREFIX_APPEND] >>
     fs[same_blocks_def]) >>
  `not_fresh_at cs'' input /\ local_ptrs_reserved ce cs'' /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs'' x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cs'' x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `OS clamped t' CG CT` by
    (qpat_assum `Abbrev (OS = _)` (fn th =>
       irule (PURE_REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]
         bodyFullAbiDecodeRelativeLoadExactTheory.abi_decode_owned_scalar_frame_with_history_lower)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`Gf`,`t`,`cs''`,`tnf`] >> asm_rewrite_tac[]) >>
  `!x. not_fresh_at start x ==> lookup_var x t' = lookup_var x s /\
    FLOOKUP CG x = FLOOKUP G x /\ op_taint CT (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at cs'' x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at cs'' x ==> _` (qspec_then `x` mp_tac) >>
     qpat_assum `!x. not_fresh_at start x ==> lookup_var x t = _ /\ _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `IO t'` by
    (qpat_assum `Abbrev (IO = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     BETA_TAC >> irule abi_decode_input_origin_transport >>
     qexistsl_tac [`s`,`start`] >>
     qpat_assum `Abbrev (IO = _)` (fn ab =>
       qpat_assum `IO s` (assume_tac o BETA_RULE o
         PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     simp[] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?p. dst = Var p /\ _` (qx_choose_then `p` strip_assume_tac) >>
  qpat_x_assum `dst = Var p` SUBST_ALL_TAC >>
  `not_fresh_at start p` by
    fs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def,not_fresh_at_def] >>
  `lookup_var p t' = SOME (n2w d) /\ ptr_covers CG CT p t' 32` by
    (qpat_assum `!x. not_fresh_at start x ==> lookup_var x t' = _ /\ _`
       (qspec_then `p` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     conj_tac >- simp[GSYM eval_operand_def] >>
     qpat_assum `ptr_covers G tn p s _`
       (mp_tac o REWRITE_RULE [ptr_covers_def]) >>
     simp[ptr_covers_def]) >>
  `local_ptrs_reserved ce clamped /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at clamped x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `d+32 <= t'.vs_alloca_next /\ w2n (n2w d : 256 word) = d` by
    (qpat_assum `Abbrev (OS = _)` (fn ab =>
       qpat_assum `OS clamped t' CG CT`
         (mp_tac o BETA_RULE o PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     `alloca_inv t'` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
     `output_base+output_cap <= t'.vs_alloca_next` by
       (qpat_assum `alloca_inv t'`
          (mp_tac o REWRITE_RULE [alloca_inv_def,alloca_next_valid_def]) >>
        strip_tac >>
        qpat_assum `!aid b sz. FLOOKUP t'.vs_allocas aid = _ ==> _`
          (qspecl_then [`output_id`,`output_base`,`output_cap`] MATCH_MP_TAC) >>
        first_assum ACCEPT_TAC) >>
     `d < dimword (:256)` by decide_tac >> simp[]) >>
  `EVERY (\(aid,p,b,k,bytes). b+k <= d \/ d+32 <= b) live` by
    (pure_rewrite_tac[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
     qpat_assum `EVERY (\(aid,p,b,k,bytes). aid < _ /\ _) live`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(e0,e1,e2,e3,e4)` mp_tac) >> simp[]) >>
  qpat_assum `type_memory_size tv = 32` (fn sz =>
    map_every (fn q => qpat_assum q (assume_tac o PURE_REWRITE_RULE [sz]))
      [`d + type_memory_size tv <= _`,
       `w2n input_word + LENGTH input_bytes <= d \/ d + type_memory_size tv <= _`,
       `EVERY (\(a,bytes). a + LENGTH bytes <= d \/ d + type_memory_size tv <= a) protected`]) >>
  qpat_assum `Abbrev (OS = _)` (fn os =>
    qpat_assum `Abbrev (IO = _)` (fn io =>
      qpat_assum `w2n (n2w d : 256 word) = d` (fn addr =>
        drule_all (PURE_REWRITE_RULE [addr,
          GSYM (REWRITE_RULE [markerTheory.Abbrev_def] os),
          GSYM (REWRITE_RULE [markerTheory.Abbrev_def] io)]
          (Q.INST [`dw` |-> `(n2w d : 256 word)`]
            abi_decode_owned_word_store_observed))))) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `z` (qx_choose_then `ZG` (qx_choose_then `ZT` strip_assume_tac)))) >>
  qpat_x_assum `t = u with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `cr = OK t'` SUBST_ALL_TAC >>
  qexistsl_tac [`OK z`,`ZG`,`ZT`] >> conj_tac
  >- (rpt strip_tac >> irule gas_origin_ptr_path_trans >>
      qexistsl_tac [`Gf`,`t`,`tnf`] >> conj_tac >- simp[] >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`CG`,`t'`,`CT`] >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `obs` >> disch_tac >>
      `fn_has_code start cs'' obs /\ fn_has_code cs'' finish' obs` by
        metis_tac[fragExecTheory.fn_has_code_split] >>
      `fn_has_code cs'' clamped obs /\ fn_has_code clamped finish' obs` by
        metis_tac[fragExecTheory.fn_has_code_split] >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `t` >> conj_tac >- simp[] >>
      irule (SIMP_RULE (srw_ss()) [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
      qexists_tac `t'` >> simp[]) >>
  disj1_tac >> qexists_tac `z` >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at clamped x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
      qpat_assum `!x. not_fresh_at clamped x ==> _` (qspec_then `x` mp_tac) >>
      qpat_assum `!x. not_fresh_at start x ==> lookup_var x t' = _ /\ _`
        (qspec_then `x` mp_tac) >> simp[])
  >- (rpt strip_tac >> qpat_assum `ZT.t_mem SUBSET CT.t_mem`
        (drule_then assume_tac o REWRITE_RULE [SUBSET_DEF]) >>
      qpat_assum `CT.t_mem = tnf.t_mem` (fn a =>
        qpat_assum `tnf.t_mem = tn.t_mem` (fn b =>
          qpat_assum `i IN CT.t_mem` (ACCEPT_TAC o REWRITE_RULE [a,b])))) >>
  rpt strip_tac >>
  qpat_assum `!tv v. type_memory_size tv = 32 /\ _ ==> _`
    (qspecl_then [`tv`,`v`] mp_tac) >> simp[]
QED
Finalise abi_decode_word_case_observed_conditional
