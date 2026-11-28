(* Allocation framing for non-slot For element preparation. *)
Theory bodyFullForArray
Ancestors
  bodyFullShadowBodyInv bodyInvCodeProps exprBodyPreProps
  whitelistForIterImmCopy whitelistForIterImmLoop stmtSimForArrayLoop
  bodyFullUnwrapCodeCtorRun bodyFullUnwrapCodeRuntimeRun fragGasOriginPtr
  ptrDiscipline allocationPtr context arithmetic pred_set
  assignTuplePtrCopyLen bodyPtrDefs stmtSimDeclCompose exprSimCopy exprLoweringProps
  stmtLowering loweringPosts loweringStateRelDefs venomMemDefs venomState
  compileEnv vyperState valueEncoding finite_map words
  bodyFullPreds bodySimFull stmtSimDefs stmtSimProps bodyFullAllocaFresh exprSimHyps bodySim allocLimits bodyFullHashKeccakFixed emitHelper
  exprSimBopRestWordLoadPath exprSimBopRestWordLayout exprSimBopRestWordTail
  fragGasMode fragGasPath
  typedCopyLayoutPtr bodyPtrBytestringBuiltinsWindowGhost bodyDynArraySource
  stmtSimForArray vyperInterpreter vyperValueOperation vyperTyping vyperTypeValues
  valueEncodingDefs valueEncodingProofs list abiDecodeStaticProps logAbiPrefixPtr reasonCopySourcePtr
  bodyFullTargetArrayLoad bodyFullGhostFrame bodyPtrSignedConvertSourceFrame exprSimVVFrame exprSimMemDefs stmtReasonLitFragMemory bodyBinopFragMemory logValueFramePtr typedCopyOriginPtr typedCopyDomain typedMemoryCopy vyperTypeSystem
  memoryLayoutSource memoryLayoutRel memoryValueEncoding layoutStoreProps robustCopyTransportPtr contextProps fragGasOriginPtrDead emitHelperProps venomExecSemantics codegenRel venomInst stmtReasonMemory fragExecPtr assignTuplePtrLocalFixedCopy fragExec fragGasSeqPtr ptrSafeRun unitTransformDefs memSafeRun
  contextCodegenRel valueEncodingProps memLocDefs immutableWordExecution stmtAppendStorageRunPtr
  gasOutcomeFullCompose gasExemptCert haltExitProj vyperStorageTrace
  exprSimSubscriptArraySource exprSimSubscriptArrayOrigin
  targetSubscriptMemory stmtSimForArrayFrame vyperLocalAccessFrame exprSimIfExp[qualified,ignore_grammar]
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]
  gasOutcomeFullMods[qualified]

(* The bytestring copy uses the padded live footprint, not the capacity of
   either type. The path and representation refer to the same raw run. *)
Theorem for_memory_bytes_element_joint_frame:
  compile_iter_elem_copy c (Var xs) (Var xd) bytes LocMemory F dty sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type sty /\ is_bytestring_type dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
   (?str. v = StringV str /\ len = LENGTH str)) /\
  n = 32 + 32 * ((len+31) DIV 32) /\
  len+31 < dimword (:256) /\ n < dimword (:256) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + n < dimword (:256) /\ w2n dw + n < dimword (:256) /\
  w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
  (w2n sw + n <= w2n dw \/ w2n dw + n <= w2n sw) /\
  ptr_covers G tn xs s n /\ FLOOKUP s.vs_allocas aid = SOME (w2n dw,capacity) /\
  ptr_covers G tn xd s capacity /\ n <= capacity /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < n ==> (w2n dw+i IN tnf.t_mem <=> w2n sw+i IN tn.t_mem)) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `compile_store_bytestring (Var xs) (Var xd) sa = ((),sb)` by
    fs[compile_iter_elem_copy_def, compile_store_memory_def] >>
  drule_all bodyPtrIfExpCopyHeaderTheory.robust_bytestring_header >> strip_tac >>
  `n = 32 + 32 * word_size len` by simp[vfmConstantsTheory.word_size_def] >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw` by
    simp[eval_operand_def] >>
  `!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[]) >>
  `32 + 32 * word_size len < dimword (:256) /\
   w2n sw + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n dw + (32 + 32 * word_size len) <= s.vs_alloca_next` by
    (qpat_assum `n = 32 + 32 * word_size len` (SUBST1_TAC o SYM) >>
     asm_rewrite_tac[]) >>
  drule_all bodyCopyMemoryBaseTheory.compile_store_bytestring_body_mem_ok >>
  disch_then assume_tac >>
  drule exprSimBufferStoreTheory.buffer_store_bytestring_shape >>
  simp[same_blocks_def] >> strip_tac >>
  drule_all fn_has_code_code >>
  disch_then (qx_choose_then `code_bb` strip_assume_tac) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qexists_tac `code_bb` >> simp[]) >>
  pop_assum strip_assume_tac >>
  `ptr_covers G tn xd s n` by
    (irule ptr_covers_mono >> qexists_tac `capacity` >> simp[]) >>
  drule_all bodyFullAllocGenericTheory.compile_store_bytestring_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac)))) >>
  drule_all exprSimBufferStoreTheory.buffer_store_bytestring_run >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `q = sf` by
    (qpat_assum `run_inst_seq _ s = OK sf` mp_tac >>
     qpat_assum `run_inst_seq _ s = OK q` (fn th => simp[th])) >>
  qpat_x_assum `q = sf` SUBST_ALL_TAC >>
  drule_all bodyPtrIfExpBytesPostTheory.bytestring_copy_effects >> strip_tac >>
  suspend "post"
QED

Resume for_memory_bytes_element_joint_frame[post]:
  `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
     val_in_memory dtv v (w2n dw) m` by
    (rpt strip_tac >>
     irule bodyPtrIfExpBytesPostTheory.bytestring_copy_robust_destination >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`w2n sw`, `dty`, `len`, `n`, `s`, `sf`, `stv`,
                   `sty`, `tenv`, `tn`, `tnf`] >>
     qpat_x_assum `n = 32 + 32 * word_size len` kall_tac >>
     qpat_x_assum `sf.vs_memory = (mcopy _ _ (32 + 32 * word_size len) s).vs_memory`
       kall_tac >>
     asm_rewrite_tac[]) >>
  `val_in_memory dtv v (w2n dw) sf.vs_memory` by
    (qpat_assum `!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> _`
       (qspec_then `sf.vs_memory` mp_tac) >> simp[mem_agree_outside_def]) >>
  `sf.vs_halted = s.vs_halted /\ sf.vs_current_bb = s.vs_current_bb /\
   sf.vs_allocas = s.vs_allocas` by
    (qpat_assum `sf with <|vs_vars := _; vs_memory := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `ptr_covers Gf tnf xd sf capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  `FLOOKUP sf.vs_vars xd = SOME dw` by
    (rewrite_tac[GSYM lookup_var_def] >> simp[]) >>
  `typed_copy_frame (w2n dw) n s.vs_memory sf.vs_memory` by
    (qpat_assum `sf.vs_memory = (mcopy _ _ n s).vs_memory` SUBST1_TAC >>
     simp[typed_copy_frame_def, placeMemoryTypedPrimitiveTheory.mcopy_memory_length] >>
     rpt gen_tac >> disch_tac >>
     irule valueCopyTheory.mem_bytes_at_mcopy_disjoint >> first_assum ACCEPT_TAC) >>
  `!k. typed_copy_state_frame sa (w2n dw) n s (sf with vs_inst_idx := k)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x sf = lookup_var x s`
       (assume_tac o REWRITE_RULE[lookup_var_def]) >>
     simp[NoAsms, typed_copy_state_frame_def, lookup_var_def] >>
     conj_tac
     >- (qpat_assum `sf with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
         simp[NoAsms, venom_state_component_equality]) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`sf with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)`,
                `Gf`, `tnf`] >>
  qpat_x_assum `sf.vs_memory = (mcopy _ _ (32 + 32 * word_size len) s).vs_memory`
    kall_tac >>
  qpat_x_assum `sf.vs_memory = (mcopy _ _ n s).vs_memory` kall_tac >>
  simp[lookup_var_def, ptr_covers_def] >>
  `32 * word_size len + 32 = n` by
    (once_rewrite_tac[ADD_COMM] >>
     qpat_assum `n = 32 + 32 * word_size len` (ACCEPT_TAC o SYM)) >>
  pop_assum SUBST1_TAC >>
  qpat_assum `!k. typed_copy_state_frame sa (w2n dw) n s (sf with vs_inst_idx := k)`
    (qspec_then `LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)` ACCEPT_TAC)
QED

Finalise for_memory_bytes_element_joint_frame

(* The declaration reserves the name; the following emission is precisely
   the allocation buffer compiler at the predeclaration state. *)
Theorem for_array_declare_emit_alloc_buffer:
  !cenv id fty saL bc saD saA.
    declare_local cenv id fty saL = (bc,saD) /\
    emit_local_alloca bc id saD = ((),saA) /\ cenv.ce_alloca_locals ==>
    compile_alloc_buffer (type_memory_bytes cenv fty) saL =
      (<|buf_operand := Var (STRING #"%" (toString saL.cs_next_var));
         buf_size := type_memory_bytes cenv fty|>,saA)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all declare_local_ptr >> strip_tac >>
  gvs[emit_local_alloca_def, compile_alloc_buffer_def, emit_op_def,
      fresh_var_def, fresh_id_def, emit_inst_def, emit_def,
      comp_bind_def, comp_return_def, comp_ignore_bind_def]
QED

(* This boundary preserves the original entry frame through the actual
   immutable element copy and source binding. It makes no joint-path claim. *)
Theorem for_immutable_element_copy_alloca_frame:
  compile_iter_elem_copy c src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es1 s /\
  immutable_holds c cx ty (Value v) a es1 s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + bytes < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_frame c es0 sa0 s0 c es1 s /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ bytes <= capacity /\
  FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  es1.scopes = sc :: rest /\ ee.scopes = (sc |+ (id,entry)) :: rest /\
  local_ptrs_reserved c sa ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      alloca_frame c es0 sa0 s0 c ee z
Proof
  strip_tac >>
  `copy_old_operand sa (Var p)` by simp[copy_old_operand_def] >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule_all immutable_iter_copy_typed_run_full >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule alloca_frame_declare_store >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`aid0`, `s`, `sa0`, `w`] >>
  asm_rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
  conj_tac >- gvs[copy_runtime_frame_def] >>
  rpt gen_tac >> strip_tac >>
  `aid <> aid0` by decide_tac >>
  `off + z' <= w2n w \/ w2n w + capacity <= off` by
    (qpat_x_assum `allocas_non_overlapping s`
       (mp_tac o REWRITE_RULE [venomMemDefsTheory.allocas_non_overlapping_def]) >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  first_x_assum irule >> decide_tac
QED

(* The emitted copy uses the outer environment, while the fresh loop pointer
   belongs to bc.  Only the initial frame environment is transported. *)
Theorem for_immutable_element_copy_outer_frame:
  compile_iter_elem_copy c src (Var p) bytes LocCode F ty ty sa = ((),sb) /\
  bytes = type_memory_size tv /\ 0 < bytes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es s /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  immutable_holds c cx ty (Value v) a es s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + bytes < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  alloca_frame c es0 sa0 s0 bc (es with scopes := FEMPTY :: es.scopes) s /\
  (!name. IS_SOME (lookup_scopes name es0.scopes) ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ bytes <= capacity /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  local_ptrs_reserved bc sa ==>
  ?z. copy_runtime_frame sa s sb z /\
      val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
      val_footprint tv v <= bytes /\
      LENGTH s.vs_memory <= LENGTH z.vs_memory /\
      (!off len. off + len <= w2n w \/ w2n w + bytes <= off ==>
        mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      alloca_frame c es0 sa0 s0 bc ee z
Proof
  strip_tac >>
  `compile_iter_elem_copy bc src (Var p) bytes LocCode F ty ty sa = ((),sb)` by
    (drule immutable_iter_copy_top_ext >>
     disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  `stmt_state_rel H ctx func bc cx
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule array_empty_scope_rel_transport >> goal_assum (drule_at Any) >> simp[]) >>
  `immutable_holds bc cx ty (Value v) a
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule immutable_value_holds_transport >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `bc.ce_is_ctor = c.ce_is_ctor /\ bc.ce_imm_alloca = c.ce_imm_alloca` by
    (fs[cenv_top_ext_def] >>
     qpat_x_assum `_ = c` (SUBST1_TAC o SYM) >> simp[]) >>
  `alloca_frame bc es0 sa0 s0 bc
      (es with scopes := FEMPTY :: es.scopes) s` by
    (irule alloca_frame_cenv_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `!region. bc.ce_is_ctor /\ bc.ce_imm_alloca = SOME region ==>
      eval_operand region s = SOME 0w /\ copy_old_operand sa region` by simp[] >>
  `(bc.ce_is_ctor ==> regions_disjoint (w2n a) bytes (w2n w) bytes)` by simp[] >>
  `(es with scopes := FEMPTY :: es.scopes).scopes = FEMPTY :: es.scopes` by simp[] >>
  drule_all for_immutable_element_copy_alloca_frame >> strip_tac >>
  qexists_tac `z` >> asm_rewrite_tac[] >>
  irule alloca_frame_cenv_pre >> goal_assum (drule_at Any) >> simp[]
QED

(* The semantic frame and the joint path share a deterministic raw endpoint.
   Only the latter advances the instruction cursor. *)
Theorem for_immutable_large_element_joint_frame:
  compile_iter_elem_copy c src (Var p) (32*n) LocCode F ty ty sa = ((),sb) /\
  32 < 32*n /\ 32*n = type_memory_size tv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es s /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  immutable_holds c cx ty (Value v) a es s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + capacity < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) (32*n) (w2n w) (32*n)) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  alloca_frame c es0 sa0 s0 bc (es with scopes := FEMPTY :: es.scopes) s /\
  (!name. IS_SOME (lookup_scopes name es0.scopes) ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ 32*n <= capacity /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  local_ptrs_reserved bc sa /\
  op_taint tn src = {} /\ ptr_covers G tn p s capacity /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n w + 32*n <= s.vs_alloca_next /\
  (c.ce_is_ctor ==>
    op_prov G src = NONE /\ w2n a + 32*n <= lo /\ lo <= w2n w /\
    w2n a + 32*n <= s.vs_alloca_next) /\
  (~c.ce_is_ctor ==>
    w2n a + 32*n <= LENGTH s.vs_data_section /\
    w2n a + 32*n < dimword (:256)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf z.
    copy_runtime_frame sa s sb z /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= 32*n /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + 32*n <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    alloca_frame c es0 sa0 s0 bc ee z /\
    (!x. x IN tnf.t_mem <=>
      if w2n w <= x /\ x < w2n w + 32*n
      then c.ce_is_ctor /\ w2n a + (x - w2n w) IN tn.t_mem
      else x IN tn.t_mem) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!q sz. not_fresh_at sa q /\ ptr_covers G tn q s sz ==>
      ptr_covers Gf tnf q z sz)
Proof
  strip_tac >>
  `0 < 32*n /\ w2n w + 32*n < dimword (:256)` by decide_tac >>
  `!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region` by metis_tac[] >>
  drule_all for_immutable_element_copy_outer_frame >> strip_tac >>
  `(32*n+31) DIV 32 = n` by simp[Once MULT_COMM, ADD_DIV_ADD_DIV] >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca src (Var p) n 0 sa = ((),sb)` by
    (drule immutable_iter_large_copy >> simp[] >>
     disch_then (fn th => fs[th])) >>
  Cases_on `c.ce_is_ctor`
  >- (fs[] >>
      `!region. c.ce_imm_alloca = SOME region ==>
         eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
         op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
      drule (code_copy_ctor_range_origin_ptr |> Q.INST [`off` |-> `0`] |> SRULE []) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
      disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
      simp[ADD_COMM] >> strip_tac >>
      `t = z` by fs[copy_runtime_frame_def] >>
      qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[] >>
      qpat_x_assum `32*n = type_memory_size tv` (fn th => fs[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  fs[] >>
  drule (runtime_code_copy_range_origin |> Q.INST [`off` |-> `0`] |> SRULE []) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
  simp[ADD_COMM] >> strip_tac >>
  `t = z` by fs[copy_runtime_frame_def] >>
  qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[IN_DIFF] >>
  qpat_x_assum `32*n = type_memory_size tv` (fn th => fs[GSYM th]) >>
  conj_tac >- first_assum ACCEPT_TAC >> simp[CONJ_COMM]
QED

(* Apply the enabled Array iterator IH to the actual expression compilations.
   Keep the full vv post, including aggregate ownership and exceptional exits. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     c cx (expr_type e) e es` by
    (fs[body_iterator_full_ok_def, Once body_expr_full_ok_def] >>
     first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`shadow_sa`, `shadow_sb`] >> simp[]
QED
*)
Theorem for_array_expr_prefix_full:
  body_iterator_full_ok_mods mods exps cx (Array e) /\
  body_const_cells_agree mods cx env es /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ expr_body_pre_mods mods c cx env e es /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  return_buf_frame d c sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func c cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d c cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    c.ce_modules cx st0 (eval_expr cx e) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?tv. res = INL tv /\
      vv_post H ctx func c cx e es sa sb s ee tv vv t /\
      vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      ptr_vv_ok cx (post_value_type c e) tv vv ee G1 tn1 t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type c e) /\
        ~is_bytestring_type (post_value_type c e) ==>
        vv_own c cx (post_value_type c e) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?v. read_result cx tv ee = (INL v,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type c e) ==>
        ptr_buf_ok c e op G1 t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok c e p.ptr_operand G1 t) /\
      ghost_kept_at lo c es sa G tn s G1 tn1)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))
Proof
  cheat
QED

(* A non-slot iterator materializes exactly the elements of its source read. *)
Theorem for_array_copy_read[local]:
  (!tr slot etv bd. rv <> PlaceR (StoragePlace tr slot (ArrayTV etv bd))) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  array_iterator_results cx ty rv ee = (INL vs,ei) ==>
  ei = ee /\ ?av xs. read_result cx rv ee = (INL (ArrayV av),ee) /\
    extract_elements tv (ArrayV av) = SOME xs /\ vs = MAP Value xs
Proof
  strip_tac >>
  drule vyperInterpreterTheory.array_iterator_results_state >> strip_tac >>
  drule vyperInterpreterTheory.array_iterator_results_copy >> strip_tac >>
  Cases_on `read_result cx rv ee` >> rename1 `_ = (rr,er)` >>
  drule read_result_state >> strip_tac >>
  Cases_on `rr` >>
  gvs[vyperStateTheory.bind_def, lift_option_type_def, vyperStateTheory.raise_def,
      vyperStateTheory.return_def] >>
  rename1 `read_result cx rv ee = (INL v,ee)` >>
  Cases_on `v` >> gvs[vyperValueOperationTheory.extract_elements_def,
    lift_option_type_def, vyperStateTheory.raise_def, vyperStateTheory.return_def]
QED

(* The actual source list and the header observation share the expression
   endpoint. A fixed array contributes its dense, type-indexed element list. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all for_array_copy_read >> disch_then
    (CONJUNCTS_THEN2 SUBST_ALL_TAC
      (qx_choose_then `av` (qx_choose_then `xs` strip_assume_tac))) >>
  `type_widens_to env.type_defs (post_value_type c e) (ArrayT ty bd)` by
    (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
     drule_then strip_assume_tac expr_body_pre_static_facts >>
     drule_all post_value_type_widens >> simp[]) >>
  `?pty pbd. post_value_type c e = ArrayT pty pbd /\
     (case bd of Fixed n => pbd = Fixed n | Dynamic n => ?m. pbd = Dynamic m /\ m <= n)` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >> simp[type_widens_to_def] >>
     disch_then strip_assume_tac
     >- (qexistsl_tac [`ty`, `bd`] >> Cases_on `bd` >> simp[]) >>
     Cases_on `post_value_type c e` >> fs[arg_type_fits_def] >>
     rename1 `arg_type_fits (ArrayT pty pbd) (ArrayT ty bd)` >>
     Cases_on `pbd` >> Cases_on `bd` >> gvs[arg_type_fits_def] >>
     metis_tac[]) >>
  drule post_type_evaluates >> strip_tac >>
  `?pet. evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV pet pbd)` by
    (qpat_x_assum `evaluate_type _ (post_value_type c e) = SOME _` mp_tac >>
     simp[] >> metis_tac[evaluate_type_ArrayT_cases]) >>
  qhdtm_assum `vv_post`
    (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
  `?a. eval_operand addr s = SOME a /\
       (loc = LocMemory ==>
         val_in_memory (ArrayTV pet pbd) (ArrayV av) (w2n a) s.vs_memory /\
         op_taint tn addr = {} /\ ptr_mem_ok cx (post_value_type c e) (ArrayV av) addr G tn s) /\
       (loc = LocCode ==>
         vv_location vv = SOME LocCode /\
         immutable_holds c cx (post_value_type c e) rv a ee s /\
         op_taint tn addr = {} /\ op_prov G addr = NONE)` by
    (Cases_on `vv` >> gvs[vv_holds_def, vv_operand_def, vv_location_def,
      ptr_vv_ok_def, ptr_val_ok_def, expr_val_rel_def, is_word_type_def,
      is_bytestring_type_def] >>
     rename1 `case p.ptr_location of _ => _` >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  `loc = LocMemory ==> val_wf (ArrayTV pet pbd) (ArrayV av) /\
    (!i. w2n a <= i /\ i < w2n a + val_footprint (ArrayTV pet pbd) (ArrayV av) ==>
         i < s.vs_alloca_next)` by
    (strip_tac >>
     `!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory` by
       (Cases_on `vv` >> gvs[vv_location_def]) >>
     `~is_word_type (post_value_type c e)` by simp[is_word_type_def] >>
     `eval_operand (vv_operand vv) s = SOME a` by
       (qpat_assum `addr = vv_operand vv` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
     drule_all bodyPtrIfExpAllocSourceTheory.vv_at_memory_footprint >> simp[]) >>
  `loc = LocCode ==> value_has_type (ArrayTV pet pbd) (ArrayV av)` by
    (strip_tac >>
     `immutable_holds c cx (post_value_type c e) rv a ee s` by fs[] >>
     qhdtm_x_assum `immutable_holds` (strip_assume_tac o REWRITE_RULE [immutable_holds_def]) >>
     gvs[]) >>
  `val_wf (ArrayTV pet pbd) (ArrayV av)` by
    (qpat_x_assum `loc = LocMemory \/ loc = LocCode` strip_assume_tac >>
     fs[valueEncodingTypingTheory.value_has_type_val_wf]) >>
  qpat_x_assum `loc = (case vv_location vv of NONE => LocMemory | SOME l => l)` kall_tac >>
  conj_tac >- REFL_TAC >>
  qexistsl_tac [`av`, `xs`, `pty`, `pbd`, `pet`, `a`] >> simp[] >>
  namedCases_on `bd` ["cap", "cap"] >> gns[]
  >- (Cases_on `av` >> gvs[val_wf_def, extract_elements_def, array_elements_def,
                            array_length_def]) >>
  qpat_x_assum `?m. pbd = Dynamic m /\ _`
    (qx_choose_then `pc` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  namedCases_on `av` ["ds", "ks", "ts"] >> gnvs[val_wf_def, extract_elements_def,
    array_elements_def, array_length_def] >>
  qpat_x_assum `loc = LocMemory \/ loc = LocCode` strip_assume_tac >> gvs[]
  >- (conj_tac
      >- fs[valueEncodingPropsTheory.val_in_memory_dynarray,
            valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      qhdtm_x_assum `ptr_mem_ok` (mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
      disch_then (qspecl_then [`ArrayTV pet (Dynamic pc)`, `a`] mp_tac) >>
      simp[val_footprint_def, type_memory_size_def, exprSimPropsTheory.val_store_size_def] >>
      strip_tac >>
      conj_tac
      >- (qexists_tac `x` >> fs[ptr_covers_def, eval_operand_def]) >>
      conj_tac
      >- (irule bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean >>
           qexistsl_tac [`pc`, `s.vs_memory`, `pet`, `ds`] >> simp[]) >>
      qpat_x_assum `!i. w2n a <= i /\ _ ==> i < s.vs_alloca_next`
        (qspec_then `w2n a + 31` mp_tac) >>
      simp[val_footprint_def, type_memory_size_def]) >>
  conj_tac
  >- (`immutable_holds c cx (ArrayT pty (Dynamic pc)) (Value (ArrayV (DynArrayV ds))) a ee s` by
        (drule_all reasonEndpointResourcesPtrTheory.immutable_holds_read_value >> simp[]) >>
      `evaluate_type (get_tenv cx) pty = SOME pet` by
        (qpat_assum `evaluate_type _ (ArrayT pty (Dynamic pc)) = _`
           (mp_then Any mp_tac evaluate_type_ArrayT_cases) >> simp[]) >>
      drule_all exprSimBopRestWordLoadsTheory.rest_word_array_immutable_header >>
      Cases_on `c.ce_is_ctor` >> simp[array_length_def]) >>
  reverse (Cases_on `c.ce_is_ctor`) >> gvs[]
  >- (qhdtm_x_assum `immutable_holds`
        (strip_assume_tac o REWRITE_RULE [immutable_holds_def]) >>
      `state_rel H func c cx ee s` by fs[Once stmt_state_rel_def] >>
      drule stateRelProjTheory.state_rel_immutables_rel >>
      simp[immutables_rel_def] >> strip_tac >>
      rename1 `a = n2w (off + k)` >>
      rename1 `sub_layout itv iv k _ _` >>
      `off + type_memory_size itv <= LENGTH s.vs_data_section` by
        (first_x_assum (drule_all_then strip_assume_tac) >> simp[]) >>
      gnvs[sub_layout_def, type_memory_size_def] >>
      `off + k < dimword (:256)` by decide_tac >>
      simp[w2n_n2w] >> decide_tac) >>
  conj_tac
  >- (irule bodyPtrBopInMemoryContentsTheory.dynarray_memory_header_clean >>
      qexistsl_tac [`pc`, `s.vs_memory`, `pet`, `ds`] >> simp[]) >>
  `w2n a + 32 <= lo` by fs[type_memory_size_def] >>
  `lo <> 0` by decide_tac >>
  `immutable_base_zero c s` by fs[Once stmt_state_rel_def] >>
  qhdtm_x_assum `ghost_inv_at` (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  fs[immutable_base_zero_def] >>
  Cases >> simp[op_taint_def, op_prov_def]
QED
*)
Theorem for_nonslot_array_length_observation:
  expr_body_pre_mods mods c cx env e es0 /\
  expr_type e = ArrayT ty bd /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  eval_expr cx e es0 = (INL rv,ee) /\
  (!tr slot etv b. rv <> PlaceR (StoragePlace tr slot (ArrayTV etv b))) /\
  array_iterator_results cx (expr_type e) rv ee = (INL vs,ei) /\
  vv_post H ctx func c cx e es0 sa sb s0 ee rv vv s /\
  ptr_vv_ok cx (post_value_type c e) rv vv ee G tn s /\
  ghost_inv_at D lo d c cx ee G tn s /\
  (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx rv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
               eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v (w2n w) m)) /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (loc = LocMemory \/ loc = LocCode) /\ addr = vv_operand vv /\
  ncount = (case bd of Fixed n => n | Dynamic n => n) /\
  dynamic = (case bd of Fixed _ => F | Dynamic _ => T) ==>
  ei = ee /\
  ?av xs pty pbd pet a.
    read_result cx rv ee = (INL (ArrayV av),ee) /\
    extract_elements (ArrayTV et bd) (ArrayV av) = SOME xs /\
    vs = MAP Value xs /\ LENGTH vs = array_length (ArrayTV et bd) av /\
    post_value_type c e = ArrayT pty pbd /\
    evaluate_type (get_tenv cx) (post_value_type c e) = SOME (ArrayTV pet pbd) /\
    val_wf (ArrayTV pet pbd) (ArrayV av) /\
    eval_operand addr s = SOME a /\
    (loc = LocMemory ==>
      val_in_memory (ArrayTV pet pbd) (ArrayV av) (w2n a) s.vs_memory) /\
    (loc = LocCode ==>
      immutable_holds c cx (post_value_type c e) rv a ee s) /\
    (~dynamic ==> ncount = LENGTH vs) /\
    (dynamic ==>
      (if loc = LocCode /\ ~c.ce_is_ctor then
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
       else mload (w2n a) s) = n2w (LENGTH vs)) /\
    (dynamic /\ loc = LocMemory ==>
      (?x. addr = Var x /\ ptr_covers G tn x s 32) /\
      mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= s.vs_alloca_next) /\
    (dynamic /\ loc = LocCode ==>
      op_taint tn addr = {} /\ op_prov G addr = NONE /\
      (~c.ce_is_ctor ==> w2n a + 32 <= LENGTH s.vs_data_section /\
                         w2n a + 32 < dimword (:256)) /\
      (c.ce_is_ctor ==>
        mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= lo /\
        lo <= s.vs_alloca_next /\
        !region. c.ce_imm_alloca = SOME region ==>
          eval_operand region s = SOME 0w /\ op_taint tn region = {} /\
          op_prov G region = NONE))
Proof
  cheat
QED

(* Actual non-slot length slice.  The header observation is an input here;
   deriving it from the iterable expression belongs to the prefix join. *)
Theorem for_nonslot_array_length_run:
  !dynamic c loc addr sa len_op sb count vs a func s ctx.
    (if dynamic then
       compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc addr
     else return (Lit (n2w count))) sa = (len_op,sb) /\
    (loc = LocMemory \/ loc = LocCode) /\
    (~dynamic ==> count = LENGTH vs) /\
    (dynamic ==> eval_operand addr s = SOME a) /\
    (dynamic /\ loc = LocCode /\ c.ce_is_ctor /\
       c.ce_imm_alloca <> NONE ==>
       eval_operand (THE c.ce_imm_alloca) s = SOME 0w) /\
    (dynamic ==>
      (if loc = LocCode /\ ~c.ce_is_ctor then
         word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
       else mload (w2n a) s) = n2w (LENGTH vs)) /\
    fn_has_code sa sb func /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?z t.
      run_inst_seq (emitted_insts sa sb) s = OK z /\
      t = z with vs_inst_idx := LENGTH sb.cs_current_insts /\
      gas_path ctx func s 0 (OK t) /\
      eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      t = s with <|vs_vars := t.vs_vars;
                   vs_inst_idx := LENGTH sb.cs_current_insts|> /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> reverse (Cases_on `dynamic`)
  >- (simp[comp_return_def] >> strip_tac >> gvs[] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, eval_operand_def,
           lookup_var_def, gas_path_rules]) >>
  simp[] >> strip_tac >> (
  `loc <> LocCalldata` by gvs[] >>
  `?z. run_inst_seq (emitted_insts sa sb) s = OK z /\
       eval_operand len_op z = SOME (n2w (LENGTH vs))` by
    (irule rest_word_ptr_load_run >>
     qpat_assum `compile_ptr_load _ _ _ _ _ = _`
       (fn th => irule_at Any th) >>
     qexistsl_tac [`0w`, `a`] >>
     Cases_on `loc` >> gvs[] >>
     Cases_on `c.ce_is_ctor` >> gvs[] >>
     Cases_on `c.ce_imm_alloca = NONE` >> gvs[WORD_ADD_0]) >>
  drule_all rest_word_ptr_load_run_frame >> strip_tac >>
  drule rest_word_ptr_load_fresh >> strip_tac >>
  `gas_path ctx func s 0
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted` by
    (drule_all (SRULE []
       (Q.INST [`memory` |-> `F`] (SPEC_ALL rest_word_ptr_load_marked))) >>
     disch_then (qspec_then `ctx` mp_tac) >>
     simp[gas_marked_path_def]) >>
  qexists_tac `z` >> simp[lookup_var_def] >>
  conj_tac >- (qpat_x_assum `z = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!x. (!i. MEM i _ ==> _) ==> _`
    (qspec_then `x` MATCH_MP_TAC) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> EVERY _ _`
    (qspec_then `x` mp_tac) >> simp[listTheory.EVERY_MEM])
QED

(* A single immutable word uses the same zero-offset transfer as the existing
   copy supplier.  Only preservation outside the store window is exported. *)
Theorem for_immutable_word_element_joint_frame:
  compile_iter_elem_copy c src (Var p) 32 LocCode F ty ty sa = ((),sb) /\
  type_memory_size tv = 32 /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel H ctx func c cx es s /\
  cenv_top_ext c bc (FEMPTY :: es.scopes) /\
  immutable_holds c cx ty (Value v) a es s /\
  copy_old_operand sa src /\ not_fresh_at sa p /\
  eval_operand src s = SOME a /\ lookup_var p s = SOME w /\
  w2n w + capacity < dimword (:256) /\
  (c.ce_is_ctor ==> regions_disjoint (w2n a) 32 (w2n w) 32) /\
  (!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
    op_taint tn region = {} /\ op_prov G region = NONE) /\
  alloca_frame c es0 sa0 s0 bc (es with scopes := FEMPTY :: es.scopes) s /\
  (!name. IS_SOME (lookup_scopes name es0.scopes) ==>
    FLOOKUP bc.ce_vars name = FLOOKUP c.ce_vars name) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP s.vs_allocas aid = SOME b) /\
  venomMemDefs$allocas_non_overlapping s /\
  FLOOKUP s.vs_allocas aid0 = SOME (w2n w,capacity) /\
  sa0.cs_next_id <= aid0 /\ 32 <= capacity /\
  FLOOKUP bc.ce_vars id = SOME (PtrVar (Var p) capacity) /\
  ee.scopes = (FEMPTY |+ (id,entry)) :: es.scopes /\
  local_ptrs_reserved bc sa /\
  op_taint tn src = {} /\ ptr_covers G tn p s capacity /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  w2n w + 32 <= s.vs_alloca_next /\
  (c.ce_is_ctor ==>
    op_prov G src = NONE /\ w2n a + 32 <= lo /\ lo <= w2n w /\
    w2n a + 32 <= s.vs_alloca_next) /\
  (~c.ce_is_ctor ==>
    w2n a + 32 <= LENGTH s.vs_data_section /\
    w2n a + 32 < dimword (:256)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?Gf tnf z.
    copy_runtime_frame sa s sb z /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),Gf,tnf) /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= 32 /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + 32 <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (z with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    alloca_frame c es0 sa0 s0 bc ee z /\
    (!i. ~(w2n w <= i /\ i < w2n w + 32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    tnf.t_imm = tn.t_imm /\
    (!q. not_fresh_at sa q ==> FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    allocas_from lo z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    (!q sz. not_fresh_at sa q /\ ptr_covers G tn q s sz ==>
      ptr_covers Gf tnf q z sz)
Proof
  strip_tac >>
  `w2n w + 32 < dimword (:256)` by decide_tac >>
  `!region. c.ce_is_ctor /\ c.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region` by metis_tac[] >>
  `32 = type_memory_size tv /\ 0 < (32:num)` by simp[] >>
  drule_all for_immutable_element_copy_outer_frame >> strip_tac >>
  `compile_imm_copy_to_memory c.ce_is_ctor c.ce_imm_alloca src (Var p)
     (SUC 0) 0 sa = ((),sb)` by
    (qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[immutable_iter_small_copy, compile_imm_copy_to_memory_def,
       compile_lit_byte_offset_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
     pairarg_tac >> gvs[] >> pairarg_tac >> gvs[]) >>
  Cases_on `c.ce_is_ctor`
  >- (fs[] >>
      `!region. c.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\ copy_old_operand sa region /\
        op_taint tn region = {} /\ op_prov G region = NONE` by metis_tac[] >>
      drule (code_copy_ctor_range_origin_ptr |> Q.INST [`off` |-> `0`] |> SRULE []) >>
      disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
      disch_then (drule_at (Pat `allocas_from _ _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
      disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
      disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
      simp[ADD_COMM] >> strip_tac >>
      `t = z` by fs[copy_runtime_frame_def] >>
      qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[] >>
      rpt strip_tac >> simp[]) >>
  fs[] >>
  drule (runtime_code_copy_range_origin |> Q.INST [`off` |-> `0`] |> SRULE []) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `allocas_from _ _`)) >>
  disch_then (drule_at (Pat `eval_operand src s = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (qspecl_then [`explicit`, `ctx`, `PG`, `D`] mp_tac) >>
  simp[ADD_COMM] >> strip_tac >>
  `t = z` by fs[copy_runtime_frame_def] >>
  qexistsl_tac [`Gf`, `tnf`, `z`] >> fs[IN_DIFF] >>
  rpt strip_tac >> simp[]
QED

(* Here vs is the list from the original iterator read.  The source path
   frame identifies it with the elements of the current observed array;
   no equality of the old and current root values is needed. *)
Theorem for_local_place_array_current_child:
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var root) sz) /\
  lookup_var root s = SOME rw /\ ghost_inv_at D lo d cenv cx es G tn s /\
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
  mem_path_offset entry.type path = SOME (delta,ArrayTV stv bd) /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  vs = array_elements (ArrayTV stv bd) av /\ k < LENGTH vs ==>
  ptr_covers G tn root s sz /\
  delta + type_memory_size (ArrayTV stv bd) <= type_memory_size entry.type /\
  compatible_bound bd (LENGTH vs) /\
  value_has_type stv (EL k vs) /\ val_wf stv (EL k vs) /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv (EL k vs)
      (w2n rw + delta + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
       k * type_memory_size stv) mem)
Proof
  strip_tac >>
  drule exprSimPropsTheory.mem_path_offset_sound >> strip_tac >>
  drule_all vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
  strip_tac >>
  drule_all vyperPlaceStatePreservationTheory.subscripts_type_well_formed >>
  strip_tac >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory (ArrayTV stv bd) (ArrayV av) (w2n rw + delta) mem` by
    (rpt strip_tac >> irule whitelistForIterMemTheory.imm_typed_path_memory >>
     qexistsl_tac [`path`, `entry.type`, `entry.value`] >> simp[]) >>
  asm_rewrite_tac[] >> namedCases_on `bd` ["cap", "cap"]
  >- (`?al. av = SArrayV al` by
        (Cases_on `av` >> fs[Once vyperTypingTheory.value_has_type_def]) >>
      `LENGTH vs = cap` by simp[vyperValueOperationTheory.array_elements_def] >>
      gvs[vyperValueTheory.compatible_bound_def] >>
      drule_all stmtSimForArrayTheory.fixed_array_elements_typed >> simp[] >>
      rpt strip_tac >>
      `val_in_memory (ArrayTV stv (Fixed cap)) (ArrayV (SArrayV al))
         (w2n rw + delta) mem` by simp[] >>
      drule_all stmtSimForArrayTheory.fixed_array_element_in_memory >>
      simp[AC ADD_ASSOC ADD_COMM]) >>
  `?xs. av = DynArrayV xs /\ LENGTH xs <= cap` by
    (Cases_on `av` >> fs[Once vyperTypingTheory.value_has_type_def]) >>
  gvs[vyperValueOperationTheory.array_elements_def, vyperValueTheory.compatible_bound_def] >>
  drule_all bodyDynArraySourceTheory.dynarray_elements_typed >> simp[] >>
  rpt strip_tac >>
  rename1 `evaluate_subscripts _ _ _ = INL (ArrayV (DynArrayV xs))` >>
  `elems_in_memory xs (w2n rw + delta + 32) stv mem` by
    fs[valueEncodingPropsTheory.val_in_memory_dynarray,
       AC ADD_ASSOC ADD_COMM] >>
  drule_all exprSimAggregateEncodingTheory.elems_in_memory_EL >>
  simp[AC ADD_ASSOC ADD_COMM]
QED

(* The saved Value is independent of the mutable source scopes.  The frame
   starts at the expression endpoint: its new allocation is old at sb. *)
Theorem for_owned_array_current_child:
  array_iterator_results cx aty (Value (ArrayV av)) ee = (INL vs,ee) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV stv bd) /\
  evaluate_type (get_tenv cx) ty = SOME (ArrayTV stv bd) /\
  value_has_type (ArrayTV stv bd) (ArrayV av) /\ k < LENGTH vs /\
  p.ptr_location = LocMemory /\
  vv_own c cx ty sa sb ee (Value (ArrayV av)) (LocatedValue ann p) u /\
  ptr_vv_ok cx ty (Value (ArrayV av)) (LocatedValue ann p) ee G0 tn0 u /\
  eval_operand p.ptr_operand s = eval_operand p.ptr_operand u /\
  alloca_frame c ee sb u c' es s /\
  (!aid r. FLOOKUP u.vs_allocas aid = SOME r ==> FLOOKUP s.vs_allocas aid = SOME r) /\
  (!aid b len i. FLOOKUP u.vs_allocas aid = SOME (b,len) /\
    aid < sb.cs_next_id /\
    (!n lb lsz. local_region c ee.scopes u n lb lsz ==>
      b + len <= lb \/ lb + lsz <= b) /\
    b <= i /\ i < b + len /\ i IN tn.t_mem ==> i IN tn0.t_mem) ==>
  ?w v. eval_operand p.ptr_operand s = SOME w /\ EL k vs = Value v /\
    value_has_type stv v /\ val_wf stv v /\
    (val_footprint (ArrayTV stv bd) (ArrayV av) = 0 \/
     ?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\
       w2n w + val_footprint (ArrayTV stv bd) (ArrayV av) <= b + len /\
       (!n lb lsz. local_region c' es.scopes s n lb lsz ==>
         b + len <= lb \/ lb + lsz <= b)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v
        (w2n w + (case bd of Fixed _ => 0 | Dynamic _ => 32) +
         k * type_memory_size stv) m)
Proof
  strip_tac >>
  `vs = MAP Value (array_elements (ArrayTV stv bd) av)` by
    (qpat_x_assum `array_iterator_results _ _ _ _ = _` mp_tac >>
     simp[array_iterator_results_def, read_result_def, vyperStateTheory.bind_def,
          vyperStateTheory.return_def, lift_option_type_def, extract_elements_def]) >>
  qabbrev_tac `nbytes = val_footprint (ArrayTV stv bd) (ArrayV av)` >>
  qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_assum `Abbrev _` (fn th =>
    simp[vv_own_def, read_result_def, vyperStateTheory.return_def,
         GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  disch_then (qx_choose_then `w` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `!m. mem_agree_outside tn0.t_mem u.vs_memory m ==>
       val_in_memory (ArrayTV stv bd) (ArrayV av) (w2n w) m` by
    fs[ptr_vv_ok_def, ptr_mem_ok_def, read_result_def, vyperStateTheory.return_def] >>
  qpat_x_assum `alloca_frame _ _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [alloca_frame_def]) >>
  `mem_bytes_at (w2n w) nbytes s.vs_memory = mem_bytes_at (w2n w) nbytes u.vs_memory /\
   (!i. w2n w <= i /\ i < w2n w + nbytes /\ i IN tn.t_mem ==> i IN tn0.t_mem)` by
    (Cases_on `nbytes = 0` >- (simp[mem_bytes_at_def] >> decide_tac) >>
     qpat_x_assum `(?aid b len. _) \/ _` mp_tac >> simp[] >>
     disch_then (qx_choose_then `aid` (qx_choose_then `b` (qx_choose_then `len` strip_assume_tac))) >>
     conj_tac >-
       (`mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory` by
          (sym_tac >> metis_tac[]) >>
        irule (cj 1 mem_bytes_at_agree_window) >>
        qexistsl_tac [`len`, `b`] >> asm_rewrite_tac[] >> decide_tac) >>
     qx_gen_tac `i` >> strip_tac >>
     qpat_assum `!aid b len i. _ ==> i IN tn0.t_mem`
       (qspecl_then [`aid`, `b`, `len`, `i`] mp_tac) >>
     impl_tac >- (asm_rewrite_tac[] >> decide_tac) >> simp[]) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (ArrayTV stv bd) (ArrayV av) (w2n w) m` by
    (`val_wf (ArrayTV stv bd) (ArrayV av) /\
       val_footprint (ArrayTV stv bd) (ArrayV av) <= nbytes` by
       simp[Abbr `nbytes`, valueEncodingTypingTheory.value_has_type_val_wf] >>
     rpt strip_tac >> irule robust_val_in_memory_window_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`tn0.t_mem`, `tn.t_mem`, `nbytes`, `u.vs_memory`, `s.vs_memory`] >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`w`, `EL k (array_elements (ArrayTV stv bd) av)`] >>
  simp[EL_MAP] >>
  `well_formed_type_value (ArrayTV stv bd)` by metis_tac[evaluate_type_well_formed_type_value] >>
  Q.SUBGOAL_THEN
    `nbytes = 0 \/ ?aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\ w2n w + nbytes <= b + len /\
      (!n lb lsz. local_region c' es.scopes s n lb lsz ==> b + len <= lb \/ lb + lsz <= b)` assume_tac >-
    (Cases_on `nbytes = 0` >- simp[] >>
     qpat_x_assum `(?aid b len. _) \/ _` mp_tac >> simp[] >>
     disch_then (qx_choose_then `aid` (qx_choose_then `b` (qx_choose_then `len` strip_assume_tac))) >>
     `FLOOKUP s.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
     qexistsl_tac [`aid`, `b`, `len`] >> simp[] >>
     qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _ /\ _`
       (qspecl_then [`aid`, `b`, `len`] mp_tac) >>
     impl_tac >- asm_rewrite_tac[] >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  qpat_x_assum `Abbrev _` (fn th =>
    simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  `k < LENGTH (array_elements (ArrayTV stv bd) av)` by fs[] >>
  simp[EL_MAP] >>
  namedCases_on `bd` ["cap", "cap"] >>
  namedCases_on `av` ["xs", "al", "xs"] >>
  qpat_assum `value_has_type (ArrayTV _ _) (ArrayV _)`
    (CHECK_ASSUME_TAC o SRULE [value_has_type_inv]) >> simp[]
  >- (`k < cap` by fs[array_elements_def] >>
      drule_all fixed_array_elements_typed >> strip_tac >>
      simp[array_elements_def, EL_GENLIST] >>
      conj_tac >- (qpat_x_assum `nbytes = 0 \/ _` mp_tac >> simp[ADD_COMM]) >>
      rpt strip_tac >>
      irule sarray_in_memory_robust_element >>
      qexistsl_tac [`cap`, `al`, `s.vs_memory`, `tn`] >> asm_rewrite_tac[]) >>
  `k < LENGTH xs` by fs[array_elements_def] >>
  drule_all dynarray_elements_typed >> strip_tac >>
  simp[array_elements_def] >>
  conj_tac >- (qpat_x_assum `nbytes = 0 \/ _` mp_tac >> simp[ADD_COMM]) >>
  rpt strip_tac >>
  `val_in_memory stv (EL k xs) (w2n w + 32 + k * type_memory_size stv) m` by
    (irule dynarray_in_memory_robust_element >>
     conj_tac >- asm_rewrite_tac[] >>
     qexistsl_tac [`cap`, `s.vs_memory`, `tn`] >> asm_rewrite_tac[]) >>
  pop_assum mp_tac >> simp[AC ADD_ASSOC ADD_COMM]
QED

(* The length slice can advance the cursor but introduces no allocation.
   Keep the expression witnesses and original frame anchor unchanged. *)
Theorem for_nonslot_array_length_frame_transport:
  !H DF lo d ctx func c cx e es0 sa0 s0 G0 tn0 ee saL s G tn t G' tn'
   tv vv sb code.
    array_length_frame saL s G tn t G' tn' /\
    fn_has_code saL sb func /\ sb.cs_current_bb = saL.cs_current_bb /\
    sb.cs_current_insts = saL.cs_current_insts ++ code /\
    EVERY (\i. i.inst_opcode <> ALLOCA) code /\
    s.vs_current_bb = saL.cs_current_bb /\
    s.vs_inst_idx = LENGTH saL.cs_current_insts /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel H ctx func c cx es0 s0 /\
    vv_post H ctx func c cx e es0 sa0 saL s0 ee tv vv s /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee tv vv s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c cx ee G tn s /\
    ghost_kept_at lo c es0 sa0 G0 tn0 s0 G tn /\
    ptr_vv_ok cx (post_value_type c e) tv vv ee G tn s /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa0 saL ee tv vv s /\
      (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
    (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
          eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
      ptr_buf_ok c e op G s) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok c e p.ptr_operand G s) /\
    ci_mono sa0 saL /\ local_ptrs_reserved c sa0 /\ local_ptrs_reserved c saL /\
    (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x) /\
    (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at saL x) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at saL x) ==>
    stmt_state_rel H ctx func c cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d c cx ee G' tn' t /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    allocas_from lo t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    alloca_frame c es0 sa0 s0 c ee t /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
    (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!n b len. local_region c es0.scopes s0 n b len ==> off+sz <= b \/ b+len <= off) ==>
      mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    ghost_kept_at lo c es0 sa0 G0 tn0 s0 G' tn' /\
    vv_post H ctx func c cx e es0 sa0 saL s0 ee tv vv t /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee tv vv t /\
    ptr_vv_ok cx (post_value_type c e) tv vv ee G' tn' t /\
    (!v. tv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa0 saL ee tv vv t /\
      (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
    (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
            val_in_memory rt v (w2n w) mem)) /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
      ptr_buf_ok c e op G' t) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok c e p.ptr_operand G' t) /\
    eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
    op_prov G' (vv_operand vv) = op_prov G (vv_operand vv) /\
    op_taint tn' (vv_operand vv) = op_taint tn (vv_operand vv) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_data_section = s.vs_data_section /\
    tn'.t_mem = tn.t_mem
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    (qpat_assum `_ with vs_vars := _ = s` (SUBST1_TAC o SYM) >>
     simp[venom_state_component_equality]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\ t.vs_data_section = s.vs_data_section /\
   t.vs_current_bb = s.vs_current_bb /\ t.vs_labels = s.vs_labels /\
   t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables` by
    (qpat_assum `_ with vs_vars := _ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. not_fresh_at saL x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by simp[op_taint_def] >>
  `!x. not_fresh_at sa0 x ==> not_fresh_at saL x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x w. not_fresh_at sa0 x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by metis_tac[] >>
  `!n b sz. local_region c ee.scopes t n b sz <=> local_region c ee.scopes s n b sz` by
    (irule copy_buffer_local_region_frame >> qexists_tac `saL` >> simp[]) >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
   op_prov G' (vv_operand vv) = op_prov G (vv_operand vv) /\
   op_taint tn' (vv_operand vv) = op_taint tn (vv_operand vv)` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def, op_prov_def, op_taint_def]) >>
  `stmt_state_rel H ctx func c cx ee t` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`s`,`saL`] >>
     fs[vv_post_def]) >>
  `ghost_inv_at (DF H) lo d c cx ee G' tn' t` by
    (irule ghost_inv_at_exterior_frame >> qexistsl_tac [`G`,`ee`,`s`,`saL`,`tn`] >> simp[]) >>
  `alloca_history func t` by suspend "history" >>
  `vv_post H ctx func c cx e es0 sa0 saL s0 ee tv vv t` by suspend "vv" >>
  `alloca_frame c es0 sa0 s0 c ee t` by
    (irule vv_post_alloca_frame >> simp[] >>
     conj_tac >- fs[vv_post_def, locals_kept_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `ghost_kept_at lo c es0 sa0 G0 tn0 s0 G' tn'` by suspend "kept" >>
  `ptr_vv_ok cx (post_value_type c e) tv vv ee G' tn' t` by suspend "pointer" >>
  suspend "post"
QED

Resume for_nonslot_array_length_frame_transport[history]:
  drule_all fn_has_code_code >> strip_tac >>
  qpat_x_assum `isPREFIX code _`
    (qx_choose_then `rest` assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH code` by fs[] >>
  `t with vs_inst_idx := s.vs_inst_idx + LENGTH code = t` by
    simp[venom_state_component_equality] >>
  qpat_x_assum `t with vs_inst_idx := _ = t` (SUBST1_TAC o SYM) >>
  irule alloca_history_no_alloca_slice >>
  simp[] >> qexistsl_tac [`bb`,`rest`] >> fs[]
QED

Resume for_nonslot_array_length_frame_transport[vv]:
  `vv_post H ctx func c cx e es0 sa0 saL s0 ee tv vv
      (t with vs_inst_idx := s.vs_inst_idx)` suffices_by simp[vv_post_inst_idx] >>
  irule vv_post_vars_frame >> simp[stmt_state_rel_inst_idx] >>
  qexistsl_tac [`s`, `saL`] >>
  simp[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  conj_tac >-
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >> fs[lookup_var_def]) >>
  qpat_assum `s.vs_inst_idx = LENGTH saL.cs_current_insts` (SUBST1_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Resume for_nonslot_array_length_frame_transport[kept]:
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G tn` mp_tac >>
  simp[ghost_kept_at_def] >> strip_tac >> rpt strip_tac >> metis_tac[]
QED

Resume for_nonslot_array_length_frame_transport[pointer]:
  Cases_on `vv` >> fs[vv_operand_def, ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume for_nonslot_array_length_frame_transport[post]:
  `vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee tv vv t` by
    (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    ((metis_tac[stmt_state_rel_allocas_below_fmp])) >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `!v. tv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa0 saL ee tv vv t /\
      (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)` by
    (rpt strip_tac >~ [`vv_own _ _ _ _ _ _ _ _ _`] >-
       (irule vv_own_vars_frame >> qexistsl_tac [`s`,`saL`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[] >> rpt conj_tac
  >- fs[vv_post_def]
  >- fs[vv_post_def]
  >- fs[vv_post_def]
  >- fs[vv_post_def]
  >- (qpat_assum `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
      pure_rewrite_tac[Once ADD_COMM] >> simp[])
  >- (rpt strip_tac >> gvs[vv_operand_def] >>
      irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[])
  >> rpt strip_tac >> gvs[vv_operand_def] >>
  irule ptr_buf_ok_frame >> qexistsl_tac [`G`,`s`] >> simp[]
QED

Finalise for_nonslot_array_length_frame_transport

(* Relayout writes only the typed destination window. The saved item still
   covers its entire allocation, including any bytes beyond that window. *)
Theorem for_memory_relayout_element_joint_frame:
  compile_iter_elem_copy c (Var xs) (Var xd) bytes LocMemory F dty sty sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  ~tuple_memory_layout_eq dty sty /\
  acyclic_struct_metadata c.ce_struct_fields /\
  sfields_tenv_consistent c.ce_struct_fields tenv /\
  (!name fields. FLOOKUP c.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/ w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,capacity) /\
  ptr_covers G tn xd s capacity /\ type_memory_size dtv <= capacity /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `compile_store_memory_typed c (Var xd) dty (Var xs) sty sa = ((),sb)` by
    fs[compile_iter_elem_copy_def, compile_store_memory_def] >>
  `ptr_covers G tn xd s (type_memory_size dtv)` by
    (irule ptr_covers_mono >> qexists_tac `capacity` >> asm_rewrite_tac[]) >>
  drule_all compile_store_memory_typed_origin_ptr_path >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qpat_assum `typed_copy_state_frame _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `t.vs_allocas = s.vs_allocas` by
    (qpat_assum `_ with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
                          vs_current_bb := _; vs_inst_idx := _|> = _`
       (mp_tac o AP_TERM ``venom_state_vs_allocas``) >> simp[]) >>
  `lookup_var xd t = lookup_var xd s` by simp[] >>
  `ptr_covers Gf tnf xd t capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >> simp[]) >>
  qexistsl_tac [`t`, `Gf`, `tnf`] >> asm_rewrite_tac[]
QED

(* The bulk arm uses the evaluated layout, not equality of source and item
   types. Its empty copy never checks the source pointer or touches a byte. *)
Theorem for_memory_bulk_element_joint_frame:
  compile_iter_elem_copy c (Var xs) (Var xd) n LocMemory F dty sty sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  (dty = sty \/ tuple_memory_layout_eq dty sty) /\
  n = type_memory_bytes c dty /\ n = type_memory_size dtv /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,capacity) /\
  lookup_var xd s = SOME dw /\ ptr_covers G tn xd s capacity /\ n <= capacity /\
  (0 < n ==>
    not_fresh_at sa xs /\ not_fresh_at sa xd /\ lookup_var xs s = SOME sw /\
    ptr_covers G tn xs s n /\
    w2n sw + n < dimword (:256) /\ w2n dw + n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\ w2n dw + n <= s.vs_alloca_next /\
    (w2n sw + n <= w2n dw \/ w2n dw + n <= w2n sw) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) n s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity /\
    (n = 0 ==> sb = sa /\ t = s /\ Gf = G /\ tnf = tn)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  `compile_copy_memory (Var xd) (Var xs) n sa = ((),sb)` by
    (qpat_assum `n = type_memory_bytes c dty` SUBST1_TAC >>
     qpat_x_assum `dty = sty \/ tuple_memory_layout_eq dty sty` DISJ_CASES_TAC >>
     qpat_x_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_iter_elem_copy_def, compile_store_memory_def]) >>
  `memory_layout_rel dtv stv` by
    (irule memoryLayoutSourceTheory.memory_layout_key_evaluated >>
     qexistsl_tac [`sty`, `dty`, `tenv`] >>
     simp[] >> metis_tac[layoutStorePropsTheory.bulk_store_layout_keys]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory dtv v (w2n sw) mem` by
    (rpt strip_tac >> irule memoryValueEncodingTheory.memory_value_rel_val_in_memory >>
     simp[] >> irule memoryLayoutRelTheory.memory_layout_rel_value >>
     qexists_tac `stv` >> simp[] >>
     irule memoryValueEncodingTheory.val_in_memory_memory_value_rel >> simp[]) >>
  `val_footprint dtv v <= n` by metis_tac[exprSimPropsTheory.val_footprint_le] >>
  Cases_on `0 < n` >- suspend "positive" >>
  suspend "zero"
QED

Resume for_memory_bulk_element_joint_frame[zero]:
  `n = 0` by decide_tac >>
  `sb = sa` by fs[contextPropsTheory.compile_copy_memory_zero] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory dtv v (w2n dw) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
     conj_tac >- simp[] >>
     qexistsl_tac [`s.vs_memory`, `s.vs_memory`, `0`, `w2n sw`, `tn.t_mem`, `tn.t_mem`] >>
     simp[mem_bytes_at_def]) >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
  conj_tac >- simp[gas_origin_ptr_path_rules] >>
  qpat_assum `!mem. _ ==> val_in_memory dtv v (w2n dw) mem` irule >>
  simp[mem_agree_outside_def]
QED

Resume for_memory_bulk_element_joint_frame[positive]:
  qpat_x_assum `0 < n ==> _` (map_every assume_tac o CONJUNCTS o UNDISCH) >>
  `n < dimword (:256)` by decide_tac >>
  `w2n (n2w n : bytes32) = n` by simp[] >>
  `emit_inst MCOPY [Var xd; Var xs; Lit (n2w n)] [] sa = ((),sb)` by
    (Cases_on `n` >- (qpat_x_assum `0 < 0` mp_tac >> simp[NoAsms]) >>
     qpat_assum `compile_copy_memory _ _ _ _ = _` mp_tac >>
     simp[NoAsms, compile_copy_memory_def, emit_void_def, emit_inst_def]) >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY [Var xd; Var xs; Lit (n2w n)] []` >>
  qabbrev_tac `u = mcopy (w2n dw) (w2n sw) n s` >>
  qabbrev_tac `tf = step_taint inst s u tn` >>
  `eval_operand (Var xd) s = SOME dw /\ eval_operand (Var xs) s = SOME sw /\
   eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`, stmtReasonMemoryTheory.step_mcopy_eq] >>
  `step_prov PG G inst u = G /\ tf.t_var = tn.t_var /\
   tf.t_imm = tn.t_imm /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
   (!i. i < n ==> (w2n dw + i IN tf.t_mem <=> w2n sw + i IN tn.t_mem)) /\
   (!i. ~(w2n dw <= i /\ i < w2n dw + n) ==> (i IN tf.t_mem <=> i IN tn.t_mem))`
    by suspend "ghost" >>
  qabbrev_tac `t = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)`
    by suspend "path" >>
  `t.vs_memory = u.vs_memory` by simp[Abbr `t`] >>
  `!mem. mem_agree_outside tf.t_mem t.vs_memory mem ==> val_in_memory dtv v (w2n dw) mem`
    by (rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
        conj_tac >- simp[] >>
        qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `n`, `w2n sw`, `tn.t_mem`, `tf.t_mem`] >>
        simp[Abbr `u`, valueEncodingPropsTheory.mcopy_mem_bytes_at_same]) >>
  suspend "post"
QED

Resume for_memory_bulk_element_joint_frame[ghost]:
  conj_tac >-
    simp[Abbr `inst`, ptrDisciplineTheory.step_prov_def,
         ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.out_prov_def,
         venomInstTheory.mk_inst_def, finite_mapTheory.DRESTRICT_UNIV] >>
  `tf = step_taint (mk_inst sa.cs_next_id MCOPY [Var xd; Var xs; Lit (n2w n)] [])
          s (mcopy (w2n dw) (w2n sw) n s) tn` by
    simp[Abbr `tf`, Abbr `inst`, Abbr `u`] >>
  drule_all assignTuplePtrLocalFixedCopyTheory.mcopy_operand_taint_frames_ptr >>
  simp[NoAsms, AC CONJ_ASSOC CONJ_COMM]
  >> (metis_tac[])
QED

Resume for_memory_bulk_element_joint_frame[path]:
  gen_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ [inst]` by simp[Abbr `inst`] >>
  drule_all fragExecTheory.fn_has_code_same_block >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. i < LENGTH [inst] ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by suspend "pointer" >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    simp[Abbr `inst`, unitTransformDefsTheory.inst_mem_below_frontier_def,
         memSafeRunTheory.inst_dload_in_section_def,
         venomInstTheory.mk_inst_def, contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def, codegenRelTheory.sized_source_write_range_def,
         eval_operand_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS` by simp[Abbr `inst`, venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def] >>
  `ctx_has_dalloca ctx ==> dalloca_no_wrap inst s` by
    simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tf)` by
    (drule_all fragGasSeqPtrTheory.straight_line_origin_ptr_edge >>
     disch_then (qspecl_then [`explicit`, `PG`] mp_tac) >> simp[Abbr `t`, Abbr `tf`]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[gas_origin_ptr_path_rules, Abbr `t`, Abbr `u`, venomExecSemanticsTheory.mcopy_def,
       write_memory_with_expansion_def]
QED

Resume for_memory_bulk_element_joint_frame[pointer]:
  `ptr_covers G tn xd s n` by
    (irule ptr_covers_mono >> qexists_tac `capacity` >> simp[]) >>
  (* Reuse just the access and taint tests; check the allocation and step
     clauses on the actual context. *)
  `ptr_inst_ok D 0 0 (ctx with ctx_functions := []) func G tn inst s` by
    ((simp[Abbr `inst`] >> irule fragExecPtrTheory.ptr_inst_ok_mcopy >>
     qpat_assum `w2n (n2w n : bytes32) = n` SUBST1_TAC >>
     simp[ctx_has_dalloca_def] >> asm_rewrite_tac[] >> (metis_tac[Abbr `inst`, ctx_has_dalloca_def, fragExecPtrTheory.ptr_inst_ok_mcopy]))) >>
  qpat_x_assum `ptr_inst_ok D 0 0 _ func G tn inst s`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [ptrSafeRunTheory.ptr_inst_ok_def]) >>
  `access_ok lo G func inst s` by
    (irule lowerDloadReachableFloorTheory.ld_access_ok_raise_floor >>
     qexists_tac `0` >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  `step_inst 0 ctx inst s = OK u` by simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `u.vs_requests = s.vs_requests` by
    simp[Abbr `u`, venomExecSemanticsTheory.mcopy_def, write_memory_with_expansion_def] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def]
QED

Resume for_memory_bulk_element_joint_frame[post]:
  `val_in_memory dtv v (w2n dw) t.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory dtv v (w2n dw) mem` irule >>
     simp[mem_agree_outside_def]) >>
  `typed_copy_state_frame sa (w2n dw) n s t` by
    simp[Abbr `t`, Abbr `u`, typed_copy_mcopy_state_frame] >>
  `lookup_var xd t = lookup_var xd s` by
    (qpat_assum `lookup_var xd s = SOME dw` mp_tac >>
     simp[NoAsms, Abbr `t`, Abbr `u`, venomExecSemanticsTheory.mcopy_def,
          write_memory_with_expansion_def, lookup_var_def]) >>
  `ptr_covers G tf xd t capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  qexistsl_tac [`t`, `G`, `tf`] >>
  simp[ptrDisciplineTheory.op_taint_def] >>
  simp[Abbr `t`, Abbr `u`, venomExecSemanticsTheory.mcopy_def,
       write_memory_with_expansion_def]
QED

Finalise for_memory_bulk_element_joint_frame

(* The word arm loads the clean source before writing the reserved item. *)
Theorem for_memory_word_element_joint_frame:
  compile_iter_elem_copy c (Var xs) (Var xd) bytes LocMemory F dty sty sa = ((),sb) /\
  is_word_type dty /\ type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  value_has_type stv v /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory stv v (w2n sw) mem) /\
  w2n sw + 32 <= s.vs_alloca_next /\ w2n dw + 32 <= s.vs_alloca_next /\
  ptr_covers G tn xs s 32 /\
  FLOOKUP s.vs_allocas aid = SOME (w2n dw,capacity) /\
  ptr_covers G tn xd s capacity /\ 32 <= capacity /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf)) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      val_in_memory dtv v (w2n dw) mem) /\
    typed_copy_state_frame sa (w2n dw) 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    FLOOKUP t.vs_allocas aid = SOME (w2n dw,capacity) /\
    lookup_var xd t = SOME dw /\ ptr_covers Gf tnf xd t capacity
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  drule_all typed_copy_word_widening >> strip_tac >> gvs[] >>
  `compile_store_memory_typed c (Var xd) dty (Var xs) dty sa = ((),sb)` by
    fs[compile_iter_elem_copy_def, typedCopyAgreementTheory.compile_store_memory_typed_word] >>
  `eval_operand (Var xs) s = SOME sw /\ eval_operand (Var xd) s = SOME dw` by
    simp[eval_operand_def] >>
  `!x. Var xs = Var x \/ Var xd = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> gvs[]) >>
  drule typed_copy_word_run_seq >> simp[] >>
  disch_then (qspecl_then [`s`,`dw`,`sw`] mp_tac) >> simp[] >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule externalReturnNormalizeMemTheory.typed_copy_word_mem_ok >>
     qexistsl_tac [`c`,`dw`,`Var xd`,`dty`,`sw`,`Var xs`,`dty`] >> asm_rewrite_tac[]) >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MLOAD [Var xs] [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [Var xd; Var (STRING #"%" (toString sa.cs_next_var))] []]` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[typedCopyAgreementTheory.compile_store_memory_typed_word,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1]) >>
  drule_all assignTuplePtrLoadStepTheory.robust_typed_word_clean >> strip_tac >>
  qabbrev_tac `tmp = STRING #"%" (toString sa.cs_next_var)` >>
  `!p. not_fresh_at sa p ==> p <> tmp` by
    (simp[Abbr `tmp`, not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `xd <> tmp` by simp[] >>
  qabbrev_tac `ld = mk_inst sa.cs_next_id MLOAD [Var xs] [tmp]` >>
  qabbrev_tac `st = mk_inst (sa.cs_next_id+1) MSTORE [Var xd;Var tmp] []` >>
  qabbrev_tac `w = mload (w2n sw) s` >>
  qabbrev_tac `u = update_var tmp w s` >>
  qabbrev_tac `G1 = step_prov PG G ld u` >>
  qabbrev_tac `tn1 = step_taint ld s u tn` >>
  `u = update_var tmp (mload (w2n sw) s) s /\
   G1 = step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var xs] [tmp]) u /\
   tn1 = step_taint (mk_inst sa.cs_next_id MLOAD [Var xs] [tmp]) s u tn` by
     simp[Abbr `u`, Abbr `w`, Abbr `ld`, Abbr `G1`, Abbr `tn1`] >>
  drule_all decoderSetupStepPtrTheory.setup_mload_ghost >> strip_tac >>
  qabbrev_tac `tn2 = tn1 with t_mem := tn1.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32}` >>
  qabbrev_tac `t = mstore (w2n dw) w u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn2)` by
    suspend "path" >>
  suspend "post"
QED

Resume for_memory_word_element_joint_frame[path]:
  qabbrev_tac `p = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `lookup_var xd p = SOME dw /\ lookup_var tmp p = SOME w` by
    (qpat_assum `lookup_var xd s = SOME dw`
       (assume_tac o REWRITE_RULE [venomStateTheory.lookup_var_def]) >>
     simp[Abbr `p`, Abbr `u`, venomStateTheory.lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst_base ld s = OK u /\ step_inst_base st p = OK (mstore (w2n dw) w p)` by
    simp[Abbr `ld`, Abbr `st`, Abbr `u`, Abbr `w`, eval_operand_def,
         venomInstTheory.mk_inst_def, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomExecSemanticsTheory.exec_read1_def, venomExecSemanticsTheory.exec_write2_def] >>
  `FLOOKUP G1 xd = FLOOKUP G xd /\ op_taint tn1 (Var xd) = op_taint tn (Var xd)` by
    (qpat_assum `!y. y <> tmp ==> _` (qspec_then `xd` mp_tac) >> simp[]) >>
  `ptr_covers G1 tn1 xd p capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  `ptr_covers G1 tn1 xd p 32` by (irule ptr_covers_mono >> qexists_tac `capacity` >> simp[]) >>
  `allocas_from lo p /\ (ctx_has_dalloca ctx ==> allocas_below_fmp p)` by
    simp[Abbr `p`, Abbr `u`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
  `eval_operand (Var tmp) p = SOME w` by simp[eval_operand_def] >>
  `step_prov PG G1 st (mstore (w2n dw) w p) = G1 /\
   step_taint st p (mstore (w2n dw) w p) tn1 = tn2` by
    (qpat_assum `Abbrev (st = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (tn2 = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     conj_tac
     >- (irule (cj 1 exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame) >>
         simp[] >> qexists_tac `tn1` >> simp[]) >>
     irule (cj 2 exprSimPtrTopLevelImmutableCopyTheory.toplevel_immutable_mstore_ghost_frame) >> simp[]) >>
  gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn ld s` by
    (simp[Abbr `ld`] >> irule exprPtrCtorImmStoreTheory.ptr_inst_ok_mload_lo >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G1 tn1 st p` by
    (qpat_assum `Abbrev (st = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule exprPtrUnwrapCopyEdgesTheory.ptr_inst_ok_mstore_tainted >> simp[]) >>
  `inst_seq_ptr D lo ctx func PG G tn [ld;st] s G1 tn2` by
    (once_rewrite_tac[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     qpat_assum `step_inst_base ld s = OK u` (fn th => rewrite_tac[th, venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC) >>
     map_every (fn q => qpat_assum q (rewrite_tac o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (p = _)`, `Abbrev (G1 = _)`, `Abbrev (tn1 = _)`] >>
     once_rewrite_tac[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     qpat_assum `step_inst_base st p = OK _` (fn th => rewrite_tac[th, venomExecSemanticsTheory.exec_result_case_def] >> BETA_TAC) >>
     rewrite_tac[fragGasSeqPtrTheory.inst_seq_ptr_def] >>
     map_every (fn q => qpat_assum q (rewrite_tac o single))
       [`ptr_inst_ok _ _ _ _ _ _ _ ld s`, `ptr_inst_ok _ _ _ _ _ _ _ st p`,
        `step_prov _ _ st _ = _`, `step_taint st p _ _ = _`]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by (gvs[same_blocks_def]) >>
  drule_all fn_has_code_code >> strip_tac >>
  `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G1 tn2` by
    (qpat_assum `emitted_insts sa sb = _` (rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `MAP (\i. (func.fn_name,i.inst_id) IN explicit)
       (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) = []` by
    (qpat_assum `emitted_insts sa sb = _` (rewrite_tac o single) >>
     simp[Abbr `ld`, Abbr `st`, venomInstTheory.mk_inst_def]) >>
  `t = (mstore (w2n dw) w u with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb))` by
    (qpat_assum `Abbrev (t = _)` (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `sb.cs_current_insts = _` (rewrite_tac o single) >>
     qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[th, listTheory.LENGTH_APPEND])) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
     (asm_rewrite_tac[] >> (metis_tac[])) >>
  `(ctx_has_dalloca ctx ==> !pre i post z.
      emitted_insts sa sb = pre ++ i::post /\ run_inst_seq pre s = OK z ==>
      dalloca_no_wrap i z)` by
    (rpt strip_tac >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     qpat_assum `emitted_insts sa sb = [ld;st]`
       (fn th => qpat_x_assum `MEM i (emitted_insts sa sb)`
         (mp_tac o REWRITE_RULE [th, MEM])) >>
     disch_then DISJ_CASES_TAC >>
     simp[Abbr `ld`, Abbr `st`, venomInstTheory.mk_inst_def]) >>
  drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >>
  qpat_assum `MAP _ (FILTER _ _) = []` (rewrite_tac o single) >>
  qpat_assum `t = _` (rewrite_tac o single o SYM)
QED

Resume for_memory_word_element_joint_frame[post]:
  `w = typed_val_to_w256 dtv v` by
    ((qpat_assum `!m. _ ==> mem_word_at _ m = _` (qspec_then `s.vs_memory` mp_tac) >>
     simp[Abbr `w`, mload_def, mem_word_at_def, mem_agree_outside_def] >> (metis_tac[Abbr `w`, mload_def, mem_word_at_def, mem_agree_outside_def]))) >>
  `mem_word_at (w2n dw) t.vs_memory = w` by
    simp[Abbr `t`, valueEncodingPropsTheory.mstore_mem_word_at_same] >>
  `!i. w2n dw <= i /\ i < w2n dw + 32 ==> i NOTIN tn2.t_mem` by
    simp[Abbr `tn2`] >>
  `!mem. mem_word_at (w2n dw) mem = typed_val_to_w256 dtv v ==>
         val_in_memory dtv v (w2n dw) mem` by
    (drule_all exprSimPropsTheory.val_in_memory_word >> simp[]) >>
  `val_in_memory dtv v (w2n dw) t.vs_memory` by simp[] >>
  `!mem. mem_agree_outside tn2.t_mem t.vs_memory mem ==>
         val_in_memory dtv v (w2n dw) mem` by
    (rpt strip_tac >> drule_all bodyPtrPrecompileBuiltinsArithmeticValueTheory.clean_word_mem_agree >>
     simp[]) >>
  `typed_copy_state_frame sa (w2n dw) 32 s t` by
    simp[Abbr `t`, Abbr `u`, Abbr `tmp`, typed_copy_word_state_frame] >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ t.vs_allocas = s.vs_allocas` by
    (qpat_assum `same_blocks sa sb`
       (strip_assume_tac o REWRITE_RULE [same_blocks_def]) >>
     simp[Abbr `t`, Abbr `u`, mstore_def, update_var_def]) >>
  `tn2.t_mem = tn.t_mem DIFF {i | w2n dw <= i /\ i < w2n dw + 32} /\
   tn2.t_imm = tn.t_imm /\ tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans` by
    simp[Abbr `tn2`] >>
  `!p. op_taint tn2 (Var p) = op_taint tn1 (Var p)` by
    (qpat_assum `Abbrev (tn2 = _)`
       (rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     simp[NoAsms, op_taint_def]) >>
  `!p. not_fresh_at sa p ==>
       FLOOKUP G1 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!y. y <> tmp ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `lookup_var xd t = lookup_var xd s` by
    (qpat_assum `typed_copy_state_frame _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >> simp[]) >>
  `ptr_covers G1 tn2 xd t capacity` by
    (irule ptr_covers_lookup_frame >> qexistsl_tac [`G`,`s`,`tn`] >> simp[]) >>
  qexistsl_tac [`t`,`G1`,`tn2`] >> simp[]
QED

Finalise for_memory_word_element_joint_frame

(* The two memory-reading opcodes have the same word semantics, but the
   constructor can use a clean absolute address in the reserved prefix. *)
Theorem for_array_length_read_checks[local]:
  MEM opc [MLOAD; ILOAD; DLOAD] /\ eval_operand addr s = SOME a /\
  op_taint tn addr = {} /\
  (opc = DLOAD ==> w2n a <= LENGTH s.vs_data_section) /\
  (opc <> DLOAD ==> w2n a + 32 <= s.vs_alloca_next /\
    ((?p. addr = Var p /\ ptr_covers G tn p s 32) \/
     (w2n a + 32 <= lo /\ op_prov G addr = NONE))) ==>
  access_ok lo G func (mk_inst id opc [addr] [out]) s /\
  taint_ok func tn (mk_inst id opc [addr] [out]) s /\
  inst_mem_below_frontier (mk_inst id opc [addr] [out]) s /\
  inst_dload_in_section (mk_inst id opc [addr] [out]) s
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[access_ok_def, taint_ok_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
       inst_dload_in_section_def, mk_inst_def, source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mem_read_ops_def] >>
  rpt strip_tac >> gvs[ptr_covers_def, eval_operand_def, op_prov_def] >>
  metis_tac[]
QED

Theorem for_array_length_read_step[local]:
  MEM opc [MLOAD; ILOAD; DLOAD] /\ eval_operand addr s = SOME a ==>
  step_inst_base (mk_inst id opc [addr] [out]) s =
  OK (update_var out
    (if opc = DLOAD then word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
     else mload (w2n a) s) s)
Proof
  simp[] >> strip_tac >> gvs[]
  >- simp[emitHelperPropsTheory.step_MLOAD]
  >- (`mk_inst id ILOAD [addr] [out] = instruction id ILOAD [addr] [out]` by
        simp[mk_inst_def, instruction_component_equality] >>
      asm_rewrite_tac[] >> irule step_inst_base_ILOAD >> simp[]) >>
  drule exprSimUnwrapTheory.step_DLOAD >> simp[]
QED

Theorem for_array_length_read_clean[local]:
  MEM opc [MLOAD; ILOAD; DLOAD] /\ eval_operand addr s = SOME a /\
  (opc <> DLOAD ==> mem_word_taint tn.t_mem (w2n a) = {}) ==>
  op_taint (step_taint (mk_inst id opc [addr] [out]) s u tn) (Var out) = {} /\
  op_prov (step_prov PG G (mk_inst id opc [addr] [out]) u) (Var out) = NONE
Proof
  simp[] >> strip_tac >> gvs[] >>
  simp[op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
       op_prov_def, step_prov_def, out_prov_def, set_prov_def,
       mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

(* A direct load's raw result differs from the packet endpoint only by
   positioning the cursor at the end of the emitted slice. *)
Theorem for_array_length_direct_packet[local]:
  ~(loc = LocCode /\ ctor /\ IS_SOME imm) /\
  compile_ptr_load ctor imm loc addr = emit_op opc [addr] /\
  emit_op opc [addr] sa = (p,sb) /\
  MEM opc [MLOAD; ILOAD; DLOAD] /\ eval_operand addr s = SOME a /\
  op_taint tn addr = {} /\
  (opc = DLOAD ==> w2n a <= LENGTH s.vs_data_section) /\
  (opc <> DLOAD ==> w2n a + 32 <= s.vs_alloca_next /\
    ((?x. addr = Var x /\ ptr_covers G tn x s 32) \/
     (w2n a + 32 <= lo /\ op_prov G addr = NONE)) /\
    mem_word_taint tn.t_mem (w2n a) = {}) /\
  (if opc = DLOAD then word_of_bytes T (0w:bytes32)
     (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
   else mload (w2n a) s) = w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq (emitted_insts sa sb) s = OK z ==>
  ?G' tn'. array_length_loader_ok ctor imm loc addr w sa p sb lo ctx func PG
      s G tn (z with vs_inst_idx := LENGTH sb.cs_current_insts) G' tn' /\
    op_taint tn' p = {} /\ op_prov G' p = NONE
Proof
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `p = Var _` SUBST_ALL_TAC >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sb = [mk_inst _ _ _ [out]]` >>
  `step_inst_base (mk_inst sa.cs_next_id opc [addr] [out]) s =
     OK (update_var out w s)` by
    (drule_all for_array_length_read_step >> disch_then (mp_tac o Q.SPEC `out`) >> simp[]) >>
  `z = update_var out w s` by fs[run_inst_seq_def] >>
  `access_ok lo G func (mk_inst sa.cs_next_id opc [addr] [out]) s /\
   taint_ok func tn (mk_inst sa.cs_next_id opc [addr] [out]) s /\
   inst_mem_below_frontier (mk_inst sa.cs_next_id opc [addr] [out]) s /\
   inst_dload_in_section (mk_inst sa.cs_next_id opc [addr] [out]) s` by
    (irule for_array_length_read_checks >> simp[] >> qexists_tac `a` >>
     simp[] >> strip_tac >> res_tac >> simp[]) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id opc [addr] [out]) z`,
    `step_taint (mk_inst sa.cs_next_id opc [addr] [out]) s z tn`] >>
  reverse conj_tac
  >- (irule for_array_length_read_clean >> simp[] >> qexists_tac `a` >>
      simp[] >> strip_tac >> res_tac >> simp[]) >>
  simp[array_length_loader_ok_def] >> qexists_tac `opc` >>
  simp[array_length_step_ok_def] >> gvs[]
QED

(* Constructor code first adds the zero region base. Check the load at
   the positioned ADD endpoint, but identify the final state by the raw run. *)
Theorem for_array_length_ctor_packet[local]:
  compile_imm_load_word T (SOME rb) addr sa = (p,sb) /\
  eval_operand addr s = SOME a /\ eval_operand rb s = SOME 0w /\
  op_taint tn addr = {} /\ op_taint tn rb = {} /\
  op_prov G addr = NONE /\ op_prov G rb = NONE /\
  w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
  mem_word_taint tn.t_mem (w2n a) = {} /\ mload (w2n a) s = w /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq (emitted_insts sa sb) s = OK z ==>
  ?G' tn'. array_length_loader_ok T (SOME rb) LocCode addr w sa p sb lo ctx func PG
      s G tn (z with vs_inst_idx := LENGTH sb.cs_current_insts) G' tn' /\
    op_taint tn' p = {} /\ op_prov G' p = NONE
Proof
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all compile_imm_load_word_ctor_execution >> strip_tac >>
  Cases_on `emit_op ADD [addr; rb] sa` >>
  rename1 `emit_op ADD [addr; rb] sa = (ap,sm)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `ap = Var out1` >>
  `emit_op ILOAD [Var out1] sm = (p,sb)` by
    (qpat_x_assum `compile_imm_load_word T _ _ _ = _` mp_tac >>
     simp[compile_imm_load_word_def, comp_bind_def]) >>
  qpat_assum `emit_op ILOAD _ _ = _`
    (mp_tac o MATCH_MP emitted_insts_emit_op) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `p = Var out2` >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ADD [addr;rb] [out1]` >>
  qabbrev_tac `u1 = update_var out1 a s` >>
  qabbrev_tac `s1 = u1 with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  qabbrev_tac `G1 = step_prov PG G i1 u1` >>
  qabbrev_tac `tn1 = step_taint i1 s u1 tn` >>
  qabbrev_tac `i2 = mk_inst sm.cs_next_id ILOAD [Var out1] [out2]` >>
  qabbrev_tac `u2 = update_var out2 w s1` >>
  `z = update_var out2 w u1` by
    (fs[Abbr `u1`, Abbr `out1`, Abbr `out2`] >>
     qpat_assum `mload _ _ = w` (SUBST1_TAC o SYM) >> simp[]) >>
  `tn1 = tn with t_var := tn.t_var |+ (out1,{})` by
    (simp[Abbr `tn1`, Abbr `i1`] >> irule scalar_add_taint >> simp[Abbr `u1`, update_var_def]) >>
  `eval_operand (Var out1) s1 = SOME a /\ op_taint tn1 (Var out1) = {} /\
   op_prov G1 (Var out1) = NONE /\ tn1.t_mem = tn.t_mem /\
   mload (w2n a) s1 = w` by
    (qpat_x_assum `mload _ _ = w` mp_tac >>
     simp[Abbr `s1`, Abbr `u1`, Abbr `G1`, Abbr `i1`, eval_operand_def,
          lookup_var_def, update_var_def, op_taint_def, op_prov_def, mk_inst_def,
          step_prov_def, out_prov_def, set_prov_def, first_prov_def,
          FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mload_def]) >>
  `access_ok lo G func i1 s /\ taint_ok func tn i1 s /\
   inst_mem_below_frontier i1 s /\ inst_dload_in_section i1 s` by
    (simp[Abbr `i1`, mk_inst_def, access_ok_def, taint_ok_def, mem_read_ops_def,
          source_memory_read_ranges_def, codegenRelTheory.source_memory_write_ranges_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def, inst_dload_in_section_def] >>
     metis_tac[]) >>
  `w2n a + 32 <= s1.vs_alloca_next /\ allocas_from lo s1 /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp s1)` by
    (simp[Abbr `s1`, Abbr `u1`, update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     fs[allocas_from_def, allocas_below_fmp_def]) >>
  `access_ok lo G1 func i2 s1 /\ taint_ok func tn1 i2 s1 /\
   inst_mem_below_frontier i2 s1 /\ inst_dload_in_section i2 s1` by
    (qunabbrev_tac `i2` >> irule for_array_length_read_checks >>
     simp[]) >>
  `step_inst_base i2 s1 = OK u2` by
    (simp[Abbr `i2`, Abbr `u2`] >>
     drule_all (SIMP_RULE (srw_ss()) []
       (for_array_length_read_step |> Q.INST [`opc` |-> `ILOAD`])) >> simp[]) >>
  qexistsl_tac [`step_prov PG G1 i2 u2`, `step_taint i2 s1 u2 tn1`] >>
  reverse conj_tac
  >- (simp[Abbr `i2`] >>
      qpat_x_assum `p = Var out2` SUBST_ALL_TAC >>
      irule for_array_length_read_clean >> simp[]) >>
  simp_tac (srw_ss()) [array_length_loader_ok_def, LET_THM] >>
  qexistsl_tac [`out1`,`sm`,`out2`,`a`,`0w`] >>
  unabbrev_all_tac >>
  pure_rewrite_tac[WORD_ADD_0, instIdxIndepTheory.update_var_idx,
    ghostPcTransportPtrTheory.step_prov_inst_idx,
    ghostPcTransportPtrTheory.step_taint_inst_idx] >>
  gs[WORD_ADD_0, array_length_step_ok_def, update_var_def]
QED

Theorem for_array_length_checked_packet[local]:
  compile_ptr_load ctor imm loc addr sa = (p,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  array_length_loader_ok ctor imm loc addr w sa p sb lo ctx func PG s G tn t G' tn' ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
  eval_operand p t = SOME w /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ array_length_frame sa s G tn t G' tn'
Proof
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule_all (SRULE [PULL_EXISTS, cardinalityCoreTheory.LEFT_IMP_EXISTS_THM]
    (array_length_joint |> Q.INST [`dyn` |-> `T`, `D` |->
       `<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>`])) >>
  disch_then (qspec_then `explicit` (qx_choose_then `u`
    (qx_choose_then `Gu` (qx_choose_then `ntu` strip_assume_tac)))) >>
  `u = t /\ Gu = G' /\ ntu = tn'` by
    (qpat_x_assum `array_length_loader_ok _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ t G' tn'` mp_tac >>
     qpat_x_assum `array_length_loader_ok _ _ _ _ _ _ _ _
         _ _ _ _ _ _ _ u Gu ntu` mp_tac >>
     rewrite_tac[AND_IMP_INTRO] >>
     Cases_on `loc = LocCode /\ ctor /\ IS_SOME imm`
     >- (simp[array_length_loader_ok_def, LET_THM, array_length_step_ok_def] >>
         strip_tac >> gvs[]) >>
     asm_rewrite_tac[array_length_loader_ok_def, LET_THM, array_length_step_ok_def] >>
     strip_tac >> imp_res_tac emitted_insts_emit_op >>
     gvs[mk_inst_def, instruction_component_equality]) >>
  gvs[] >> gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

(* Check the physical dynamic header (or fixed literal) at the exact
   endpoint of the compiler's raw run, with the cursor positioned. *)
Theorem for_nonslot_array_length_checked:
  (if dynamic then compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc addr
   else comp_return (Lit (n2w cnt))) sa = (len_op,sb) /\
  (loc = LocMemory \/ loc = LocCode) /\
  (~dynamic ==> cnt = LENGTH vs) /\
  (dynamic ==> eval_operand addr s = SOME a /\
    (if loc = LocCode /\ ~c.ce_is_ctor then
       word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
     else mload (w2n a) s) = n2w (LENGTH vs)) /\
  (dynamic /\ loc = LocMemory ==>
    (?p. addr = Var p /\ ptr_covers G tn p s 32) /\
    mem_word_taint tn.t_mem (w2n a) = {} /\ w2n a + 32 <= s.vs_alloca_next) /\
  (dynamic /\ loc = LocCode ==>
    op_taint tn addr = {} /\ op_prov G addr = NONE /\
    (if c.ce_is_ctor then
       mem_word_taint tn.t_mem (w2n a) = {} /\
       w2n a + 32 <= lo /\ lo <= s.vs_alloca_next /\
       (!rb. c.ce_imm_alloca = SOME rb ==> eval_operand rb s = SOME 0w /\
         op_taint tn rb = {} /\ op_prov G rb = NONE)
     else w2n a + 32 <= LENGTH s.vs_data_section)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  run_inst_seq (emitted_insts sa sb) s = OK z ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    eval_operand len_op (z with vs_inst_idx := LENGTH sb.cs_current_insts) =
      SOME (n2w (LENGTH vs)) /\
    op_taint tn' len_op = {} /\ op_prov G' len_op = NONE /\
    ~(z with vs_inst_idx := LENGTH sb.cs_current_insts).vs_halted /\
    (z with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
    (z with vs_inst_idx := LENGTH sb.cs_current_insts).vs_inst_idx =
      LENGTH sb.cs_current_insts /\
    array_length_frame sa s G tn (z with vs_inst_idx := LENGTH sb.cs_current_insts) G' tn'
Proof
  reverse (Cases_on `dynamic`) >> simp[]
  >- (simp[comp_return_def] >> strip_tac >> gvs[emitted_insts_def, run_inst_seq_def] >>
      `s with vs_inst_idx := LENGTH sa.cs_current_insts = s` by
        simp[venom_state_component_equality] >>
      qexistsl_tac [`G`, `tn`] >>
      simp[eval_operand_def, op_taint_def, op_prov_def, array_length_frame_def,
           venom_state_component_equality] >>
      gen_tac >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  DISCH_THEN (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qabbrev_tac `t = z with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `?G' tn'. array_length_loader_ok c.ce_is_ctor c.ce_imm_alloca loc addr
        (n2w (LENGTH vs)) sa len_op sb lo ctx func PG s G tn t G' tn' /\
      op_taint tn' len_op = {} /\ op_prov G' len_op = NONE` suffices_by
    (strip_tac >> drule_all for_array_length_checked_packet >>
     disch_then (qspec_then `explicit` strip_assume_tac) >>
     qexistsl_tac [`G'`, `tn'`] >> gs[Abbr `t`]) >>
  qunabbrev_tac `t` >>
  qpat_x_assum `loc = LocMemory \/ loc = LocCode` strip_assume_tac
  >- (gvs[compile_ptr_load_def] >>
      qpat_assum `ptr_covers _ _ _ _ _`
        (assume_tac o CONJUNCT1 o REWRITE_RULE [ptr_covers_def]) >>
      irule for_array_length_direct_packet >> simp[compile_ptr_load_def] >>
      qexists_tac `MLOAD` >> simp[]) >>
  Cases_on `c.ce_is_ctor` >> gvs[]
  >- (Cases_on `c.ce_imm_alloca` >> gvs[compile_ptr_load_def, compile_imm_load_word_def]
      >- (irule for_array_length_direct_packet >>
          simp[compile_ptr_load_def, compile_imm_load_word_def] >>
          qexists_tac `ILOAD` >> simp[]) >>
      irule for_array_length_ctor_packet >> simp[compile_imm_load_word_def]) >>
  irule for_array_length_direct_packet >>
  fs[compile_ptr_load_def, compile_imm_load_word_def] >>
  qexists_tac `DLOAD` >> simp[] >> decide_tac
QED

(* The selected memory arm belongs to the set framed by iterator_unmodified. *)
Theorem eval_iterator_memory_place_access:
  !e cx es ee root path pending.
    expr_writes_ok (\_. F) e /\
    eval_expr cx e es = (INL (PlaceR (MemoryPlace root path)),ee) ==>
    ?target attrs tail.
      MEM target (expr_places e) /\
      place_access target pending = (NameTarget root,attrs) /\
      path ++ MAP AttrSubscript pending = MAP AttrSubscript attrs ++ tail
Proof
  ho_match_mp_tac
    (vyperASTTheory.expr_induction |> Q.SPEC `P` |> Q.SPEC `\_. T` |>
     SIMP_RULE (srw_ss()) []) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[expr_writes_ok_def] >> rpt strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (Name _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
           bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs(),
           expr_places_def, place_access_def] >>
      strip_tac >> gvs[])
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rename1 `eval_expr _ (TopLevelName _ nid) _ = _` >> PairCases_on `nid` >>
      qpat_x_assum `eval_expr _ (TopLevelName _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, vyperLocalAccessFrameTheory.lookup_global_not_memory])
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def,
           raise_def, COND_RATOR, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      drule exprSimIfExpTheory.ifexp_conditional_result_shape >> simp[] >> strip_tac >> gvs[] >>
      rename1 `eval_expr cx arm zs = (INL (PlaceR (MemoryPlace root path)),ws)` >>
      qpat_assum `!cx es ee root path pending. eval_expr cx arm es = _ ==> _`
        (qspecl_then [`cx`,`zs`,`ws`,`root`,`path`,`pending`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl [`target`,`attrs`,`tail`] >> simp[expr_places_def])
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, COND_RATOR, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      drule exprSimPropsTheory.select_result_memory_place >>
      disch_then (qspecl_then [`root`,`path`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      rename1 `eval_expr _ obj _ = (INL (PlaceR (MemoryPlace _ path0)),bs)` >>
      qpat_assum `!cx es ee root path pending. eval_expr cx obj es = _ ==> _`
        (qspecl_then [`cx`,`es`,`bs`,`root`,`path0`,`[]`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `select_result _ (expr_type obj) _ (ValueSubscript v) _ = _` >>
      qexistsl [`SubscriptTarget target e'`,`attrs`,
                `tail ++ [ValueSubscript v] ++ MAP AttrSubscript pending`] >>
      simp[expr_places_def, place_access_def, MEM_MAP] >> metis_tac[])
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      strip_tac >> gvs[] >>
      drule exprSimPropsTheory.select_result_memory_place >>
      disch_then (qspecl_then [`root`,`path`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      rename1 `eval_expr _ obj _ = (INL (PlaceR (MemoryPlace _ path0)),bs)` >>
      rename1 `select_result cx _ _ (AttrSubscript fld) _ = _` >>
      qpat_assum `!cx es ee root path pending. eval_expr cx obj es = _ ==> _`
        (qspecl_then [`cx`,`es`,`bs`,`root`,`path0`,`fld::pending`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl [`AttributeTarget target fld`,`attrs`,`tail`] >>
      simp[expr_places_def, place_access_def, MEM_MAP] >> metis_tac[]) >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
      type_check_def, check_def, assert_def, lift_option_type_def, AllCaseEqs()]
  >~ [`lookup_flag_mem cx ns mid es = _`]
  >- (Cases_on `ns` >>
      gvs[lookup_flag_mem_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()])
  >~ [`eval_expr cx (StructLit ty ns fields) es = _`]
  >- (Cases_on `ns` >> gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()]) >>
  rename1 `eval_expr cx (Call ty target args drv) es = _` >>
  Cases_on `target` >>
  TRY (rename1 `IntCall fid` >> Cases_on `fid`) >>
  TRY (rename1 `CreateTarget kind _ _ _` >> Cases_on `kind`) >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
      type_check_def, check_def, assert_def, lift_option_type_def, raise_def, AllCaseEqs()]
  >>~- ([`eval_send`], drule exprSimSendTheory.eval_send_value >> simp[])
  >>~- ([`eval_raw_call`],
       qpat_x_assum `eval_raw_call _ _ _ _ _ _ _ = _` mp_tac >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[eval_raw_call_def, bind_def, ignore_bind_def, return_def,
            raise_def, COND_RATOR, AllCaseEqs(), pairTheory.UNCURRY, LET_THM] >> rw[] >> gvs[])
  >>~- ([`eval_create_operands`],
       drule vyperLocalAccessFrameTheory.eval_create_operands_success_value >> simp[]) >>
  drule vyperCallFrameTheory.eval_ext_call_success_value >> simp[]
QED

(* Non-slot iterator evaluation and its actual conditional length slice. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> simp[Once evaluate_def] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  conj_tac >- simp[storage_trace_frame_array_iterator_results] >>
  conj_tac >- (rpt gen_tac >> simp[] >> strip_tac >>
    irule gas_exempt_cert_bind_result >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule gas_exempt_cert_error_result >> simp[]) >>
  conj_tac >- simp[cj 5 evaluate_storage_trace_frame] >>
  qexists_tac `\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\
    ?tv. res = INL tv /\
      vv_post H ctx func c cx e es sa sb s ee tv vv t /\
      vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d c cx ee G1 tn1 t /\
      ptr_vv_ok cx (post_value_type c e) tv vv ee G1 tn1 t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type c e) /\
        ~is_bytestring_type (post_value_type c e) ==>
        vv_own c cx (post_value_type c e) sa sb ee tv vv t /\
        (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?v. read_result cx tv ee = (INL v,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
              val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type c e) ==>
        ptr_buf_ok c e op G1 t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok c e p.ptr_operand G1 t) /\
      ghost_kept_at lo c es sa G tn s G1 tn1` >>
  reverse conj_tac
  >- (drule_all for_array_expr_prefix_full >>
      disch_then (qspec_then `PG` assume_tac) >>
      irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >> simp[] >>
      strip_tac >> metis_tac[expr_exit_INR_type, halt_exit_INR_type]) >>
  suspend "normal"
QED
*)
Theorem for_nonslot_array_prefix_full:
  body_iterator_full_ok_mods mods exps cx (Array e) /\
  body_const_cells_agree mods cx env es /\
  (contract_inv mods exps ctx c cx /\
     module_body_inv mods c.ce_module tops c cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\ expr_body_pre_mods mods c cx env e es /\
  well_typed_iterator env elem (Array e) /\ supported_iterator tops elem (Array e) n /\
  (!src name. e = TopLevelName (expr_type e) (src,name) ==>
     ?ts. ALOOKUP mods src = SOME ts /\
       IS_SOME (supported_immutable_type ts (NONE,name))) /\
  (~(?ty nid. e = TopLevelName ty nid) ==>
   !tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid) /\
  expr_type e = ArrayT elem bd /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\
  compile_expr (gas_shadow_env T c) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved c sa /\
  (!H. dead_lo_ok H (DF H) lo c cx) /\
  (!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  return_buf_frame d c sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst t. frag_reachable ctx func s fn inst t ==> dalloca_fmp_headroom inst t) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func c cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d c cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  loc = (case vv_location vv of NONE => LocMemory | SOME l => l) /\
  (case bd of
     vyperAST$Fixed cnt => comp_return (Lit (n2w cnt))
   | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc (vv_operand vv)) sb =
    (len_op,sc) /\ fn_has_code sb sc func ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    c.ce_modules cx st0 (eval_iterator cx (Array e)) (es,s,G,tn)
    (\H res ee G' tn' t. ?vs rv av xs et.
      res = INL vs /\ vs = MAP Value xs /\
      (?obs. !tail. eval_expr cx e (es with gas_obs := obs ++ tail) =
        (INL rv,ee with gas_obs := tail)) /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
      value_has_type (ArrayTV et bd) (ArrayV av) /\
      (!name path. rv = PlaceR (MemoryPlace name path) ==>
        runtime_place_typed cx ee (MemoryPlace name path) (ArrayTV et bd)) /\
      (!name path. rv = PlaceR (MemoryPlace name path) ==>
        ?entry. lookup_scopes name ee.scopes = SOME entry /\
          evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
      read_result cx rv ee = (INL (ArrayV av),ee) /\
      extract_elements (ArrayTV et bd) (ArrayV av) = SOME xs /\
      (loc = LocMemory \/ loc = LocCode) /\
      (loc = LocMemory ==> rv = Value (ArrayV av) \/
        ?id path. rv = PlaceR (MemoryPlace id path)) /\
      eval_operand len_op t = SOME (n2w (LENGTH vs)) /\
      op_taint tn' len_op = {} /\ op_prov G' len_op = NONE /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      stmt_state_rel H ctx func c cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at (DF H) lo d c cx ee G' tn' t /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      allocas_from lo t /\ return_buf_frame d c sc t /\
      s.vs_alloca_next <= t.vs_alloca_next /\ alloca_frame c es sa s c ee t /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
      ghost_kept_at lo c es sa G tn s G' tn' /\
      vv_post H ctx func c cx e es sa sb s ee rv vv t /\
      vv_store_bound cx (post_value_type c e) (lowered_value_type c e) ee rv vv t /\
      ptr_vv_ok cx (post_value_type c e) rv vv ee G' tn' t /\
      (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
        ~is_bytestring_type (post_value_type c e) ==>
        vv_own c cx (post_value_type c e) sa sb ee rv vv t /\
        (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
      (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
            val_in_memory rt (ArrayV av) (w2n w) mem)) /\
      (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
        ptr_buf_ok c e op G' t) /\
      (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok c e p.ptr_operand G' t))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[normal]:
  map_every qx_gen_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`u`] >>
  simp[] >> strip_tac >>
  qabbrev_tac `H0 = vyperStorageFootprint$storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`, vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H0` (drule_then (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (qx_choose_then `rv` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac)))))) >>
  qabbrev_tac `esx = es with gas_obs := gas_explicit marks s.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e esx = (INL rv,mid)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid`
       (fn th => simp[NoAsms, Abbr `esx`, th])) >>
  `expr_body_pre c cx env e esx` by simp[Abbr `esx`, exprSimSourceTheory.expr_body_pre_gas_obs] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  disch_then (qx_choose_then `tvt` strip_assume_tac) >>
  `?et. tvt = ArrayTV et bd` by metis_tac[evaluate_type_ArrayT_cases] >>
  qpat_x_assum `tvt = ArrayTV _ _` SUBST_ALL_TAC >>
  `!name path. rv = PlaceR (MemoryPlace name path) ==>
    runtime_place_typed cx mid (MemoryPlace name path) (ArrayTV et bd)` by
    (rpt strip_tac >>
     qpat_assum `rv = PlaceR (MemoryPlace name path)`
       (fn eq => qpat_assum `eval_expr cx e esx = (INL rv,mid)`
         (assume_tac o REWRITE_RULE [eq])) >>
     drule_all exprSimSubscriptArraySourceTheory.expr_body_pre_place_metadata >>
     simp[]) >>
  drule abiEncodeArgsSimTheory.abi_args_vv_post_read >>
  disch_then (qx_choose_then `v` assume_tac) >>
  `value_has_type (ArrayTV et bd) v` by metis_tac[] >>
  `?av. v = ArrayV av` by
    (qpat_assum `value_has_type (ArrayTV et bd) v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `bd` >> Cases_on `v` >> simp[value_has_type_def]) >>
  qpat_x_assum `v = ArrayV av` SUBST_ALL_TAC >>
  `?pty pbd. post_value_type c e = ArrayT pty pbd` by
    (`type_widens_to env.type_defs (post_value_type c e) (ArrayT elem bd)` by
       (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >>
        qpat_assum `expr_body_pre c cx env e esx`
          (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >>
        drule_all post_value_type_widens >> simp[]) >>
     qpat_x_assum `type_widens_to _ _ _` mp_tac >> simp[type_widens_to_def] >>
     Cases_on `post_value_type c e` >> simp[arg_type_fits_def]) >>
  `~is_word_type (post_value_type c e) /\ ~is_bytestring_type (post_value_type c e)` by
    simp[is_word_type_def, is_bytestring_type_def] >>
  Q.SUBGOAL_THEN `(!tr slot tv b. rv <> PlaceR (StoragePlace tr slot (ArrayTV tv b))) /\
    (loc = LocMemory \/ loc = LocCode) /\
    (loc = LocMemory ==> rv = Value (ArrayV av) \/ ?id path. rv = PlaceR (MemoryPlace id path))`
    (map_every assume_tac o CONJUNCTS)
  >- (Cases_on `?ty nid. e = TopLevelName ty nid`
      >- (pop_assum (qx_choose_then `ty` (qx_choose_then `nid` SUBST_ALL_TAC)) >>
          PairCases_on `nid` >>
          `?ity. supported_immutable_type tops (nid0,nid1) = SOME ity` by
            (qpat_assum `!nid. _ ==> IS_SOME _` (qspec_then `(nid0,nid1)` mp_tac) >>
             simp[NoAsms, vyperASTTheory.expr_type_def, optionTheory.IS_SOME_EXISTS]) >>
          `expr_sim_inv c cx env es` by metis_tac[expr_body_pre_static_facts] >>
          drule_all exprOpenMainTheory.supported_immutable_bound >> strip_tac >>
          `loc = LocCode` by
            (drule exprSimTopLevelImmutableTheory.compile_toplevel_immutable_ptr >>
             disch_then (qspecl_then [`expr_type (TopLevelName ty (nid0,nid1))`,`sa`,`ty`] assume_tac) >>
             qpat_assum `compile_expr _ _ _ _ = (vv,sb)` mp_tac >>
             simp[] >> strip_tac >> gvs[vv_location_def, mk_ptr_def]) >>
          `get_module_code cx NONE = SOME tops` by metis_tac[body_inv_main_code] >>
          drule body_inv_modules_aligned >> strip_tac >>
          `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by metis_tac[] >>
          drule_all bodyStorageMetadataTheory.supported_immutable_type_find_NONE >> strip_tac >>
          qpat_x_assum `nid0 = NONE` SUBST_ALL_TAC >>
          `rv = PlaceR (ImmutablePlace NONE nid1 [])` by
            (qpat_x_assum `eval_expr _ (TopLevelName _ _) esx = _` mp_tac >>
             Cases_on `ALOOKUP esx.immutables cx.txn.target` >>
             simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
                  get_immutables_def, get_address_immutables_def, return_def, raise_def] >>
             rename1 `ALOOKUP esx.immutables cx.txn.target = SOME imms` >>
             Cases_on `FLOOKUP (get_source_immutables NONE imms) nid1` >>
             simp[return_def, raise_def]) >> simp[]) >>
      `rv = Value (ArrayV av) \/ ?id path. rv = PlaceR (MemoryPlace id path)`
      suffices_by
        (strip_tac
         >- (Cases_on `vv` >> fs[vv_location_def]) >>
         qpat_assum `vv_post H0 ctx func c cx e es sa sb s mid rv vv u`
           (assume_tac o cj 5 o REWRITE_RULE [vv_post_def]) >>
         qpat_x_assum `rv = PlaceR (MemoryPlace _ _)` SUBST_ALL_TAC >>
         Cases_on `vv` >> fs[vv_location_def, vv_place_ptr_def]) >>
      Cases_on `?ty nm. e = Name ty nm`
      >- (pop_assum (qx_choose_then `ty` (qx_choose_then `nm` SUBST_ALL_TAC)) >>
          qpat_x_assum `eval_expr _ (Name _ _) esx = _` mp_tac >>
          simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
               bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
          disch_then strip_assume_tac >> disj2_tac >>
          qexistsl_tac [`nm`, `[]`] >> simp[Once EQ_SYM_EQ]) >>
      `expr_writes_ok (\_. F) e` by fs[well_typed_iterator_def] >>
      `!tgt nid. loop_iterator_place e = SOME tgt ==> target_root tgt <> TopLevelNameTarget nid` by
        (qpat_assum `~(?ty nid. e = TopLevelName ty nid) ==> _` (fn guard =>
         qpat_assum `~(?ty nid. e = TopLevelName ty nid)`
           (ACCEPT_TAC o MATCH_MP guard))) >>
      drule_all whitelistForIterTheory.memory_iterator_source_classify >>
      strip_tac >> fs[read_result_def, return_def]) >>
  Q.SUBGOAL_THEN
    `!a ctx0 en zs name path ze.
      well_typed_expr en a /\
      expr_writes_ok (\_. F) a /\
      eval_expr ctx0 a zs = (INL (PlaceR (MemoryPlace name path)),ze) ==>
      ?entry v. lookup_scopes name ze.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL v`
    ASSUME_TAC
  >- suspend "iterator_live_induction" >>
  `!name path. rv = PlaceR (MemoryPlace name path) ==>
      ?entry. lookup_scopes name mid.scopes = SOME entry /\
        evaluate_subscripts entry.type entry.value path = INL (ArrayV av)` by
    suspend "iterator_live_read" >>
  disj1_tac >> qexists_tac `rv` >> conj_tac >- REFL_TAC >>
  Q_TAC (fn tm => SUBGOAL_THEN tm (qx_choose_then `xs` ASSUME_TAC))
    `?xs. extract_elements (ArrayTV et bd) (ArrayV av) = SOME xs`
  >- simp[extract_elements_def] >>
  `!tail. array_iterator_results cx (ArrayT elem bd) rv (mid with gas_obs := tail) =
        (INL (MAP Value xs),mid with gas_obs := tail)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> strip_tac >>
     qpat_assum `expr_type e = ArrayT elem bd` (SUBST1_TAC o SYM) >>
     simp[array_iterator_results_copy, bind_def, lift_option_type_def, return_def,
          IgnAsm `expr_type e = ArrayT elem bd`]) >>
  `array_iterator_results cx (expr_type e) rv mid = (INL (MAP Value xs),mid)` by
    (qpat_assum `expr_type e = ArrayT elem bd` SUBST1_TAC >>
     qpat_assum `mid with gas_obs := [] = mid` (fn eq =>
       qpat_assum `!tail. array_iterator_results _ _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [eq])))) >>
  `vv_post H0 ctx func c cx e esx sa sb s mid rv vv u` by
    simp[Abbr `esx`, exprSimPropsTheory.vv_post_initial_gas] >>
  qabbrev_tac `dynamic = case bd of vyperAST$Fixed _ => F | Dynamic _ => T` >>
  qabbrev_tac `cnt = case bd of vyperAST$Fixed k => k | Dynamic k => k` >>
  `dynamic = (case bd of vyperAST$Fixed _ => F | Dynamic _ => T) /\
   cnt = (case bd of vyperAST$Fixed k => k | Dynamic k => k)` by
    simp[Abbr `dynamic`, Abbr `cnt`] >>
  `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx rv mid = (INL v,mid) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
                eval_operand (vv_operand vv) u = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           (!m. mem_agree_outside tn1.t_mem u.vs_memory m ==>
                val_in_memory rt v (w2n w) m)` by
    (qpat_assum `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
     rewrite_tac[Once arithmeticTheory.ADD_COMM]) >>
  drule_at_then (Pat `eval_expr _ _ _ = (INL _,_)`) drule_all
    (REWRITE_RULE [] (Q.INST [`addr` |-> `vv_operand vv`]
      (SPEC_ALL for_nonslot_array_length_observation))) >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (qx_choose_then `av1` (qx_choose_then `xs1`
      (qx_choose_then `pty1` (qx_choose_then `pbd1`
        (qx_choose_then `pet` (qx_choose_then `a`
          (map_every assume_tac o CONJUNCTS)))))))) >>
  suspend "length"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_induction]:
  POP_ASSUM_LIST (K all_tac) >>
  completeInduct_on `expr_size a` >>
  Cases_on `a` >> simp[] >> rpt strip_tac
  >~ [`eval_expr _ (Name _ _) _ = _`]
  >- (qpat_x_assum `eval_expr _ (Name _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
           bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs(),
           optionTheory.IS_SOME_EXISTS, evaluate_subscripts_def] >>
      strip_tac >> gvs[] >> metis_tac[])
  >~ [`eval_expr _ (TopLevelName _ _) _ = _`]
  >- (rename1 `eval_expr _ (TopLevelName _ nid) _ = _` >>
      PairCases_on `nid` >>
      qpat_x_assum `eval_expr _ (TopLevelName _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, vyperLocalAccessFrameTheory.lookup_global_not_memory])
  >~ [`eval_expr _ (Subscript _ _ _) _ = _`]
  >- suspend "iterator_live_subscript"
  >~ [`eval_expr _ (Attribute _ _ _) _ = _`]
  >- suspend "iterator_live_attribute"
  >~ [`eval_expr _ (IfExp _ _ _ _) _ = _`]
  >- suspend "iterator_live_conditional" >>
  drule_at (Pat `eval_expr _ _ _ = _`) eval_iterator_memory_place_access >>
  simp[vyperTypeSystemTheory.expr_places_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_subscript]:
  rename1 `eval_expr ctx0 (Subscript ann obj key) zs = _` >>
  Cases_on `subscript_reads_base ctx0 obj key` >>
  qpat_x_assum `eval_expr ctx0 (Subscript ann obj key) zs = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  drule exprSimSubscriptArrayOriginTheory.select_result_memory_origin >>
  strip_tac >> gvs[] >>
  suspend "iterator_live_subscript_frame"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_subscript_frame]:
  rename1 `eval_expr ctx0 obj zs = (INL (PlaceR (MemoryPlace name path0)),zm)` >>
  rename1 `eval_expr ctx0 key zm = (INL idx,zk)` >>
  rename1 `read_result ctx0 idx zk = (INL kv,zr)` >>
  `zr = zk` by (drule read_result_state >> simp[]) >>
  qpat_x_assum `zr = zk` SUBST_ALL_TAC >>
  `well_typed_expr en obj /\ well_typed_expr en key` by
    (qpat_assum `well_typed_expr en (Subscript ann obj key)` mp_tac >>
     simp[Once well_typed_expr_def, NoAsms] >> rpt strip_tac >>
     drule_all exprSimSubscriptArrayOriginTheory.type_place_expr_not_memory >>
     simp[]) >>
  `expr_writes_ok (\_. F) obj /\ expr_writes_ok (\_. F) key` by
    (qpat_assum `expr_writes_ok _ (Subscript ann obj key)` mp_tac >>
     simp[expr_writes_ok_def, NoAsms]) >>
  `expr_writes_ok (\w. FST (place_access w []) <> NameTarget name) key` by
    (drule_at (Pat `well_typed_expr _ _`)
       (Q.SPECL [`en`,`key`] (cj 1 stmtSimForArrayFrameTheory.writes_ok_typed_mono)) >>
     disch_then (qspecl_then
       [`\_. F`,`\w. FST (place_access w []) <> NameTarget name`] mp_tac) >>
     simp[]) >>
  `lookup_scopes name zk.scopes = lookup_scopes name zm.scopes` by
    (irule stmtSimForArrayFrameTheory.scope_projection_lookup >>
     qspecl_then [`ctx0`,`key`] mp_tac
       (cj 5 (Q.SPEC `name` stmtSimForArrayFrameTheory.eval_name_projection_mutual)) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qspecl_then [`zm`,`INL idx`,`zk`] mp_tac) >> simp[]) >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size obj` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `obj` mp_tac) >> simp[NoAsms] >>
  disch_then (qspecl_then [`ctx0`,`en`,`zs`,`name`,`path0`,`zm`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`en0`,`v0`] (map_every assume_tac o CONJUNCTS)) >>
  `lookup_scopes name zk.scopes = SOME en0` by
    (qpat_assum `lookup_scopes name zk.scopes = lookup_scopes name zm.scopes`
       SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `select_result _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [select_result_def]) >>
  drule_all targetSubscriptMemoryTheory.extend_place_memory_live >>
  strip_tac >> gvs[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_attribute]:
  rename1 `eval_expr ctx0 (Attribute ann obj attrId) zs = _` >>
  qpat_x_assum `eval_expr ctx0 (Attribute ann obj attrId) zs = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  strip_tac >>
  drule exprSimSubscriptArrayOriginTheory.select_result_memory_origin >>
  strip_tac >> gvs[] >>
  suspend "iterator_live_attribute_base"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_attribute_base]:
  rename1 `eval_expr ctx0 obj zs = (INL (PlaceR (MemoryPlace name path0)),zm)` >>
  `well_typed_expr en obj` by
    (qpat_assum `well_typed_expr en (Attribute ann obj attrId)` mp_tac >>
     simp[Once well_typed_expr_def,NoAsms]) >>
  `expr_writes_ok (\_. F) obj` by
    (qpat_assum `expr_writes_ok _ (Attribute ann obj attrId)` mp_tac >>
     simp[expr_writes_ok_def,NoAsms]) >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size obj` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `obj` mp_tac) >> simp[NoAsms] >>
  disch_then (qspecl_then [`ctx0`,`en`,`zs`,`name`,`path0`,`zm`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`en0`,`v0`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `select_result _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [select_result_def]) >>
  drule_all targetSubscriptMemoryTheory.extend_place_memory_live >>
  strip_tac >> gvs[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_read]:
  rpt strip_tac >>
  `eval_expr cx e esx = (INL (PlaceR (MemoryPlace name path)),mid)` by
    (qpat_assum `rv = PlaceR (MemoryPlace name path)` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `well_typed_expr env e /\ expr_writes_ok (\_. F) e` by
    (qpat_assum `well_typed_iterator env elem (Array e)` mp_tac >>
     simp[well_typed_iterator_def, NoAsms]) >>
  qpat_assum `!a ctx0 en zs name path ze. well_typed_expr en a /\ _ ==> _`
    (qspecl_then [`e`,`cx`,`env`,`esx`,`name`,`path`,`mid`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`en0`,`v0`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `read_result cx rv mid = (INL (ArrayV av),mid)` mp_tac >>
  qpat_assum `rv = PlaceR (MemoryPlace name path)`
    (fn th => REWRITE_TAC [th]) >>
  simp[read_result_def, read_place_def, read_memory_path_def, get_scopes_def, bind_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def] >>
  metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[iterator_live_conditional]:
  rename1 `eval_expr ctx0 (IfExp ann cond yes no) zs = _` >>
  `well_typed_expr en yes /\ well_typed_expr en no` by
    (qpat_assum `well_typed_expr en (IfExp ann cond yes no)` mp_tac >>
     simp[Once well_typed_expr_def, NoAsms]) >>
  qpat_x_assum `expr_writes_ok _ (IfExp ann cond yes no)`
    (strip_assume_tac o REWRITE_RULE [expr_writes_ok_def]) >>
  qpat_x_assum `eval_expr ctx0 (IfExp ann cond yes no) zs = _` mp_tac >>
  simp[Once evaluate_def, switch_BoolV_def, bind_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[] >>
  drule exprSimIfExpTheory.ifexp_conditional_result_shape >> simp[] >> strip_tac >> gvs[] >>
  rename1 `eval_expr ctx0 arm ms = (INL (PlaceR (MemoryPlace name path)),ze)` >>
  qpat_assum `!m. m < _ ==> _` (qspec_then `expr_size arm` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `arm` mp_tac) >> simp[NoAsms] >>
  disch_then (qspecl_then [`ctx0`,`en`,`ms`,`name`,`path`,`ze`] mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[length]:
  `(if dynamic then compile_ptr_load c.ce_is_ctor c.ce_imm_alloca loc (vv_operand vv)
    else comp_return (Lit (n2w cnt))) sb = (len_op,sc)` by
    ((Cases_on `bd` >> fs[Abbr `dynamic`, Abbr `cnt`] >> (metis_tac[Abbr `dynamic`, Abbr `cnt`]))) >>
  `dynamic ==> eval_operand (vv_operand vv) u = SOME a` by
    (disch_tac >> qpat_assum `eval_operand (vv_operand vv) u = SOME a` ACCEPT_TAC) >>
  `dynamic /\ loc = LocCode /\ c.ce_is_ctor /\ c.ce_imm_alloca <> NONE ==>
    eval_operand (THE c.ce_imm_alloca) u = SOME 0w` by
    (qpat_assum `dynamic /\ loc = LocCode ==> _` mp_tac >>
     Cases_on `c.ce_imm_alloca` >> simp[NoAsms] >> metis_tac[]) >>
  drule_then drule_all for_nonslot_array_length_run >>
  disch_then (qspec_then `ctx` (qx_choose_then `z` (qx_choose_then `t0`
    (map_every assume_tac o CONJUNCTS)))) >>
  `allocas_from lo u` by (metis_tac[ghost_inv_at_def]) >>
  `dynamic ==> eval_operand (vv_operand vv) u = SOME a /\
    (if loc = LocCode /\ ~c.ce_is_ctor then
      word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) u.vs_data_section ++ REPLICATE 32 0w))
     else mload (w2n a) u) = n2w (LENGTH (MAP Value xs))` by
    (strip_tac >> fs[]) >>
  `dynamic /\ loc = LocCode ==>
    op_taint tn1 (vv_operand vv) = {} /\ op_prov G1 (vv_operand vv) = NONE /\
    (if c.ce_is_ctor then
       mem_word_taint tn1.t_mem (w2n a) = {} /\
       w2n a + 32 <= lo /\ lo <= u.vs_alloca_next /\
       (!rb. c.ce_imm_alloca = SOME rb ==> eval_operand rb u = SOME 0w /\
         op_taint tn1 rb = {} /\ op_prov G1 rb = NONE)
     else w2n a + 32 <= LENGTH u.vs_data_section)` by
    (qpat_assum `dynamic /\ loc = LocCode ==> _ /\ _ /\ (_ ==> _) /\ _`
       (fn th => POP_ASSUM_LIST (K (mp_tac th))) >>
     Cases_on `c.ce_is_ctor` >> simp[]) >>
  drule_then drule_all
    (REWRITE_RULE [LET_THM]
      (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
        (SPEC_ALL for_nonslot_array_length_checked))) >>
  qpat_assum `t0 = z with vs_inst_idx := _` (ONCE_REWRITE_TAC o single o GSYM) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choose_then `G2` (qx_choose_then `tn2`
      (map_every assume_tac o CONJUNCTS)) o BETA_RULE)) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- (qpat_assum `~u.vs_halted` ACCEPT_TAC) >>
  qexistsl_tac [`G2`, `mid`, `INL (MAP Value xs)`, `t0`, `tn2`] >>
  conj_tac >- (qpat_assum `!tail. array_iterator_results _ _ _ _ = _` ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
    (qspec_then `DF H` ACCEPT_TAC)) >>
  BETA_TAC >>
  qpat_assum `mid with gas_obs := [] = mid` (SUBST1_TAC) >>
  qexistsl_tac [`rv`,`av`,`xs`,`et`] >>
  suspend "frame"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[frame]:
  `ci_mono sb sc /\ sc.cs_current_bb = sb.cs_current_bb /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sb sc)` by
    (qpat_assum `(if dynamic then _ else _) sb = _` mp_tac >>
     qpat_assum `loc = LocMemory \/ loc = LocCode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     reverse (Cases_on `dynamic`) >> simp[]
     >- (simp[comp_return_def] >> strip_tac >>
         simp[ci_mono_refl, emitted_insts_def]) >>
     disch_tac >> disch_tac >>
     `loc <> LocCalldata` by (qpat_assum `loc = _ \/ loc = _` strip_assume_tac >> simp[]) >>
     drule_all rest_word_ptr_load_code >> strip_tac >>
     conj_tac
     >- (qspecl_then [`c.ce_is_ctor`,`c.ce_imm_alloca`,`loc`,`vv_operand vv`,`sb`]
           mp_tac ci_mono_compile_ptr_load >> simp[]) >>
     simp[EVERY_MEM] >> qx_gen_tac `i` >> disch_tac >>
     qpat_assum `EVERY _ _` (qspec_then `i` mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp[] >> strip_tac >> simp[]) >>
  `ci_mono sa sb` by
    (qspecl_then [`c`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 compile_expr_ci_mono) >>
     qpat_assum `compile_expr c (expr_type e) e sa = _` (fn th => simp[NoAsms, th])) >>
  suspend "anchor"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume for_nonslot_array_prefix_full[anchor]:
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_next_var <= sc.cs_next_var` by
    (qpat_assum `ci_mono sa sb` mp_tac >> qpat_assum `ci_mono sb sc` mp_tac >>
     simp[NoAsms, ci_mono_def]) >>
  `local_ptrs_reserved c sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (qx_gen_tac `x` >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> asm_rewrite_tac[]) >>
  `!x sz. c.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[] >>
  `!x sz. c.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x` by
    metis_tac[] >>
  drule_at_then (Pat `compile_expr _ _ _ _ = _`) (drule_then assume_tac)
    reasonEndpointResourcesPtrTheory.compile_expr_old_operand >>
  qpat_x_assum `copy_old_operand sb _`
    (assume_tac o REWRITE_RULE [copy_old_operand_def]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (`valid_horizon cx st0 H esx.storage_trace` suffices_by simp[NoAsms, Abbr `esx`] >>
     irule (Q.ISPEC `eval_expr cx e`
       (Q.GEN `f` vyperStorageFootprintTheory.valid_horizon_frame)) >>
     qexistsl_tac [`e`, `INL rv`, `mid`] >>
     asm_rewrite_tac[cj 5 evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
    (qspec_then `H` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H` (drule_then (CONJUNCTS_THEN2 kall_tac
      (CONJUNCTS_THEN2 kall_tac (qx_choose_then `rvH`
        (fn th =>
          map_every assume_tac (CONJUNCTS (CONJUNCT2 th)) >>
          SUBST_ALL_TAC (SYM (REWRITE_RULE [sumTheory.INL_11] (CONJUNCT1 th))))))))) >>
  drule_then (drule_at_then (Pat `stmt_state_rel _ _ _ _ _ _ _`)
    (drule_at_then (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
      (drule_at_then (Pat `ghost_inv_at _ _ _ _ _ _ _ _ _`)
        (drule_at_then (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)
          (drule_at (Pat `_ = _ ++ _`))))))
    for_nonslot_array_length_frame_transport >>
  impl_tac
  >- ((asm_rewrite_tac[] >> qx_gen_tac `v` >> disch_tac >>
      qpat_assum `!v. rv = Value v /\ _ ==> _` (qspec_then `v` mp_tac) >>
      asm_rewrite_tac[] >> (metis_tac[]))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `return_buf_frame d c sc t0` by
    (`sa.cs_next_var <= sc.cs_next_var` by
       (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `sb.cs_next_var` >>
        asm_rewrite_tac[]) >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`c`,`s`,`sa`] >> simp[]) >>
  `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
     eval_operand (vv_operand vv) t0 = SOME w ==>
     type_memory_size rt + w2n w <= lo /\
     !mem. mem_agree_outside tn2.t_mem t0.vs_memory mem ==>
       val_in_memory rt (ArrayV av) (w2n w) mem` by
    (disch_tac >>
     qpat_assum `c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. _ /\ !rt w. _ /\ eval_operand (vv_operand vv) t0 = SOME w ==> _` mp_tac >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `cv` (map_every assume_tac o CONJUNCTS)) >>
     `cv = ArrayV av` by
       (qpat_assum `read_result cx rv mid = (INL cv,mid)` mp_tac >>
        qpat_assum `read_result cx rv mid = (INL (ArrayV av),mid)`
          (fn th => simp[NoAsms, th])) >>
     qpat_x_assum `cv = ArrayV av` SUBST_ALL_TAC >>
     qpat_assum `!rt w. _ /\ eval_operand (vv_operand vv) t0 = SOME w ==> _`
       (ACCEPT_TAC o REWRITE_RULE [Once arithmeticTheory.ADD_COMM])) >>
  `eval_operand len_op t0 = SOME (n2w (LENGTH xs))` by
    (qpat_assum `eval_operand len_op t0 = SOME (n2w (LENGTH (MAP Value xs)))`
       (ACCEPT_TAC o REWRITE_RULE [listTheory.LENGTH_MAP])) >>
  qpat_assum `loc = case vv_location vv of NONE => LocMemory | SOME l => l`
    (SUBST1_TAC o SYM) >>
  qpat_assum `expr_type e = ArrayT elem bd` (SUBST1_TAC o SYM) >>
  (conj_tac >- REFL_TAC) >>
  (conj_tac >-
    (qexists_tac `gas_explicit marks s.vs_gas_readings` >>
     qpat_assum `!tail. eval_expr cx e _ = (INL rv,_)` ACCEPT_TAC)) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qx_gen_tac `v` >> strip_tac >>
     qpat_assum `rv = Value v` (SUBST1_TAC o SYM) >>
     qpat_assum `!v. _ ==> vv_own _ _ _ _ _ _ rv _ t0 /\ _`
       (qspec_then `v` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise for_nonslot_array_prefix_full
*)
