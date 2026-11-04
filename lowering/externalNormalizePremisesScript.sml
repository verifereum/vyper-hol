(* Producer boundaries for the actual external Return normalization branch. *)
Theory externalNormalizePremises
Ancestors
  externalReturnBounds typedNormalizeProducer valueEncodingTyping
  typedNormalizeStaticRigidity valueCopyBytes vyperTypeSystem
  exprSim vyperTyping vyperValue compileEnv valueEncoding
  externalReturnNormalizeMem allocaSiteResource exprLoweringProps
  venomMemDefs venomExecSemantics finite_map stmtSimReturnWiden exprSimAlloc
  stmtSimDecl loweringHalt

Theorem normalize_nonbytes_footprint[local]:
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  ~is_bytestring_type ty ==>
  val_footprint tv v = type_memory_size tv
Proof
  strip_tac >> Cases_on `v` >> simp[val_footprint_def] >>
  gvs[value_has_type_def] >> Cases_on `ty` >>
  gvs[evaluate_type_def, is_bytestring_type_def, AllCaseEqs()]
QED

Theorem normalize_source_window:
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ~is_word_type ty /\ ~is_bytestring_type ty ==>
  ?w. eval_operand op s = SOME w /\
    (type_memory_size tv = 0 \/
     w2n w + type_memory_size tv <= s.vs_alloca_next) /\
    w2n w + type_memory_size tv < dimword (:256)
Proof
  strip_tac >> drule_all normalize_nonbytes_footprint >> strip_tac >>
  drule_all expr_val_at_frontier >> strip_tac >>
  qexists_tac `w` >> simp[] >>
  drule_all stmtSimReturnTheory.expr_val_at_bound >> simp[]
QED

(* A real normalization site, including re-entry at an already recorded site.
   The source address is kept as a natural number here; operand transport is
   supplied separately by allocation's existing register-frame boundary. *)
Theorem normalize_site_windows:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  expr_val_at cenv cx ty sa sb es v src s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  ~is_word_type ty /\ ~is_bytestring_type ty /\
  0 < type_memory_size tv /\ eval_operand src s = SOME p /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w n)] /\ inst.inst_outputs = [out] /\
  not_local_ptr cenv es.scopes out /\ sb.cs_next_id <= inst.inst_id /\
  n < dimword (:256) ==>
  ?t b. exec_alloca inst s (n2w n : bytes32) = OK t /\
    lookup_var out t = SOME (n2w b) /\ alloca_room ctx func t /\ alloca_inv t /\
    w2n p + type_memory_size tv <= t.vs_alloca_next /\
    b + n <= t.vs_alloca_next /\
    w2n p + type_memory_size tv < dimword (:256) /\
    b + n < dimword (:256) /\
    venomMemDefs$regions_disjoint (w2n p,type_memory_size tv) (b,n) /\
    t.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    (drule_all normalize_nonbytes_footprint >> simp[]) >>
  `0 < val_footprint tv v` by simp[] >>
  drule_all normalize_source_window >> strip_tac >> gvs[] >>
  `alloca_room ctx func s /\ alloca_inv s` by fs[stmt_state_rel_def] >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n (n2w n : bytes32)` by
    (fs[stmt_state_rel_def] >> rpt strip_tac >>
     qpat_x_assum `!inst n base sz. _` drule_all >> simp[]) >>
  drule_all alloca_site_execute >> strip_tac >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n (n2w n : bytes32) /\
    venomMemDefs$regions_disjoint (w2n p,type_memory_size tv) (b,sz)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_x_assum `!b sz. FLOOKUP s.vs_allocas _ = _ ==> _` irule >>
         goal_assum (drule_at Any)) >>
     `0 < val_footprint tv v` by asm_rewrite_tac[] >>
     drule_all normalize_alloca_source_separate >>
     pure_rewrite_tac[venomMemDefsTheory.regions_disjoint_def] >>
     asm_rewrite_tac[] >> decide_tac) >>
  `w2n p + type_memory_size tv <= s.vs_alloca_next` by decide_tac >>
  drule_all alloca_site_execute_protected >> strip_tac >>
  qexistsl_tac [`t`,`b`] >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  gvs[venomMemDefsTheory.regions_disjoint_def, arithmeticTheory.LESS_MOD] >>
  simp[] >> decide_tac
QED

Theorem normalize_return_source_kinds:
  type_widens_to tenv sty dty /\
  ~is_word_type dty /\
  ~(is_bytestring_type dty /\ is_bytestring_type sty) /\ sty <> dty ==>
  ~is_word_type sty /\ ~is_bytestring_type sty /\ ~is_bytestring_type dty
Proof
  strip_tac >>
  `~is_word_type sty` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type dty` by metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  simp[] >> strip_tac >>
  Cases_on `sty` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def] >>
      Cases_on `dty` >> gvs[type_widens_to_def, arg_type_fits_def] >>
      rename1 `BaseT db` >> Cases_on `db` >>
      gvs[arg_type_fits_def, is_bytestring_type_def] >>
      rename1 `BytesT dd` >> Cases_on `dd` >>
      gvs[arg_type_fits_def, is_bytestring_type_def]) >>
  Cases_on `dty` >> gvs[type_widens_to_def, arg_type_fits_def] >>
  rename1 `BaseT db` >> Cases_on `db` >>
  gvs[arg_type_fits_def, is_bytestring_type_def]
QED

(* Empty aggregate layouts cannot undergo a genuine widening. *)
Theorem normalize_zero_layout_identity_joint[local]:
  (!sty dty. arg_type_fits sty dty ==>
    !tenv tv. (evaluate_type tenv sty = SOME tv \/
               evaluate_type tenv dty = SOME tv) /\
      type_memory_size tv = 0 ==> sty = dty) /\
  (!stys dtys. arg_types_fit stys dtys ==>
    !tenv tvs. (evaluate_types tenv stys [] = SOME tvs \/
                evaluate_types tenv dtys [] = SOME tvs) /\
      type_memory_size_list tvs = 0 ==> stys = dtys)
Proof
  ho_match_mp_tac arg_type_fits_ind >>
  rw[arg_type_fits_def, evaluate_type_def, type_memory_size_def,
     AllCaseEqs()] >>
  gvs[type_memory_size_def, evaluate_types_OPT_MMAP, AllCaseEqs()] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `tenv` >> simp[]
QED

Theorem normalize_return_source_positive:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME tv ==> 0 < type_memory_size tv
Proof
  strip_tac >> Cases_on `type_memory_size tv = 0` >> simp[] >>
  `arg_type_fits sty dty` by fs[type_widens_to_def] >>
  drule (cj 1 normalize_zero_layout_identity_joint) >>
  disch_then (qspecl_then [`tenv`,`tv`] mp_tac) >> simp[]
QED

Theorem normalize_return_alloc_windows:
  compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\
  expr_val_at cenv cx sty sa sb es v src s /\
  type_widens_to (get_tenv cx) sty dty /\
  ~is_word_type dty /\
  ~(is_bytestring_type dty /\ is_bytestring_type sty) /\ sty <> dty /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\
  eval_operand src s = SOME p /\ n < dimword (:256) /\
  (!x. src = Var x ==> not_fresh_at sb x) ==>
  ?t b. exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
    lookup_var (STRING #"%" (toString sb.cs_next_var)) t = SOME (n2w b) /\
    alloca_room ctx func t /\ alloca_inv t /\
    w2n p + type_memory_size tv <= t.vs_alloca_next /\
    b + n <= t.vs_alloca_next /\
    w2n p + type_memory_size tv < dimword (:256) /\
    b + n < dimword (:256) /\
    venomMemDefs$regions_disjoint (w2n p,type_memory_size tv) (b,n) /\
    t.vs_memory = s.vs_memory /\
    eval_operand src t = SOME p /\ eval_operand buf.buf_operand t = SOME (n2w b)
Proof
  strip_tac >> drule_all normalize_return_source_kinds >> strip_tac >>
  `0 < type_memory_size tv` by metis_tac[normalize_return_source_positive] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sb.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `src <> Var (STRING #"%" (toString sb.cs_next_var))` by metis_tac[] >>
  `!t b. exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
      lookup_var (STRING #"%" (toString sb.cs_next_var)) t = SOME (n2w b) ==>
      eval_operand src t = SOME p /\ eval_operand buf.buf_operand t = SOME (n2w b)` by
    (rpt strip_tac >> simp[venomStateTheory.eval_operand_def] >>
     drule exec_alloca_operand_frame >>
     simp[venomInstTheory.mk_inst_def] >>
     disch_then (qspec_then `src` mp_tac) >> simp[]) >>
  `(?t b. exec_alloca (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sb.cs_next_var)]) s (n2w n : bytes32) = OK t /\
     lookup_var (STRING #"%" (toString sb.cs_next_var)) t = SOME (n2w b) /\
     alloca_room ctx func t /\ alloca_inv t /\
     w2n p + type_memory_size tv <= t.vs_alloca_next /\
     b + n <= t.vs_alloca_next /\
     w2n p + type_memory_size tv < dimword (:256) /\ b + n < dimword (:256) /\
     venomMemDefs$regions_disjoint (w2n p,type_memory_size tv) (b,n) /\
     t.vs_memory = s.vs_memory)` suffices_by metis_tac[] >>
  irule normalize_site_windows >>
  goal_assum (drule_at Any) >> simp[venomInstTheory.mk_inst_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cx`,`sa`,`sb`,`src`,`sty`,`v`] >> simp[]
QED

Theorem normalize_return_destination_positive:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv dty = SOME tv ==> 0 < type_memory_size tv
Proof
  strip_tac >> Cases_on `type_memory_size tv = 0` >> simp[] >>
  `arg_type_fits sty dty` by fs[type_widens_to_def] >>
  drule (cj 1 normalize_zero_layout_identity_joint) >>
  disch_then (qspecl_then [`tenv`,`tv`] mp_tac) >> simp[]
QED

Theorem normalize_return_value_layout:
  type_widens_to tenv sty dty /\ sty <> dty /\
  evaluate_type tenv sty = SOME stv /\ value_has_type stv v /\
  (!ty tv. evaluate_type tenv ty = SOME tv ==>
     type_memory_bytes cenv ty = type_memory_size tv) ==>
  ?dtv. evaluate_type tenv dty = SOME dtv /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_memory_bytes cenv dty = type_memory_size dtv /\
    0 < type_memory_size dtv
Proof
  strip_tac >>
  drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >>
  strip_tac >> qexists_tac `tu` >> simp[] >>
  conj_tac >- metis_tac[cj 1 value_has_type_val_wf] >>
  conj_tac >- metis_tac[cj 1 value_has_type_val_wf] >>
  metis_tac[normalize_return_destination_positive]
QED
