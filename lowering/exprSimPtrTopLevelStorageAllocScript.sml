(* Allocation interface probes for storage/transient aggregate forcing. *)
Theory exprSimPtrTopLevelStorageAlloc
Ancestors
  allocationPtr loweringHalt exprSimPtrProps fragExec fragExecPtr ghostPcTransportPtr rich_list
  exprSimStorageCopy exprSimAlloc exprSimHyps valueEncodingProps
  exprSimHypsDefs exprLoweringProps bodyPtrDefs context compileEnv vyperAST
  venomInst venomState venomExecSemantics venomInstProofs ptrDiscipline words finite_map

Theorem toplevel_storage_fresh_alloca_coverage:
  FLOOKUP s.vs_allocas id = NONE /\
  s.vs_alloca_next + nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK s1 ==>
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s s1 tn) out s1 nb
Proof
  metis_tac[fresh_alloca_ptr_covers]
QED

Theorem toplevel_storage_reused_alloca_coverage:
  FLOOKUP s.vs_allocas id = SOME (b,nb) /\ b+nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s = OK s1 ==>
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s1)
    (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [out]) s s1 tn) out s1 nb
Proof
  strip_tac >> drule reused_alloca_step >>
  disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  irule (cj 1 reused_alloca_ptr_covers) >> simp[]
QED

Theorem toplevel_storage_copy_capacity:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann ==>
  type_memory_bytes cenv ann = 32 * type_slot_size tv /\
  type_memory_bytes cenv ann < 2**64
Proof
  strip_tac >> drule expr_body_pre_copy_ok >>
  simp[expr_type_def, type_memory_size_slots]
QED

(* The ordinary allocation execution boundary re-establishes stmt_state_rel;
   this extracts all loop arithmetic premises without requiring freshness. *)
Theorem toplevel_storage_allocated_bounds:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann /\
  nb = type_memory_bytes cenv ann /\
  stmt_state_rel ctx func cenv cx es s1 /\
  FLOOKUP s1.vs_allocas id = SOME (b,nb) ==>
  nb = 32 * type_slot_size tv /\ type_slot_size tv < 2**256 /\
  b + 32 * type_slot_size tv < 2**256 /\
  b + 32 * type_slot_size tv <= s1.vs_alloca_next
Proof
  strip_tac >> drule_all toplevel_storage_copy_capacity >> strip_tac >>
  `alloca_room ctx func s1 /\ alloca_inv s1` by
    fs[stmt_state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  `b+nb <= s1.vs_alloca_next` by
    (fs[venomMemDefsTheory.alloca_inv_def,
        venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  gvs[dimword_def] >> decide_tac
QED

Theorem toplevel_storage_copy_word_count:
  expr_body_pre cenv cx env (TopLevelName ann nsid) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ ~is_word_type ann ==>
  (type_memory_bytes cenv ann + 31) DIV 32 = type_slot_size tv /\
  type_memory_bytes cenv ann < dimword (:256)
Proof
  strip_tac >> drule_all toplevel_storage_copy_capacity >> strip_tac >>
  gvs[dimword_def] >> decide_tac
QED

(* The ordinary endpoint is kept explicitly: only the instruction cursor
   changes when lifting its successful ALLOCA to a counted pointer path. *)
Theorem toplevel_alloc_buffer_ptr_path:
  compile_alloc_buffer nb sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?Gf tnf p.
    buf.buf_operand = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers Gf tnf p u nb /\
    Gf = step_prov PG G
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [p]) u /\
    tnf = step_taint
      (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [p]) s u tn
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (fs[same_blocks_def, emitted_insts_def, IS_PREFIX_APPEND] >>
     metis_tac[rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
       [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK u` by
    fs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all alloca_step_ptr_covers >> strip_tac >>
  qmatch_asmsub_abbrev_tac `step_inst_base ai s = OK u` >>
  qexistsl_tac [`step_prov PG G ai u`, `step_taint ai s u tn`,
    `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[] >>
  `step_inst 0 ctx ai s = OK u` by
    simp[step_inst_non_invoke, Abbr `ai`, mk_inst_def] >>
  `~u.vs_halted` by
    (drule step_preserves_halted >>
     simp[Abbr `ai`, mk_inst_def, is_terminator_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn ai s` by
    (simp[Abbr `ai`] >> irule ptr_inst_ok_alloca >> simp[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  `ai.inst_opcode <> INVOKE /\ ~is_terminator ai.inst_opcode /\
   ai.inst_opcode <> GAS` by simp[Abbr `ai`, mk_inst_def, is_terminator_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all gas_path_ptr_one_step >> simp[arithmeticTheory.ADD1]
QED

Theorem toplevel_alloca_ghost_frame:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w nb)] [p]) (fn_insts fn) /\
  nb < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s = OK u /\
  FLOOKUP u.vs_allocas id = SOME (b,nb) ==>
  step_prov PG G (mk_inst id ALLOCA [Lit (n2w nb)] [p]) u =
    G |+ (p,(b,nb)) /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_var =
    tn.t_var |+ (p,{}) /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s u tn).t_mem
    SUBSET tn.t_mem UNION {i | b <= i /\ i < b+nb}
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `nb` mp_tac) >>
      simp[] >> disch_then (qspec_then `p` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `p` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`p`, `PG`, `G`, `tn`] strip_assume_tac) >>
  gvs[update_var_def]
QED

Theorem toplevel_alloc_buffer_ptr_run:
  compile_alloc_buffer nb sa = (buf,sb) /\ fn_has_code sa sb fn /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w Gf tnf p.
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    stmt_state_rel ctx fn cenv cx es u /\
    buf.buf_operand = Var p /\ eval_operand (Var p) u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb) /\
    w2n w + nb < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    w2n w + nb <= u.vs_alloca_next /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers Gf tnf p u nb /\ not_fresh_at sb p /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gf x = FLOOKUP G x /\
       op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem SUBSET tn.t_mem UNION {i | w2n w <= i /\ i < w2n w+nb} /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) nb b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
       regions_disjoint (w2n w) nb b len)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all toplevel_alloc_buffer_ptr_path >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    fs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all toplevel_alloca_ghost_frame >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  `w2n w + nb <= t.vs_alloca_next` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ t` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.alloca_next_valid_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `step_inst 0 ctx
    (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    simp[step_inst_non_invoke, mk_inst_def] >>
  `~t.vs_halted` by
    (drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule step_preserves_control_flow >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`t`, `w`, `Gf`, `tnf`, `p`] >>
  gvs[same_blocks_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
      simp[FLOOKUP_UPDATE, op_taint_def]) >>
  metis_tac[]
QED

Theorem toplevel_alloca_static_effects:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [p]) s = OK u ==>
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\ u.vs_memory = s.vs_memory /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  simp[step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  `aid <> id` by metis_tac[optionTheory.NOT_SOME_NONE] >>
  simp[FLOOKUP_UPDATE]
QED

Theorem toplevel_alloc_buffer_static_effects:
  compile_alloc_buffer nb sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  u.vs_call_ctx = s.vs_call_ctx /\ u.vs_accounts = s.vs_accounts /\
  u.vs_transient = s.vs_transient /\ u.vs_memory = s.vs_memory /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry)
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  fs[run_inst_seq_def, AllCaseEqs()] >>
  drule toplevel_alloca_static_effects >> simp[]
QED
