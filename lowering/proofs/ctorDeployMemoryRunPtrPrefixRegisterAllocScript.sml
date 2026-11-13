(* Fresh constructor buffer allocation: identical concrete and ghost endpoints. *)
Theory ctorDeployMemoryRunPtrPrefixRegisterAlloc
Ancestors
  ctorRegisterArgs moduleLowering context compileEnv emitHelper
  ctorDeployMemoryRunPtrPrefixSteps
  ctorDeployMemoryRunPtrPrefixAllocationFloor
  ptrSafeRun ptrDiscipline venomState venomExecSemantics venomInst
  finite_map words arithmetic pred_set list rich_list fragExec memLocDefs codegenRel contextCodegenRel

Theorem prefix_register_alloc_taint:
  FLOOKUP s.vs_allocas aid = NONE /\ n < dimword (:256) ==>
  let i = mk_inst aid ALLOCA [Lit (n2w n)] [x];
      a = update_var x (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (aid,(s.vs_alloca_next,n)); vs_alloca_next := s.vs_alloca_next+n|>)
  in step_taint i s a tn =
    tn with <|t_var := tn.t_var |+ (x,{});
      t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+n}|>
Proof
  strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, out_taint_def,
    mem_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    new_site_bytes_def, step_writes_def, written_taint_def,
    source_memory_write_ranges_def, range_bytes_def, update_var_def,
    eval_operand_def, EXTENSION, taint_component_equality, FLOOKUP_UPDATE] >>
  fs[FLOOKUP_DEF] >> simp[AllCaseEqs()] >> metis_tac[ADD_COMM]
QED

Theorem prefix_register_alloc_window:
  q.t_mem = tn.t_mem UNION {j | p <= j /\ j < p+n} ==>
  (!j. j < p /\ j IN q.t_mem ==> j IN tn.t_mem) /\
  (!B. DISJOINT B tn.t_mem /\ DISJOINT B {j | p <= j /\ j < p+n} ==>
       DISJOINT B q.t_mem)
Proof
  strip_tac >> conj_tac >- (simp[] >> rpt strip_tac >> gvs[] ) >>
  simp[DISJOINT_UNION] >> metis_tac[DISJOINT_SYM]
QED

Theorem prefix_register_alloc_pair:
  FLOOKUP s.vs_allocas aid = NONE /\ n < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst aid ALLOCA [Lit (n2w n)] [x];
      a = update_var x (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (aid,(s.vs_alloca_next,n)); vs_alloca_next := s.vs_alloca_next+n|>);
      H = G |+ (x,(s.vs_alloca_next,n));
      q = tn with <|t_var := tn.t_var |+ (x,{});
        t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+n}|>
  in step_inst_base i s = OK a /\
     ghost_step fuel ctx PG G tn i s = (H,q) /\
     ptr_safe_step D lo fuel ctx fn PG G tn i s /\
     allocas_from lo a /\ lo <= a.vs_alloca_next /\
     (!v. v <> x ==> FLOOKUP H v = FLOOKUP G v /\
       eval_operand (Var v) a = eval_operand (Var v) s /\
       op_taint q (Var v) = op_taint tn (Var v))
Proof
  strip_tac >> simp[] >>
  `step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [x]) s
      (update_var x (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,n));
          vs_alloca_next := n+s.vs_alloca_next|>)) tn =
    tn with <|t_var := tn.t_var |+ (x,{});
      t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < n+s.vs_alloca_next}|>` by
    (drule_all prefix_register_alloc_taint >> simp[ADD_COMM]) >>
  simp[prefix_alloca_step, SRULE [LET_THM] prefix_alloca_ghost_step,
    prefix_alloca_ptr_step] >>
  conj_tac >-
    (simp[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = aid'` >> gvs[allocas_from_def] >> metis_tac[]) >>
  simp[update_var_def, FLOOKUP_UPDATE, eval_operand_def, lookup_var_def, op_taint_def]
QED

Theorem prefix_register_alloc_block:
  FLOOKUP s.vs_allocas aid = NONE /\ n < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst aid ALLOCA [Lit (n2w n)] [x]) ==>
  let a = update_var x (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (aid,(s.vs_alloca_next,n)); vs_alloca_next := s.vs_alloca_next+n|>);
      H = G |+ (x,(s.vs_alloca_next,n));
      q = tn with <|t_var := tn.t_var |+ (x,{});
        t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+n}|>
  in ptr_safe_block D lo fuel ctx fn PG H q bb (a with vs_inst_idx := SUC s.vs_inst_idx) ==>
     ptr_safe_block D lo fuel ctx fn PG G tn bb s
Proof
  strip_tac >>
  drule_all prefix_register_alloc_pair >>
  disch_then (qspecl_then [`x`,`tn`,`fuel`,`fn`,`PG`,`G`,`D`] mp_tac) >>
  simp[] >> strip_tac >> strip_tac >>
  `step_inst fuel ctx (mk_inst aid ALLOCA [Lit (n2w n)] [x]) s =
     OK (update_var x (n2w s.vs_alloca_next)
       (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,n));
         vs_alloca_next := n+s.vs_alloca_next|>))` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  `~is_terminator (mk_inst aid ALLOCA [Lit (n2w n)] [x]).inst_opcode` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all ptr_safe_block_step >> simp[]
QED

Theorem prefix_register_alloc_layout:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa fn /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)]) /\
    sa.cs_current_bb = st.cs_current_bb /\
    LENGTH sa.cs_current_insts = SUC s.vs_inst_idx
Proof
  strip_tac >>
  `sa.cs_current_bb = st.cs_current_bb /\
   sa.cs_current_insts = st.cs_current_insts ++
     [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]]` by
    gvs[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  fs[fn_has_code_def] >>
  gvs[IS_PREFIX_APPEND] >>
  simp[get_instruction_def, EL_APPEND_EQN, LENGTH_APPEND]
QED

Theorem prefix_register_alloc_run_continuation:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa fn /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ n < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let x = STRING #"%" (toString st.cs_next_var);
      a = (update_var x (n2w s.vs_alloca_next)
        (s with <|vs_allocas := s.vs_allocas |+
          (st.cs_next_id,(s.vs_alloca_next,n)); vs_alloca_next := s.vs_alloca_next+n|>))
        with vs_inst_idx := LENGTH sa.cs_current_insts;
      H = G |+ (x,(s.vs_alloca_next,n));
      q = tn with <|t_var := tn.t_var |+ (x,{});
        t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+n}|>
  in ((!fuel. ptr_safe_run D lo fuel ctx fn PG H q a) ==>
       !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  drule_all prefix_register_alloc_layout >> strip_tac >>
  strip_tac >> gen_tac >>
  `ptr_safe_block D lo fuel ctx fn PG G tn bb s` suffices_by
    simp[ptr_safe_run_def] >>
  irule (SRULE [LET_THM] prefix_register_alloc_block) >>
  asm_rewrite_tac[] >> qexistsl_tac [`st.cs_next_id`,`n`,`STRING #"%" (toString st.cs_next_var)`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` (qspec_then `fuel` mp_tac) >>
  `lookup_block st.cs_current_bb fn.fn_blocks = SOME bb` by metis_tac[] >>
  simp[ptr_safe_run_def, update_var_def]
QED

Theorem prefix_register_alloc_actual:
  compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
  n < dimword (:256) /\ alloca_inv initial /\
  alloca_frontier_inv ctx func site initial /\ fn_inst_ids_distinct func /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx ==>
  ?a H q.
    a = (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w initial.vs_alloca_next)
      (initial with <|vs_allocas := initial.vs_allocas |+
        (st.cs_next_id,(initial.vs_alloca_next,n));
        vs_alloca_next := initial.vs_alloca_next+n|>))
      with vs_inst_idx := LENGTH sa.cs_current_insts /\
    H = G |+ (STRING #"%" (toString st.cs_next_var),(initial.vs_alloca_next,n)) /\
    q = tn with <|t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{});
      t_mem := tn.t_mem UNION {j | initial.vs_alloca_next <= j /\ j < initial.vs_alloca_next+n}|> /\
    alloca_inv a /\ alloca_frontier_inv ctx func site a /\
    a.vs_alloca_next = initial.vs_alloca_next+n /\
    a.vs_alloca_next < dimword (:256) /\
    allocas_from lo a /\ lo <= a.vs_alloca_next /\
    ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
    a.vs_inst_idx = LENGTH sa.cs_current_insts /\
    abi_decode_sim ctx func initial a /\
    ((!fuel. ptr_safe_run D lo fuel ctx func PG H q a) ==>
      !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
  strip_tac >> drule_all ctor_alloc_buffer_run >> strip_tac >>
  qexists_tac `a` >> simp[] >>
  reverse conj_tac >-
    (drule_all prefix_register_alloc_run_continuation >> simp[]) >>
  gvs[update_var_def] >>
  simp[allocas_from_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  Cases_on `st.cs_next_id = aid` >> gvs[allocas_from_def] >> metis_tac[]
QED

val _ = export_theory();
