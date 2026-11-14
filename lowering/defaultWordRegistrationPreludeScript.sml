(* Compilation and common execution boundary before primitive-word decoding. *)
Theory defaultWordRegistrationPrelude
Ancestors calldataRegistrationExec moduleLowering compileEnv emitHelper
  finite_map words arithmetic ctorDeployMemoryRunPtrPrefixRegisterAlloc
  ctorDeployMemoryRunPtrPrefixRegisterAddress dispatchedDecoderTrace
  ctorDeployLoweringEntryRegisterRun ctorDeployMemoryRunMemEntryRegistration
  abiEncoderProps loweringHalt fragExec context abiDecoderReentry
  loweringStateRelDefs bodyPtrDefs venomState ptrDiscipline localPtrsProps
  ctorDeployLoweringEntryAllocation emitHelperProps venomInst venomExecSemantics
  slotCopyExecution exprLoweringProps rich_list

Theorem default_word_registration_split:
  compile_register_positional_args ce
    ((name,T,dyn,sz,info)::rest) off st = (cef,final) /\
  FLOOKUP ce.ce_vars name = SOME loc /\
  var_location_memory_size loc = SOME 32 /\
  (?c. info = DecPrimWord c) ==>
  ?buf allocated ce1 src first decoded.
    compile_alloc_buffer 32 st = (buf,allocated) /\
    ce1 = (ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand 32)) /\
    emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (src,first) /\
    compile_abi_decode_to_buf buf.buf_operand src CALLDATALOAD
      (Lit 0w) (Lit 0w) info first = ((),decoded) /\
    compile_register_positional_args ce1 rest (off+sz) decoded = (cef,final)
Proof
  strip_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  simp[Once compile_register_positional_args_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `_0` >>
  `var_location_decode_operand (PtrVar buf.buf_operand 32) =
     SOME buf.buf_operand` by simp[var_location_decode_operand_def] >>
  drule registration_decoder_prelude >>
  simp[FLOOKUP_UPDATE] >>
  disch_then strip_assume_tac >>
  qexistsl_tac [`head`, `after_head`, `cs''`] >> gvs[] >>
  `ce with ce_vars := ce.ce_vars |+ (name,PtrVar buf.buf_operand 32) =
   ce with ce_vars updated_by (\m. m |+ (name,PtrVar buf.buf_operand 32))` by
    simp[compile_env_component_equality] >>
  pop_assum SUBST1_TAC >> simp[]
QED

Theorem literal_add_ghost[local]:
  ghost_step fuel ctx PG G tn (mk_inst iid ADD [Lit (u:bytes32);Lit (v:bytes32)] [x]) s =
  (DRESTRICT G (COMPL {x}), tn with t_var := tn.t_var |+ (x,{}))
Proof
  `eval_operand (Lit u) s = SOME u /\ eval_operand (Lit v) s = SOME v` by
    simp[eval_operand_def] >>
  mp_tac (ctorDeployMemoryRunPtrPrefixBoolBodyTheory.prefix_bool_body_add_ghost
    |> Q.INST [`a` |-> `Lit u`, `b` |-> `Lit v`]) >>
  simp[eval_operand_def] >>
  simp[LET_THM] >>
  strip_tac >>
  simp[ptrDisciplineTheory.first_prov_def, ptrDisciplineTheory.set_prov_def,
    ctorDeployMemoryRunPtrPrefixMemberSetupTheory.prefix_member_add_taint, op_taint_def]
QED

Theorem default_word_registration_prelude:
  compile_alloc_buffer 32 st = (buf,allocated) /\
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] allocated = (src,first) /\
  fn_has_code st first fn /\
  alloca_inv s /\ alloca_frontier_inv_from k ctx fn site s /\
  fn_inst_ids_distinct fn /\ k + unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  alloca_history fn s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready H u p.
    buf.buf_operand = Var p /\
    eval_operand (Var p) ready = SOME (n2w s.vs_alloca_next) /\
    eval_operand src ready = SOME ((n2w 4 + n2w (off-4)):bytes32) /\
    abi_decoder_operand_live first.cs_next_var (Var p) /\
    abi_decoder_operand_live first.cs_next_var src /\
    not_fresh_at first p /\ (!v. src = Var v ==> not_fresh_at first v) /\
    ptr_covers H u p ready 32 /\ op_taint u src = {} /\
    FLOOKUP ready.vs_allocas st.cs_next_id = SOME (s.vs_alloca_next,32) /\
    ready.vs_alloca_next = s.vs_alloca_next + 32 /\
    s.vs_alloca_next + 32 < dimword (:256) /\
    alloca_inv ready /\ alloca_frontier_inv_from k ctx fn site ready /\
    allocas_from lo ready /\ lo <= ready.vs_alloca_next /\
    alloca_history fn ready /\
    ~ready.vs_halted /\ ready.vs_current_bb = first.cs_current_bb /\
    ready.vs_inst_idx = LENGTH first.cs_current_insts /\
    ready = (s with <|vs_vars := ready.vs_vars;
      vs_allocas := ready.vs_allocas; vs_alloca_next := ready.vs_alloca_next;
      vs_inst_idx := LENGTH first.cs_current_insts|>) /\
    st.cs_next_id < first.cs_next_id /\ st.cs_next_var <= first.cs_next_var /\
    (!id. id <> st.cs_next_id ==> FLOOKUP ready.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op ready = eval_operand op s) /\
    (!v. not_fresh_at st v ==> FLOOKUP H v = FLOOKUP G v /\
      op_taint u (Var v) = op_taint tn (Var v)) /\
    u.t_mem = tn.t_mem UNION
      {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    gas_path_mem ctx fn s 0 (OK ready) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) [] (OK ready,H,u)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u ready) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `cs_extends st allocated` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends allocated first` by metis_tac[prefix_register_address_emit_shape] >>
  drule_all fn_has_code_split >> strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all deploy_ctor_register_alloc_run >> strip_tac >>
  `emit_op ALLOCA [Lit (n2w 32)] st = (buf.buf_operand,allocated)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  drule prefix_register_address_emit_shape >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any strip_assume_tac prefix_register_address_emit_shape) >>
  qmatch_asmsub_abbrev_tac `update_var p _ _` >>
  qabbrev_tac `q = tn with <|t_var := tn.t_var |+ (p,{});
    t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+32}|>` >>
  qabbrev_tac `H0 = G |+ (p,(s.vs_alloca_next,32))` >>
  qabbrev_tac `x = STRING #"%" (toString allocated.cs_next_var)` >>
  qabbrev_tac `ready = (update_var x (4w + n2w (off-4)) a)
    with vs_inst_idx := LENGTH first.cs_current_insts` >>
  `p <> x` by
    (simp[Abbr `p`, Abbr `x`] >>
     simp[ASCIInumbersTheory.toString_11]) >>
  qabbrev_tac `raw = update_var p (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,32));
      vs_alloca_next := s.vs_alloca_next+32|>)` >>
  `raw = update_var (STRING #"%" (toString st.cs_next_var)) (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,32));
      vs_alloca_next := s.vs_alloca_next+32|>)` by simp[Abbr `raw`, Abbr `p`] >>
  drule_all ctor_checked_alloc_buffer_edge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `raw = _` kall_tac >>
  `gas_path_mem ctx fn s 0 (OK a) /\ alloca_history fn a` by metis_tac[] >>
  qunabbrev_tac `raw` >>
  `a.vs_inst_idx = LENGTH allocated.cs_current_insts` by simp[] >>
  `run_inst_seq (emitted_insts allocated first) a =
    OK (update_var x (4w+n2w (off-4)) a)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     `step_inst_base (mk_inst allocated.cs_next_id ADD [Lit 4w;Lit (n2w (off-4))]
        [STRING #"%" (toString allocated.cs_next_var)]) a =
        OK (update_var x (4w+n2w (off-4)) a)` by
       (simp[Abbr `x`] >> irule slot_copy_step_add >> simp[eval_operand_def]) >>
     qpat_x_assum `emitted_insts allocated first = _` SUBST1_TAC >>
     pure_rewrite_tac[run_inst_seq_def] >>
     qpat_x_assum `step_inst_base _ a = _` (fn th => rewrite_tac[th, run_inst_seq_def]) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts allocated first) a` by
    (irule ctor_checked_arg_add_mem_ok >> goal_assum (drule_at Any)) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts allocated first)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `inst_extends allocated first` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[inst_extends_def, IS_PREFIX_APPEND]) >>
  ` (update_var x (4w+n2w (off-4)) a).vs_allocas = a.vs_allocas /\
    (update_var x (4w+n2w (off-4)) a).vs_current_bb = a.vs_current_bb` by simp[update_var_def] >>
  drule_all ctor_checked_arg_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl [`ready`, `DRESTRICT H0 (COMPL {x})`,
    `q with t_var := q.t_var |+ (x,{})`, `p`] >>
  pure_rewrite_tac[CONJ_ASSOC] >>
  reverse conj_tac >- suspend "pullback" >>
  reverse conj_tac >- suspend "origin" >>
  reverse conj_tac >- suspend "memory" >>
  suspend "fields"
QED

Resume default_word_registration_prelude[fields]:
  pure_rewrite_tac[GSYM CONJ_ASSOC] >>
  simp[] >>
  conj_tac >- simp[Abbr `ready`, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `ready`, update_var_def, eval_operand_def,
    lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    Abbr `p`, ASCIInumbersTheory.toString_11] >>
  conj_tac >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    Abbr `x`, ASCIInumbersTheory.toString_11] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `p`, ASCIInumbersTheory.toString_11] >>
  conj_tac >- simp[not_fresh_at_def, Abbr `x`, ASCIInumbersTheory.toString_11] >>
  conj_tac >-
    (simp[ptr_covers_def, op_taint_def, Abbr `q`, Abbr `H0`, Abbr `ready`,
      update_var_def, lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT,
      w2n_n2w] >>
     `s.vs_alloca_next < dimword (:256)` by decide_tac >> simp[]) >>
  conj_tac >- simp[op_taint_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `ready`, update_var_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[Abbr `ready`, update_var_def] >>
  conj_tac >-
    (irule alloca_inv_fields >> qexists `a` >> simp[Abbr `ready`, update_var_def]) >>
  conj_tac >-
    (irule deploy_ctor_alloca_frontier_fields >>
     qexistsl [`a`,`site`] >> simp[Abbr `ready`, update_var_def]) >>
  conj_tac >-
    (simp[Abbr `ready`, update_var_def, allocas_from_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `aid = st.cs_next_id` >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  conj_tac >- simp[Abbr `ready`, update_var_def] >>
  conj_tac >- suspend "history" >>
  simp[Abbr `ready`, update_var_def] >>
  conj_tac >- (rpt strip_tac >> simp[FLOOKUP_UPDATE]) >>
  conj_tac >-
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     `s' <> p /\ s' <> x` by
       (simp[Abbr `p`, Abbr `x`] >> metis_tac[DECIDE ``!n:num. n <= n+1``]) >>
     simp[]) >>
  conj_tac >-
    (rpt strip_tac >>
     `v <> p /\ v <> x` by
       (gvs[not_fresh_at_def, Abbr `p`, Abbr `x`] >> metis_tac[DECIDE ``!n:num. n <= n+1``]) >>
     simp[Abbr `H0`, Abbr `q`, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def]) >>
  simp[Abbr `q`]
QED

Resume default_word_registration_prelude[history]:
  metis_tac[Abbr `ready`]
QED

Resume default_word_registration_prelude[memory]:
  `gas_path_mem ctx fn a 0 (OK ready)` by metis_tac[Abbr `ready`] >>
  metis_tac[fragGasPathMemTheory.gas_path_mem_then, ADD]
QED

Resume default_word_registration_prelude[origin]:
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) [] (OK a,H0,q)` by
    (qpat_x_assum `a = _` SUBST1_TAC >>
     simp_tac bool_ss [Abbr `H0`, Abbr `q`, Abbr `p`] >>
     irule prefix_register_address_emit_origin >>
     conj_tac >- simp[] >>
     qexistsl [`ALLOCA`,`[Lit (n2w 32)]`,`buf.buf_operand`,`st`] >>
     `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
        [STRING #"%" (toString st.cs_next_var)]) s =
       OK (update_var (STRING #"%" (toString st.cs_next_var)) (n2w s.vs_alloca_next)
         (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,32));
           vs_alloca_next := s.vs_alloca_next+32|>)) /\
       ghost_step 0 ctx PG G tn (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
         [STRING #"%" (toString st.cs_next_var)]) s =
       (G |+ (STRING #"%" (toString st.cs_next_var),(s.vs_alloca_next,32)),
        tn with <|t_var := tn.t_var |+ (STRING #"%" (toString st.cs_next_var),{});
          t_mem := tn.t_mem UNION {j | s.vs_alloca_next <= j /\ j < s.vs_alloca_next+32}|>) /\
       ptr_safe_step D lo 0 ctx fn PG G tn
         (mk_inst st.cs_next_id ALLOCA [Lit (n2w 32)]
           [STRING #"%" (toString st.cs_next_var)]) s` by
       (drule_all (Q.INST [`n` |-> `32`] prefix_register_alloc_pair) >>
        disch_then (qspecl_then [`STRING #"%" (toString st.cs_next_var)`, `tn`, `0`, `fn`, `PG`, `G`, `D`] mp_tac) >>
        simp[] >> strip_tac >> asm_rewrite_tac[]) >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (a,H0,q) []
     (OK ready,DRESTRICT H0 (COMPL {x}),q with t_var := q.t_var |+ (x,{}))` by
    (simp_tac bool_ss [Abbr `ready`, Abbr `x`] >>
     irule prefix_register_address_emit_origin >>
     conj_tac >- simp[] >>
     qexistsl [`ADD`,`[Lit 4w; Lit (n2w (off-4))]`,`src`,`allocated`] >>
     `step_inst_base (mk_inst allocated.cs_next_id ADD [Lit 4w;Lit (n2w (off-4))]
        [STRING #"%" (toString allocated.cs_next_var)]) a =
        OK (update_var (STRING #"%" (toString allocated.cs_next_var)) (4w+n2w (off-4)) a)` by
       (irule slot_copy_step_add >> simp[eval_operand_def]) >>
     simp_tac (srw_ss()) [run_inst_seq_def, is_terminator_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >>
     asm_rewrite_tac[] >>
     conj_tac >- simp[ptrSafeRunTheory.ghost_step_def, step_inst_non_invoke, mk_inst_def] >>
     conj_tac >-
       simp[literal_add_ghost] >>
     irule ctorDeployMemoryRunPtrPrefixBoolBodyTheory.prefix_bool_body_arith_ptr_step >>
     simp[eval_operand_def,op_taint_def,allocas_from_def,update_var_def,FLOOKUP_UPDATE] >>
     rpt strip_tac >> gvs[allocas_from_def] >>
     Cases_on `st.cs_next_id = aid` >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
    (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append) >>
  simp[NoAsms] >> disch_then irule >> simp[]
QED

Resume default_word_registration_prelude[pullback]:
  gen_tac >> strip_tac >>
  `(!fuel. ptr_safe_run D lo fuel ctx fn PG H0 q a) ==>
    !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s` by
    (drule_all prefix_register_alloc_run_continuation >>
     simp[NoAsms, LET_THM] >>
     disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
     simp[Abbr `H0`, Abbr `q`, Abbr `p`]) >>
  first_x_assum irule >>
  `allocas_from lo a` by
    (simp[allocas_from_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `st.cs_next_id = aid` >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  irule (SRULE [LET_THM] prefix_register_address_add_run) >>
  simp[] >>
  qexistsl [`Lit 4w`,`Lit (n2w (off-4))`,`first`,`src`,`allocated`,
    `4w`,`n2w (off-4)`] >>
  simp[eval_operand_def, op_taint_def, ptrDisciplineTheory.first_prov_def,
    ptrDisciplineTheory.set_prov_def, Abbr `ready`, Abbr `x`] >>
  gvs[]
QED

Finalise default_word_registration_prelude
