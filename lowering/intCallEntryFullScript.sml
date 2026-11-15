(* The physical parameter captures and fixed-base assignment at an
   internal entry carry one joint path. Materialization follows them. *)
Theory intCallEntryFull
Ancestors
  intCallCallee fragGasSeqPtr fragGasOriginPtr fragExecMem ptrSafeRun
  ptrDiscipline venomExecSemantics venomInst venomState list
  contextCodegenRel codegenRel memSafeRun unitTransformDefs
  instIdxIndep venomExecProofs
  exprLoweringProps fragExec venomMemProps finite_map pred_set contextProps

Theorem internal_capture_inst_ptr:
  MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo fuel ctx func G tn inst s
Proof
  strip_tac >> fs[MEM] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def,
       op_taint_def, step_inst_non_invoke, step_inst_base_opcode_eqs,
       update_var_def, eval_operand_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem internal_capture_step_ghost:
  MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  step_inst_base inst s = OK u ==>
  u = s with vs_vars := u.vs_vars /\
  step_taint inst s u tn = tn with t_var := tn.t_var |+ (out,{}) /\
  step_prov PG G inst u =
    set_prov G [out]
      (if inst.inst_opcode = PARAM /\ w2n idx < LENGTH PG
       then EL (w2n idx) PG else NONE)
Proof
  strip_tac >> fs[MEM] >>
  `u = s with vs_vars := u.vs_vars` by
    (qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[update_var_def]) >>
  `new_site_bytes s u = {}` by
    (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[new_site_bytes_def, EXTENSION, FLOOKUP_DEF] >> metis_tac[]) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, step_writes_def,
       source_memory_write_ranges_def, range_bytes_def, set_var_taint_def,
       out_taint_def, op_taint_def, eval_operand_def, adopt_reset_def,
       store_taint_def, imm_taint_def, taint_component_equality,
       step_prov_def, out_prov_def, first_prov_def, op_prov_def]
QED

Theorem internal_capture_seq_ptr:
  !code s t G tn.
    EVERY (\inst.
      MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
      ?idx out. inst.inst_operands = [Lit idx] /\
                inst.inst_outputs = [out]) code /\
    allocas_from lo s /\ ~ctx_has_dalloca ctx /\
    run_inst_seq code s = OK t ==>
    ?G' tn'. !D. inst_seq_ptr D lo ctx func PG G tn code s G' tn'
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `h.inst_opcode <> INVOKE /\ ~is_terminator h.inst_opcode /\
   h.inst_opcode <> ALLOCA /\ h.inst_opcode <> DALLOCA` by
    fs[MEM, is_terminator_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (fs[EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_x_assum `!inst. MEM inst code ==> _`
       (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> fs[MEM, is_terminator_def]) >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >>
  `allocas_from lo (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  first_x_assum (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`,
     `step_prov PG G h u`, `step_taint h s u tn`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`] >> gen_tac >>
  simp[inst_seq_ptr_def] >>
  irule internal_capture_inst_ptr >> simp[MEM] >> metis_tac[]
QED

Theorem internal_capture_seq_ghost_frame:
  !code s G tn G' tn'.
    EVERY (\inst.
      MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
      ?idx out. inst.inst_operands = [Lit idx] /\
                inst.inst_outputs = [out]) code /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' ==>
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !x. (!inst. MEM inst code ==> ~MEM x inst.inst_outputs) ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  rename1 `h.inst_operands = [Lit idx]` >>
  rename1 `h.inst_outputs = [out]` >>
  mp_tac (Q.INST [`inst` |-> `h`, `idx` |-> `idx`, `out` |-> `out`,
    `s` |-> `s`, `u` |-> `u`, `tn` |-> `tn`, `PG` |-> `PG`, `G` |-> `G`]
    (SPEC_ALL internal_capture_step_ghost)) >>
  (impl_tac >- simp[MEM]) >> strip_tac >>
  qpat_x_assum `!s G tn G' tn'. _` (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `step_prov PG G h u`, `step_taint h s u tn`, `G'`, `tn'`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  rpt strip_tac >>
  `~MEM x h.inst_outputs /\
   (!inst. MEM inst code ==> ~MEM x inst.inst_outputs)` by
    (qpat_x_assum `!inst. inst = h \/ MEM inst code ==> _` mp_tac >>
     simp[DISJ_IMP_THM, FORALL_AND_THM]) >>
  `x <> out` by
    (qpat_x_assum `!inst. inst = h \/ MEM inst code ==> _`
       (qspec_then `h` mp_tac) >>
     qpat_assum `h.inst_outputs = [out]`
       (fn th => simp_tac (srw_ss()) [th, MEM])) >>
  qpat_x_assum `!x. (!inst. MEM inst code ==> _) ==> _`
    (qspec_then `x` mp_tac) >> simp[] >> strip_tac >>
  fs[MEM, set_prov_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem internal_capture_seq_output:
  !code s t G tn G' tn'.
    EVERY (\inst.
      MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
      ?idx out. inst.inst_operands = [Lit idx] /\
                inst.inst_outputs = [out]) code /\
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) code)) /\
    run_inst_seq code s = OK t /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' ==>
    !inst idx out.
      MEM inst code /\ inst.inst_operands = [Lit idx] /\
      inst.inst_outputs = [out] ==>
      FLOOKUP G' out =
        (if inst.inst_opcode = PARAM /\ w2n idx < LENGTH PG
         then EL (w2n idx) PG else NONE) /\
      op_taint tn' (Var out) = {}
Proof
  Induct >- simp[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  rename1 `h.inst_operands = [Lit idx]` >>
  rename1 `h.inst_outputs = [out]` >>
  mp_tac (Q.INST [`inst` |-> `h`, `idx` |-> `idx`, `out` |-> `out`,
    `s` |-> `s`, `u` |-> `u`, `tn` |-> `tn`, `PG` |-> `PG`, `G` |-> `G`]
    (SPEC_ALL internal_capture_step_ghost)) >>
  (impl_tac >- simp[MEM]) >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (fs[EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_x_assum `!inst. MEM inst code ==> _ /\ ?idx out. _`
       (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> fs[MEM, is_terminator_def]) >>
  qpat_x_assum `!s t G tn G' tn'. _` (qspecl_then
    [`u with vs_inst_idx := SUC s.vs_inst_idx`,
     `t with vs_inst_idx := SUC s.vs_inst_idx`,
     `step_prov PG G h u`, `step_taint h s u tn`, `G'`, `tn'`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
  `!i. MEM i code ==> ~MEM out i.inst_outputs` by
    (fs[MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `FLOOKUP G' out = FLOOKUP (step_prov PG G h u) out /\
   op_taint tn' (Var out) = op_taint (step_taint h s u tn) (Var out)` by
    (drule_all (SRULE [MEM] internal_capture_seq_ghost_frame) >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `inst = h`
   >- (gvs[] >> simp[op_taint_def, FLOOKUP_UPDATE, set_prov_def] >>
       rpt CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
   `MEM inst code` by fs[MEM] >>
   qpat_x_assum `!inst idx out. MEM inst code /\ _ ==> _`
     (qspecl_then [`inst`, `idx'`, `out'`] mp_tac) >> simp[])
QED

Theorem compile_internal_entry_prefix_distinct_outputs:
  compile_internal_entry_prefix cenv params has_rb sa =
    ((ce,caps,rpc),sb) ==>
  ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) (emitted_insts sa sb)))
Proof
  strip_tac >> drule compile_internal_entry_prefix_shape >> strip_tac >>
  `!n. FLAT (GENLIST (\i. [STRING #"%" (toString (sa.cs_next_var + i))]) n) =
       GENLIST (\i. STRING #"%" (toString (sa.cs_next_var + i))) n` by
    (gen_tac >>
     mp_tac (Q.ISPEC `GENLIST (\i. STRING #"%" (toString (sa.cs_next_var + i))) n`
       (GEN_ALL SINGL_LIST_APPLY_R)) >>
     simp[LIST_BIND_def, MAP_GENLIST, combinTheory.o_DEF]) >>
  simp[MAP_GENLIST, combinTheory.o_DEF, mk_inst_def, FLAT_APPEND,
       ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST,
       ASCIInumbersTheory.toString_inj, MEM_GENLIST] >>
  rpt strip_tac >>
  gvs[ALL_DISTINCT_GENLIST, MEM_GENLIST, ASCIInumbersTheory.toString_inj] >>
  Cases_on `has_rb` >> gvs[] >> decide_tac
QED

Theorem compile_internal_entry_prefix_ghost_outputs:
  compile_internal_entry_prefix cenv params has_rb sa =
    ((ce,caps,rpc),sb) /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params /\
  LENGTH s.vs_params < dimword (:256) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' ==>
  (op_prov G' rpc = NONE /\ op_taint tn' rpc = {}) /\
  (!i. i < (if has_rb then 1 else 0) + LENGTH params ==>
    FLOOKUP G' (STRING #"%" (toString (sa.cs_next_var + i))) =
      (if i < LENGTH PG then EL i PG else NONE) /\
    op_taint tn' (Var (STRING #"%" (toString (sa.cs_next_var + i)))) = {})
Proof
  strip_tac >> drule compile_internal_entry_prefix_capture_code >> strip_tac >>
  drule compile_internal_entry_prefix_distinct_outputs >> strip_tac >>
  mp_tac (Q.INST
    [`code` |-> `emitted_insts sa sb`, `s` |-> `s`, `t` |-> `t`,
     `G` |-> `G`, `tn` |-> `tn`, `G'` |-> `G'`, `tn'` |-> `tn'`,
     `D` |-> `D`, `lo` |-> `lo`, `ctx` |-> `ctx`, `func` |-> `func`,
     `PG` |-> `PG`] (SPEC_ALL internal_capture_seq_output)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule compile_internal_entry_prefix_shape >> strip_tac >>
  conj_tac
  >- (qpat_assum `!inst idx out. MEM inst _ /\ _ ==> _`
        (qspecl_then
          [`mk_inst (sa.cs_next_id + (if has_rb then 1 else 0) + LENGTH params)
             RETPC_PARAM [Lit (n2w ((if has_rb then 1 else 0) + LENGTH params))]
             [STRING #"%" (toString
               (sa.cs_next_var + (if has_rb then 1 else 0) + LENGTH params))]`,
           `n2w ((if has_rb then 1 else 0) + LENGTH params)`,
           `STRING #"%" (toString
              (sa.cs_next_var + (if has_rb then 1 else 0) + LENGTH params))`]
           mp_tac) >>
      qpat_assum `emitted_insts sa sb = _` (fn code_th =>
        qpat_assum `rpc = _` (fn rpc_th =>
          simp_tac (srw_ss()) [code_th, rpc_th, mk_inst_def, op_prov_def]))) >>
  gen_tac >> strip_tac >>
  `i < dimword (:256)` by (Cases_on `has_rb` >> gvs[] >> decide_tac) >>
  `MEM (mk_inst (sa.cs_next_id + i) PARAM [Lit (n2w i)]
          [STRING #"%" (toString (sa.cs_next_var + i))]) (emitted_insts sa sb)` by
    (simp[MEM_GENLIST] >> disj1_tac >> qexists_tac `i` >>
     gvs[arithmeticTheory.ADD_COMM]) >>
  qpat_assum `!inst idx out. MEM inst _ /\ _ ==> _`
    (qspecl_then
      [`mk_inst (sa.cs_next_id + i) PARAM [Lit (n2w i)]
         [STRING #"%" (toString (sa.cs_next_var + i))]`, `n2w i`,
       `STRING #"%" (toString (sa.cs_next_var + i))`] mp_tac) >>
  qpat_assum `MEM (mk_inst _ PARAM _ _) (emitted_insts sa sb)` (fn mem_th =>
    qpat_assum `i < dimword (:256)` (fn bound_th =>
      simp_tac (srw_ss()) [mem_th, bound_th, mk_inst_def, wordsTheory.w2n_n2w]))
QED

Theorem internal_capture_seq_origin_ptr_path:
  EVERY (\inst.
    MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
    ?idx out. inst.inst_operands = [Lit idx] /\
              inst.inst_outputs = [out]) code /\
  ~s.vs_halted /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = OK t /\
  (!D. inst_seq_ptr D lo ctx func PG G tn code s G' tn') ==>
  !D explicit.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code), G', tn')
Proof
  strip_tac >> rpt gen_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = []` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> rpt strip_tac >>
     qpat_x_assum `!inst. MEM inst code ==> _`
       (drule_then strip_assume_tac) >>
     fs[MEM, is_terminator_def]) >>
  mp_tac (Q.INST [`D` |-> `D`, `explicit` |-> `explicit`]
    (Q.SPECL [`code`, `s`, `t`, `G`, `tn`, `G'`, `tn'`, `ctx`, `func`, `bb`]
      run_inst_seq_gas_origin_ptr_path)) >>
  simp[] >> disch_then irule >> simp[] >>
  irule run_inst_seq_mem_ok_every >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!inst. MEM inst code ==> _ /\ ?idx out. _`
    (qspec_then `i` mp_tac) >> simp[] >>
  simp[MEM] >> rpt strip_tac >>
  simp[inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Theorem internal_capture_origin_ptr_path:
  EVERY (\inst.
    MEM inst.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
    ?idx out. inst.inst_operands = [Lit idx] /\
              inst.inst_outputs = [out]) code /\
  ~s.vs_halted /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  run_inst_seq code s = OK t ==>
  ?G' tn'. !D explicit.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code), G', tn')
Proof
  strip_tac >> drule_all internal_capture_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `tn`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >>
  irule internal_capture_seq_origin_ptr_path >> simp[] >> metis_tac[]
QED

(* This starts after gas_invoke_entry's initial PHIs. The package's
   physical prefix contains no PHI, so it threads the supplied ghost once. *)
Theorem compile_internal_entry_prefix_joint:
  compile_internal_entry_prefix cenv params has_rb sa =
    ((ce,caps,rpc),sb) /\
  fresh_vars_wrt sa s /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params /\
  LENGTH s.vs_params < dimword (:256) /\
  ~s.vs_halted /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn' x.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    t = s with vs_vars := t.vs_vars /\ fresh_vars_wrt sb t /\
    rpc = Var x /\ not_fresh_at sb x /\
    lookup_var x t = SOME s.vs_return_pc_token /\
    (!i. i < LENGTH params ==>
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at sb p /\
          lookup_var p t =
            SOME (EL ((if has_rb then 1 else 0) + i) s.vs_params)) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
    !D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      !explicit.
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) []
          (OK (t with vs_inst_idx :=
                 s.vs_inst_idx + LENGTH (emitted_insts sa sb)), G', tn')
Proof
  strip_tac >> drule_all compile_internal_entry_prefix_run >> strip_tac >>
  drule compile_internal_entry_prefix_capture_code >> strip_tac >>
  drule_all internal_capture_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `G`, `tn`] strip_assume_tac) >>
  drule_all internal_capture_seq_origin_ptr_path >> strip_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`, `x`] >> simp[]
QED

Theorem compile_internal_entry_prefix_origin_ptr:
  compile_internal_entry_prefix cenv params has_rb sa =
    ((ce,caps,rpc),sb) /\
  fresh_vars_wrt sa s /\
  (if has_rb then 1 else 0) + LENGTH params <= LENGTH s.vs_params /\
  LENGTH s.vs_params < dimword (:256) /\
  ~s.vs_halted /\ allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn' x.
    t = s with vs_vars := t.vs_vars /\ fresh_vars_wrt sb t /\
    rpc = Var x /\ not_fresh_at sb x /\
    lookup_var x t = SOME s.vs_return_pc_token /\
    (!i. i < LENGTH params ==>
      ?p. SND (SND (EL i caps)) = Var p /\ not_fresh_at sb p /\
          lookup_var p t =
            SOME (EL ((if has_rb then 1 else 0) + i) s.vs_params)) /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
    !D explicit.
      gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) []
        (OK (t with vs_inst_idx :=
               s.vs_inst_idx + LENGTH (emitted_insts sa sb)), G', tn')
Proof
  strip_tac >> drule_all compile_internal_entry_prefix_joint >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`t`, `G'`, `tn'`, `x`] >> simp[]
QED

Theorem compile_internal_fixed_region_joint:
  compile_fixed_region_with_id region_size sa = ((id,buf),sb) /\
  fresh_vars_wrt sa s /\ ~s.vs_halted /\ allocas_from lo s /\
  ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand buf.buf_operand t = SOME 0w /\ fresh_vars_wrt sb t /\
    t = s with vs_vars := t.vs_vars /\
    op_prov G' buf.buf_operand = NONE /\ op_taint tn' buf.buf_operand = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    !D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s G' tn' /\
      !explicit.
        gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s,G,tn) []
          (OK (t with vs_inst_idx :=
                 s.vs_inst_idx + LENGTH (emitted_insts sa sb)), G', tn')
Proof
  strip_tac >> drule_all compile_fixed_region_zero_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK t` >>
  drule contextTheory.compile_fixed_region_with_id_result >> strip_tac >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ASSIGN [Lit 0w] [out]` >>
  `inst.inst_opcode = ASSIGN` by simp[Abbr `inst`, mk_inst_def] >>
  `emitted_insts sa sb = [inst]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
         Abbr `inst`, Abbr `out`] >>
  `step_inst_base inst s = OK t` by
    (Cases_on `step_inst_base inst s` >> gvs[run_inst_seq_def]) >>
  mp_tac (Q.INST [`inst` |-> `inst`, `idx` |-> `0w`, `out` |-> `out`,
    `s` |-> `s`, `u` |-> `t`, `tn` |-> `tn`, `PG` |-> `PG`, `G` |-> `G`]
    (SPEC_ALL internal_capture_step_ghost)) >>
  (impl_tac >- simp[Abbr `inst`, mk_inst_def]) >> strip_tac >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s
     (set_prov G [out] NONE) (tn with t_var := tn.t_var |+ (out,{}))` by
    (gen_tac >> simp[inst_seq_ptr_def] >>
     irule internal_capture_inst_ptr >> simp[Abbr `inst`, mk_inst_def]) >>
  `EVERY (\i. MEM i.inst_opcode [PARAM; RETPC_PARAM; ASSIGN] /\
      ?idx x. i.inst_operands = [Lit idx] /\ i.inst_outputs = [x])
      (emitted_insts sa sb)` by simp[Abbr `inst`, mk_inst_def] >>
  drule_all internal_capture_seq_origin_ptr_path >> strip_tac >>
  qexistsl_tac [`t`, `set_prov G [out] NONE`,
    `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[Abbr `out`, op_prov_def, op_taint_def, set_prov_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
