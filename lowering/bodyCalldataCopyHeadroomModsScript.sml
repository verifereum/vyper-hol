(* Copy the transaction calldata using the headroom of the reached entry. *)
Theory bodyCalldataCopyHeadroomMods
Ancestors
  bodyFullRawCallCalldataCopy bodyFullDynamicBuffer bodyFullRawCallCallOrigin
  dallocaCalldata bodyFullIfExpReach bodyPtrBytestringBuiltinsCalldataCopy
  bodyPtrEnvBuiltinsEdges fragGasSeqPtr fragGasOriginPtr fragGasOriginPtrLoop
  fragExec ptrSafetyTransport compileEnv emitHelper emitHelperProps venomInst
  venomExecSemantics venomState words finite_map pred_set list rich_list
  memSafeRun unitTransformDefs codegenRel contextCodegenRel memLocDefs
  ptrSafeRun ptrDiscipline memoryReadProps venomMemProps decoderGhostFramePtr

Theorem calldata_copy_from_headroom:
  compile_msg_data_to_memory sa = ((dp,dl),sb) /\
  fn_has_code sa sb func /\ MEM func ctx.ctx_functions /\ ctx_has_dalloca ctx /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst v. contextRawReachable$frag_reachable ctx func s fn inst v ==>
     dalloca_fmp_headroom inst v) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ allocas_below_fmp s /\
  w2n s.vs_initial_fmp <= w2n s.vs_fmp /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t G' tn' p.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    dp = Var p /\ eval_operand dp t = SOME s.vs_fmp /\
    eval_operand dl t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    ptr_covers G' tn' p t (LENGTH s.vs_call_ctx.cc_calldata) /\
    op_taint tn' dl = {} /\ op_taint tn' dp = {} /\ op_prov G' dl = NONE /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata /\
    w2n t.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata) /\
    t.vs_memory =
      (write_memory_with_expansion (w2n s.vs_fmp) s.vs_call_ctx.cc_calldata s).vs_memory /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
              vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s /\
    tn'.t_mem =
      (tn.t_mem UNION {i | w2n s.vs_fmp <= i /\ i < w2n t.vs_fmp})
        DIFF {i | w2n s.vs_fmp <= i /\
                    i < w2n s.vs_fmp + LENGTH s.vs_call_ctx.cc_calldata} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ allocas_below_fmp t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_memory_placement >> strip_tac >>
  drule calldata_memory_insts >> strip_tac >>
  qabbrev_tac `szreg = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `ptrreg = "%" ++ toString (sa.cs_next_var + 1)` >>
  qabbrev_tac `n = LENGTH s.vs_call_ctx.cc_calldata` >>
  qabbrev_tac `size_inst = mk_inst sa.cs_next_id CALLDATASIZE [] [szreg]` >>
  qabbrev_tac `alloc_inst = mk_inst (sa.cs_next_id+1) DALLOCA [Var szreg] [ptrreg]` >>
  qabbrev_tac `copy_inst = mk_inst (sa.cs_next_id+2) CALLDATACOPY
      [Var ptrreg;Lit 0w;Var szreg] []` >>
  `emitted_insts sa sb = [size_inst;alloc_inst;copy_inst]` by
    simp[Abbr `size_inst`, Abbr `alloc_inst`, Abbr `copy_inst`] >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME size_inst /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME alloc_inst /\
    get_instruction bb (SUC (SUC s.vs_inst_idx)) = SOME copy_inst` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `[size_inst;alloc_inst;copy_inst]` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `bb` strip_assume_tac) >> qexists `bb` >> simp[] >>
     qpat_assum `!i:num. _ ==> get_instruction _ _ = _` (fn th =>
       map_every (fn i => qspec_then i (assume_tac o SIMP_RULE (srw_ss()) []) th)
         [`0`,`1`,`2`]) >>
     simp[arithmeticTheory.ADD1] >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
       once_rewrite_tac [arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC]) >>
  qabbrev_tac `v = update_var szreg (n2w n) s` >>
  qabbrev_tac `s1 = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G size_inst v` >>
  qabbrev_tac `tn1 = step_taint size_inst s v tn` >>
  `step_inst_base size_inst s = OK v` by
    simp[Abbr `size_inst`, Abbr `v`, Abbr `n`, mk_inst_def,
         step_inst_base_opcode_eqs, exec_read0_def, bind_outputs_def] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK s1,G1,tn1)` by
    (rpt gen_tac >>
     `ptr_inst_ok D lo 0 ctx func G tn size_inst s` by
       (simp[Abbr `size_inst`] >> irule ptr_inst_ok_scalar_builtin_at >> simp[]) >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK s1,G1,tn1)` by
       (mp_tac (Q.INST [`i` |-> `size_inst`, `u` |-> `v`] straight_line_origin_ptr_edge) >>
        impl_tac >-
          (simp[inst_mem_below_frontier_def, Abbr `size_inst`, mk_inst_def,
                is_terminator_def, inst_dload_in_section_def,
                source_memory_read_ranges_def, source_memory_write_ranges_def,
                dalloca_no_wrap_non_dalloca] >> fs[mk_inst_def]) >>
        simp[Abbr `size_inst`, Abbr `s1`, Abbr `G1`, Abbr `tn1`, mk_inst_def]) >>
     drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `s1`, Abbr `v`]) >>
  suspend "allocate"
QED

Resume calldata_copy_from_headroom[allocate]:
  `eval_operand (Var szreg) s1 = SOME (n2w n) /\
   allocas_from lo s1 /\ allocas_below_fmp s1 /\ ~s1.vs_halted /\
   lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s1.vs_inst_idx = SOME alloc_inst` by
    (simp[Abbr `s1`, Abbr `v`, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
          update_var_def, allocas_from_def, allocas_below_fmp_def] >>
     qpat_assum `s.vs_inst_idx = _` (fn pc =>
       qpat_assum `get_instruction bb (SUC s.vs_inst_idx) = _`
         (ACCEPT_TAC o REWRITE_RULE [pc]))) >>
  `op_taint tn1 (Var szreg) = {}` by
    (simp[Abbr `tn1`, Abbr `size_inst`] >>
     irule scalar_builtin_output_clean >> simp[]) >>
  `alloc_inst.inst_opcode = DALLOCA /\ alloc_inst.inst_operands = [Var szreg] /\
   alloc_inst.inst_outputs = [ptrreg]` by simp[Abbr `alloc_inst`, mk_inst_def] >>
  `contextRawReachable$frag_reachable ctx func s1 func alloc_inst s1` by
    (irule contextRawReachableTheory.frag_reachable_start >>
     drule_all contextCodegenRelPropsTheory.lookup_instruction_active >> simp[]) >>
  (* Instantiate only the size-edge path, never a prefix before s. *)
  `dalloca_fmp_headroom alloc_inst s1` by
    (qpat_assum `!D explicit. gas_origin_ptr_path (D,_,explicit,_,_,_)
         (s,G,tn) [] (OK s1,G1,tn1)`
       (qspecl_then [`ARB`,`{}`] assume_tac) >>
     drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `w2n s1.vs_fmp + venomLayout$ceil32 (w2n (n2w n : bytes32)) < dimword (:256)` by
    (qpat_x_assum `dalloca_fmp_headroom alloc_inst s1` mp_tac >>
     simp[dalloca_fmp_headroom_def, Abbr `s1`, Abbr `v`, update_var_def,
          w2n_n2w, Abbr `n`, arithmeticTheory.MAX_DEF] >> rw[] >> decide_tac) >>
  drule_all (Q.INST [`s` |-> `s1`, `tn` |-> `tn1`] dalloca_origin_region_exact) >>
  disch_then (qspecl_then [`PG`,`G1`]
    (qx_choose_then `s2` (qx_choose_then `G2`
      (qx_choose_then `tn2` (map_every assume_tac o CONJUNCTS))))) >>
  `ptrreg <> szreg` by simp[Abbr `ptrreg`, Abbr `szreg`] >>
  `lookup_var szreg s1 = SOME (n2w n)` by
    simp[Abbr `s1`, Abbr `v`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Var ptrreg) s2 = SOME s.vs_fmp` by
    (qpat_assum `lookup_var ptrreg s2 = _` mp_tac >>
     simp[Abbr `s1`, Abbr `v`, eval_operand_def, update_var_def]) >>
  `eval_operand (Var szreg) s2 = SOME (n2w n) /\ op_taint tn2 (Var szreg) = {}` by
    (qpat_assum `!x. x <> ptrreg ==> _` (qspec_then `szreg` mp_tac) >>
     impl_tac >- metis_tac[] >> simp[eval_operand_def]) >>
  `w2n (n2w n : bytes32) = n` by simp[w2n_n2w] >>
  `s2.vs_call_ctx = s.vs_call_ctx /\ s2.vs_initial_fmp = s.vs_initial_fmp /\
    w2n s2.vs_fmp = w2n s.vs_fmp + venomLayout$ceil32 n /\
    ptr_covers G2 tn2 ptrreg s2 n` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ptr_covers G2 tn2 ptrreg s2 (w2n (n2w n : bytes32))`,
        `w2n s2.vs_fmp = w2n s1.vs_fmp + _`, `s2.vs_call_ctx = s1.vs_call_ctx`,
        `s2.vs_initial_fmp = s1.vs_initial_fmp`] >>
     qpat_assum `w2n (n2w n : bytes32) = n` mp_tac >>
     simp[NoAsms,Abbr `s1`,Abbr `v`,update_var_def] >> metis_tac[]) >>
  suspend "copy"
QED

Resume calldata_copy_from_headroom[copy]:
  qabbrev_tac `u = write_memory_with_expansion (w2n s.vs_fmp) s.vs_call_ctx.cc_calldata s2` >>
  `step_inst_base copy_inst s2 = OK u` by
    (simp[Abbr `u`, Abbr `copy_inst`, GSYM step_inst_non_invoke, mk_inst_def] >>
     qspecl_then [`Var ptrreg`,`s2`,`s.vs_fmp`,`Lit 0w`,`0w`,
                 `Var szreg`,`n2w n`,`0`,`ctx`,`sa.cs_next_id+2`]
       mp_tac calldatacopy_step >>
     simp[eval_operand_def, step_inst_non_invoke, mk_inst_def, w2n_n2w,
          TAKE_APPEND1, Abbr `n`]) >>
  `allocas_from lo s2` by
    (rewrite_tac[allocas_from_def] >>
     qpat_assum `s2.vs_allocas = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `allocas_from lo s1` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `lookup_block s2.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s2.vs_inst_idx = SOME copy_inst` by
    (simp[Abbr `s1`, Abbr `v`, update_var_def] >>
     qpat_assum `s.vs_inst_idx = _` (fn pc =>
       qpat_assum `get_instruction bb (SUC (SUC s.vs_inst_idx)) = _`
         (ACCEPT_TAC o REWRITE_RULE [pc]))) >>
  `source_memory_read_ranges copy_inst s2 = [] /\
    source_memory_write_ranges copy_inst s2 = [(w2n s.vs_fmp,n)]` by
    (qpat_assum `eval_operand (Var ptrreg) s2 = _` mp_tac >>
     qpat_assum `eval_operand (Var szreg) s2 = _` mp_tac >>
     qpat_assum `w2n (n2w n : bytes32) = n` mp_tac >>
     simp[NoAsms, Abbr `copy_inst`, mk_inst_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def, sized_source_write_range_def, eval_operand_def] >>
     rpt strip_tac >> simp[]) >>
  `mem_safe_step 0 ctx copy_inst s2` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`source_memory_read_ranges copy_inst s2 = _`, `source_memory_write_ranges copy_inst s2 = _`,
        `w2n s2.vs_fmp = _`, `s2.vs_initial_fmp = s.vs_initial_fmp`,
        `w2n s.vs_initial_fmp <= w2n s.vs_fmp`, `ctx_has_dalloca ctx`] >>
     simp[NoAsms, Abbr `copy_inst`, mem_safe_step_non_invoke, mk_inst_def,
          inst_dload_in_section_def, inst_mem_below_frontiers_def,
          dalloca_no_wrap_non_dalloca] >>
     rpt strip_tac >> disj2_tac >>
     simp[venomLayoutTheory.ceil32_ge]) >>
  `step_prov PG G2 copy_inst u = G2 /\
    step_taint copy_inst s2 u tn2 = tn2 with t_mem :=
      tn2.t_mem DIFF {i | w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + n}` by
    (simp[Abbr `copy_inst`, calldatacopy_step_prov] >>
     simp[Abbr `u`] >>
     qspecl_then [`Var ptrreg`,`Lit 0w`,`Var szreg`,`s2`,`s.vs_fmp`,`0w`,`n2w n`,
       `sa.cs_next_id+2`,`tn2`,`s.vs_call_ctx.cc_calldata`] mp_tac calldatacopy_step_taint >>
     simp[eval_operand_def, w2n_n2w]) >>
  qexistsl [`u with vs_inst_idx := SUC s2.vs_inst_idx`, `G2`,
     `step_taint copy_inst s2 u tn2`, `ptrreg`] >>
  conj_tac >- suspend "path" >>
  suspend "post"
QED

Resume calldata_copy_from_headroom[path]:
  rpt gen_tac >>
  `ptr_inst_ok D lo 0 ctx func G2 tn2 copy_inst s2` by
    (irule ptr_inst_ok_lower_bound_transport >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `0` >> simp_tac bool_ss [arithmeticTheory.ZERO_LESS_EQ] >>
     simp[NoAsms, Abbr `copy_inst`] >>
     irule ptr_inst_ok_calldatacopy_operand >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`op_taint tn2 (Var szreg) = {}`, `allocas_below_fmp s2`,
        `ptr_covers G2 tn2 ptrreg s2 n`, `w2n (n2w n : bytes32) = n`,
        `eval_operand (Var szreg) s2 = _`] >>
     simp[NoAsms, op_taint_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) []
      (OK (u with vs_inst_idx := SUC s2.vs_inst_idx),G2,step_taint copy_inst s2 u tn2)` by
    (mp_tac (Q.INST [`i` |-> `copy_inst`, `s` |-> `s2`, `G` |-> `G2`,
       `tn` |-> `tn2`] non_gas_mem_safe_origin_ptr_edge) >>
     impl_tac >- (rpt conj_tac >>
       FIRST [first_assum ACCEPT_TAC, simp[Abbr `copy_inst`, mk_inst_def, is_terminator_def]]) >>
     simp[Abbr `copy_inst`, mk_inst_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s2,G2,tn2) []
      (OK (u with vs_inst_idx := SUC s2.vs_inst_idx),G2,step_taint copy_inst s2 u tn2)` by
    (drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >>
     simp[Abbr `u`, write_memory_with_expansion_def]) >>
  irule gas_origin_ptr_path_trans >> qexistsl [`G1`,`s1`,`tn1`] >> conj_tac
  >- (qpat_assum `!D explicit. gas_origin_ptr_path (D,_,explicit,_,_,_)
        (s,G,tn) [] (OK s1,G1,tn1)` (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  irule gas_origin_ptr_path_trans >> qexistsl [`G2`,`s2`,`tn2`] >> conj_tac
  >- (qpat_assum `!D explicit. gas_origin_ptr_path (D,_,explicit,_,_,_)
        (s1,G1,tn1) [] (OK s2,G2,tn2)` (qspecl_then [`D`,`explicit`] ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED

Resume calldata_copy_from_headroom[post]:
  qabbrev_tac `t = u with vs_inst_idx := SUC s2.vs_inst_idx` >>
  qabbrev_tac `tt = step_taint copy_inst s2 u tn2` >>
  `(!x. lookup_var x t = lookup_var x s2) /\
    t.vs_current_bb = s2.vs_current_bb /\ ~t.vs_halted /\
    t.vs_inst_idx = SUC s2.vs_inst_idx /\
    w2n t.vs_fmp = w2n s2.vs_fmp /\ allocas_below_fmp t` by
    (simp[NoAsms, Abbr `t`, Abbr `u`, write_memory_with_expansion_def,
          lookup_var_def, allocas_below_fmp_def] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `allocas_below_fmp s2` (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])) >>
  `!x. op_taint tt (Var x) = op_taint tn2 (Var x)` by
    (qpat_assum `tt = tn2 with t_mem := _`
       (fn th => simp[NoAsms, th, op_taint_def])) >>
  `ptr_covers G2 tt ptrreg t n` by
    (irule ptr_covers_frame >> qexistsl [`G2`,`s2`,`tn2`] >> simp[]) >>
  `t.vs_memory =
    (write_memory_with_expansion (w2n s.vs_fmp) s.vs_call_ctx.cc_calldata s).vs_memory` by
    (qpat_assum `s2.vs_memory = s1.vs_memory` mp_tac >>
     simp[NoAsms, Abbr `t`, Abbr `u`, Abbr `s1`, Abbr `v`,
          write_memory_with_expansion_def, update_var_def] >>
     disch_then (fn th => simp[NoAsms, th])) >>
  `(t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx;
        vs_memory := s.vs_memory; vs_fmp := s.vs_fmp|>) = s` by
    (simp[NoAsms, Abbr `t`, Abbr `u`, write_memory_with_expansion_def] >>
     qpat_assum `s2 = _ with vs_inst_idx := _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[NoAsms, Abbr `s1`, Abbr `v`, update_var_def]) >>
  `read_memory (w2n s.vs_fmp) n t = s.vs_call_ctx.cc_calldata` by
    (qpat_assum `t.vs_memory = _` mp_tac >>
     simp[NoAsms, read_memory_eq_mem_bytes_at,
          valueEncodingPropsTheory.write_memory_mem_bytes_at_same, Abbr `n`]) >>
  `t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`t.vs_current_bb = s2.vs_current_bb`, `t.vs_inst_idx = SUC s2.vs_inst_idx`,
        `s2.vs_current_bb = s1.vs_current_bb`, `s2.vs_inst_idx = SUC s1.vs_inst_idx`,
        `s.vs_current_bb = sa.cs_current_bb`, `s.vs_inst_idx = LENGTH sa.cs_current_insts`,
        `sb.cs_current_bb = sa.cs_current_bb`,
        `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb`,
        `emitted_insts sa sb = [size_inst;alloc_inst;copy_inst]`] >>
     simp[NoAsms, Abbr `s1`, Abbr `v`, update_var_def, arithmeticTheory.ADD1] >> decide_tac) >>
  suspend "ghost"
QED

Resume calldata_copy_from_headroom[ghost]:
  `tn1.t_mem = tn.t_mem` by
    (simp[Abbr `tn1`] >> irule step_taint_no_memory_effect >>
     simp[Abbr `size_inst`, Abbr `v`, source_memory_write_ranges_def,
          written_taint_def, mk_inst_def, update_var_def]) >>
  `tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm` by
    (simp[Abbr `tn1`] >> irule step_taint_nonmemory_frame >>
     simp[Abbr `size_inst`, mk_inst_def]) >>
  `op_prov G1 (Var szreg) = NONE` by
    simp[Abbr `G1`, Abbr `size_inst`, scalar_builtin_output_no_prov] >>
  `op_prov G2 (Var szreg) = NONE` by
    (qpat_assum `!x. x <> ptrreg ==> _` (qspec_then `szreg` mp_tac) >>
     impl_tac >- metis_tac[] >>
     qpat_assum `op_prov G1 (Var szreg) = NONE`
       (fn th => simp_tac (srw_ss()) [op_prov_def, SIMP_RULE (srw_ss()) [op_prov_def] th])) >>
  `!x. not_fresh_at sa x ==> x <> szreg /\ x <> ptrreg` by
    (simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `szreg`, Abbr `ptrreg`] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tt (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> x <> szreg /\ x <> ptrreg`
       (drule_then strip_assume_tac) >>
     qpat_assum `!x. x <> ptrreg ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!x. lookup_var x t = lookup_var x s2`
       (qspec_then `x` (fn th => PURE_REWRITE_TAC [th])) >>
     qpat_assum `!x. op_taint tt (Var x) = op_taint tn2 (Var x)`
       (qspec_then `x` (fn th => PURE_REWRITE_TAC [th])) >>
     simp[Abbr `G1`, Abbr `tn1`, Abbr `size_inst`, Abbr `s1`, Abbr `v`,
          step_taint_other_output, step_prov_other_output, mk_inst_def, lookup_var_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  `tt.t_mem = (tn.t_mem UNION {i | w2n s.vs_fmp <= i /\ i < w2n t.vs_fmp})
       DIFF {i | w2n s.vs_fmp <= i /\ i < w2n s.vs_fmp + n} /\
    tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm` by
    (qpat_assum `tt = tn2 with t_mem := _`
       (fn th => simp[NoAsms, th]) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`tn2.t_mem = _`, `tn1.t_mem = _`, `w2n t.vs_fmp = w2n s2.vs_fmp`,
        `tn2.t_stor = _`, `tn2.t_trans = _`, `tn2.t_imm = _`,
        `tn1.t_stor = _`, `tn1.t_trans = _`, `tn1.t_imm = _`] >>
     simp[NoAsms, Abbr `s1`, Abbr `v`, update_var_def]) >>
  suspend "finish"
QED

Resume calldata_copy_from_headroom[finish]:
  map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC[th]))
    [`dp = Var ptrreg`, `dl = Var szreg`] >>
  qpat_assum `Abbrev (n = _)`
    (fn th => PURE_REWRITE_TAC[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `w2n t.vs_fmp = w2n s2.vs_fmp`
         (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `!x. op_taint tt (Var x) = op_taint tn2 (Var x)`
         (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `!x. lookup_var x t = lookup_var x s2`
    (fn th => simp[NoAsms, eval_operand_def, th]) >>
  first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [eval_operand_def])
QED

Finalise calldata_copy_from_headroom
