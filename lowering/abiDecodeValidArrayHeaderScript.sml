(* Joint execution of the bounded memory array prefix and count header. *)
Theory abiDecodeValidArrayHeader
Ancestors
  abiDecoderArrayHeader abiDecodePtrMemberFrame decoderNavigationPtr
  bodyFullAbiDecodeClampMemory[qualified,ignore_grammar]
  bodyPtrBopHashSuffix bodyFullUnwrapRun wordLoadStorePtr valueCopy
  allocaFootprint ptrSafetyTransport reasonCopySourcePtr fragExecPtr
  emitHelperProps fragExec venomExecSemantics venomState venomInst venomMemDefs
  compileEnv loweringStateRelDefs bodyPtrDefs ptrDiscipline fragExecMem fragGasSeqPtr
  exprLoweringProps decoderGhostFramePtr fragGasOriginPtr
  finite_map numposrep pred_set words list rich_list arithmetic
  logAbiPrefixPtr bodyPtrIfExpBytesCounted
  bodyPtrIfExpBytesFrame exprSimMapKey bodyFieldMemoryProps loweringShapeRules
  bodyPtrBopScalarSeq freshWrites ghostPcTransportPtr logInstSeqPtr
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderBytesBound
  abiDecoderGuard abiDecoderGuards abiDecoderRange abiEncoder emitHelper
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome abiMalformedBulkArray
  abiDecoderAbortReentry abiDecoderReentry abiDecoderVarSequence abiDecoderContract
  fragGasOriginPtrDead instIdxIndep
  fragGasCopySeqLiftProps

Theorem abi_decode_array_header_success_joint:
  abi_decode_array_header (Var output) (Var addr) MLOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa output /\ not_fresh_at sa addr /\
  lookup_var output s = SOME (n2w d) /\
  abi_decode_ptr_window G tn s addr (n2w a) 32 /\
  ptr_covers G tn output s cap /\ 32 <= cap /\
  a+32 < dimword (:256) /\ d+cap < dimword (:256) /\
  a+32 <= s.vs_alloca_next /\ d+cap <= s.vs_alloca_next /\
  allocas_from lo s ==>
  ?G' tn'.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    ptr_covers G' tn' output u cap /\
    abi_decode_ptr_window G' tn' u output (n2w d) 32 /\
    op_prov G' cnt = NONE /\ op_taint tn' cnt = {} /\
    eval_operand cnt u = SOME (mload a s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo u
Proof
  strip_tac >>
  `?middle. emit_op MLOAD [Var addr] sa = (cnt,middle) /\
     emit_void MSTORE [Var output;cnt] middle = ((),sb)` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `inst_extends sa middle /\ inst_extends middle sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `same_blocks sa middle /\ same_blocks middle sb` by
    metis_tac[emit_op_extends, emit_void_extends] >>
  `cs_extends sa middle /\ cs_extends middle sb` by
    (conj_tac >> irule cs_extends_same_block >>
     fs[inst_extends_def, same_blocks_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `fn_has_code sa middle func /\ fn_has_code middle sb func` by
    metis_tac[fn_has_code_split] >>
  `emitted_insts sa sb = emitted_insts sa middle ++ emitted_insts middle sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?loaded. run_inst_seq (emitted_insts sa middle) s = OK loaded /\
     run_inst_seq (emitted_insts middle sb) loaded = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK u` mp_tac >>
     qpat_assum `emitted_insts sa sb = _`
       (fn th => pure_rewrite_tac[th, bop_run_inst_seq_append_ok]) >> simp[]) >>
  `a < dimword (:256) /\ d < dimword (:256)` by decide_tac >>
  `lookup_var addr s = SOME (n2w a) /\ ptr_covers G tn addr s 32 /\
     (!i. w2n (n2w a:bytes32) <= i /\ i < w2n (n2w a:bytes32)+32 ==> i NOTIN tn.t_mem)` by
    fs[abi_decode_ptr_window_def] >>
  drule_all emit_mload_clean_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`ARB`, `ARB`, `ctx`, `PG`, `ARB`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!D lower ctx' func. _ ==> !fuel. ptr_safe_run _ _ _ _ _ _ _ _ _` kall_tac >>
  `loaded = update_var (STRING #"%" (toString sa.cs_next_var)) (mload a s) s` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa middle) s = OK loaded` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      exec_read1_def, eval_operand_def, w2n_n2w]) >>
  `output <> STRING #"%" (toString sa.cs_next_var)` by
    metis_tac[not_fresh_at_def, LESS_EQ_REFL] >>
  `lookup_var output loaded = SOME (n2w d) /\
   eval_operand cnt loaded = SOME (mload a s)` by
    simp[eval_operand_def, lookup_var_update_var] >>
  `u = mstore d (mload a s) loaded` by
    (qpat_x_assum `run_inst_seq (emitted_insts middle sb) loaded = OK u` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, lookup_var_update_var, w2n_n2w]) >>
  qabbrev_tac `prepared = loaded with vs_inst_idx := LENGTH middle.cs_current_insts` >>
  qabbrev_tac `inst = mk_inst middle.cs_next_id MSTORE [Var output;cnt] []` >>
  qabbrev_tac `stored = mstore d (mload a s) prepared` >>
  qabbrev_tac `tn2 = step_taint inst prepared stored tn1` >>
  `ptr_covers G1 tn1 output prepared cap /\
     lookup_var output prepared = SOME (n2w d) /\
     eval_operand cnt prepared = SOME (mload a s) /\
     prepared.vs_allocas = s.vs_allocas /\ prepared.vs_alloca_next = s.vs_alloca_next /\
     ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
     prepared.vs_inst_idx = LENGTH middle.cs_current_insts` by
    (conj_tac
     >- (irule ptr_covers_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
         simp[Abbr `prepared`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
         fs[lookup_var_def]) >>
     simp[Abbr `prepared`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     fs[same_blocks_def, lookup_var_def]) >>
  `step_prov PG G1 inst stored = G1 /\
     tn2.t_var = tn1.t_var /\ tn2.t_stor = tn1.t_stor /\
     tn2.t_trans = tn1.t_trans /\
     tn2.t_mem = tn1.t_mem DIFF {i | d <= i /\ i < d+32}` by
    (drule_at (Pat `lookup_var output prepared = _`) mstore_ghost_frame >>
     disch_then drule >>
     disch_then (qspecl_then [`PG`, `G1`, `tn1`, `middle.cs_next_id`] mp_tac) >>
     simp[Abbr `inst`, Abbr `stored`, Abbr `tn2`, w2n_n2w]) >>
  `tn2.t_imm = tn1.t_imm` by
    simp[Abbr `tn2`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `allocas_from lo prepared` by (fs[allocas_from_def] >> metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp prepared` by
    (`allocas_below_fmp prepared <=> allocas_below_fmp s` by
       simp[Abbr `prepared`, update_var_def, allocas_below_fmp_def] >>
     simp[]) >>
  `ptr_covers G1 tn1 output prepared 32` by metis_tac[ptr_covers_mono] >>
  `run_inst_seq (emitted_insts middle sb) prepared = OK stored` by
    (qpat_assum `emit_void MSTORE _ middle = _` (mp_then Any mp_tac emit_mstore_run) >>
     disch_then (qspecl_then [`prepared`, `n2w d`, `mload a s`] mp_tac) >>
     simp[Abbr `stored`, eval_operand_def, w2n_n2w]) >>
  `step_inst_base inst prepared = OK stored` by
    ((qpat_assum `run_inst_seq (emitted_insts middle sb) prepared = OK stored` mp_tac >>
     simp[run_inst_seq_def] >> Cases_on `step_inst_base inst prepared` >> simp[] >> (gvs[run_inst_seq_def]))) >>
  `inst.inst_opcode = MSTORE` by simp[Abbr `inst`, mk_inst_def] >>
  `run_inst_seq_mem_ok (emitted_insts middle sb) prepared` by
    (drule emit_mstore_mem_ok >> disch_then irule >>
     qexists_tac `n2w d` >> simp[eval_operand_def, w2n_n2w] >> decide_tac) >>
  `sb.cs_current_bb = middle.cs_current_bb` by fs[same_blocks_def] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (prepared,G1,tn1) [] (OK (stored with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn2)` by
    (rpt gen_tac >>
     `ptr_inst_ok D lo 0 ctx func G1 tn1 inst prepared` by
       ((irule (ptr_inst_ok_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >>
        simp[Abbr `inst`] >> irule ptr_inst_ok_mstore >> simp[] >> (metis_tac[Abbr `inst`, ptr_inst_ok_lower_bound_transport |> Q.INST [`lo0` |-> `0`], ptr_inst_ok_mstore]))) >>
     `inst_seq_ptr D lo ctx func PG G1 tn1 (emitted_insts middle sb) prepared G1 tn2` by
       simp[inst_seq_ptr_def, Abbr `tn2`] >>
     irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     simp[] >> qexists_tac `middle` >>
     simp[is_terminator_def, APPEND_EQ_CONS,
          memSafeRunTheory.dalloca_no_wrap_non_dalloca]) >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G1,tn2)` by
    (rpt gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK prepared,G1,tn1)` by
       (simp[Abbr `prepared`] >> first_x_assum irule >> simp[w2n_n2w]) >>
     `stored with vs_inst_idx := LENGTH sb.cs_current_insts =
        u with vs_inst_idx := LENGTH sb.cs_current_insts` by
       simp[Abbr `stored`, Abbr `prepared`, mstore_def, write_memory_with_expansion_def] >>
     metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  `u.vs_vars = loaded.vs_vars /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    simp[mstore_def, update_var_def] >>
  `!operand. op_taint tn2 operand = op_taint tn1 operand` by
    (Cases_on `operand` >> simp[op_taint_def]) >>
  `!x. lookup_var x u = lookup_var x loaded` by simp[lookup_var_def] >>
  `!operand. eval_operand operand u = eval_operand operand loaded` by
    (Cases_on `operand` >> simp[eval_operand_def]) >>
  `!x. lookup_var x u = lookup_var x prepared` by
    simp[Abbr `prepared`, lookup_var_def] >>
  `ptr_covers G1 tn2 output u cap /\ ptr_covers G1 tn2 output u 32` by
    (conj_tac >> irule ptr_covers_frame >>
     qexistsl_tac [`G1`, `prepared`, `tn1`] >> simp[]) >>
  qpat_x_assum `!x. lookup_var x u = lookup_var x prepared` kall_tac >>
  `abi_decode_ptr_window G1 tn2 u output (n2w d) 32` by
    (simp[abi_decode_ptr_window_def, w2n_n2w] >> rpt strip_tac >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     qpat_assum `u.vs_allocas = s.vs_allocas`
       (fn th => pure_rewrite_tac[allocas_from_def, th]) >>
     disch_then ACCEPT_TAC) >>
  qexistsl_tac [`G1`, `tn2`] >> simp[] >> rpt strip_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]
QED

Theorem abi_decode_array_position_load_cut[local]:
  emit_op ADD [Var source;pos] sa = (Var addr,sb) /\
  emit_op MLOAD [Var addr] sb = (Var cnt,sc) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ op_taint tn pos = {} /\
  not_fresh_at sa source /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?G2 tn2 u.
    run_inst_seq (emitted_insts sa sc) s = OK u /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sc) s G2 tn2 /\
    run_inst_seq_mem_ok (emitted_insts sa sc) s /\
    (u with vs_vars := s.vs_vars) = s /\
    abi_decode_ptr_window G2 tn2 u source (n2w B) L /\
    abi_decode_ptr_window G2 tn2 u addr (n2w (B+p)) 32 /\
    lookup_var cnt u = SOME (mload (B+p) s) /\
    op_prov G2 (Var cnt) = NONE /\ op_taint tn2 (Var cnt) = {} /\
    not_fresh_at sc addr /\ not_fresh_at sc cnt /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    tn2.t_mem = tn.t_mem /\ tn2.t_stor = tn.t_stor /\
    tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm
Proof
  strip_tac >>
  `B < dimword (:256) /\ B+p+32 < dimword (:256) /\
   B+p+32 <= s.vs_alloca_next` by decide_tac >>
  `lookup_var source s = SOME (n2w B) /\ ptr_covers G tn source s (p+32)` by
    (fs[abi_decode_ptr_window_def] >> metis_tac[ptr_covers_mono]) >>
  `w2n (n2w B:bytes32) + p < dimword (:256)` by simp[w2n_n2w] >>
  drule_all emit_addr_add_seq_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `v` strip_assume_tac)))) >>
  `eval_operand (Var source) s = SOME (n2w B)` by simp[eval_operand_def] >>
  drule_all emit_ADD_frame >>
  strip_tac >>
  `t = v` by fs[] >>
  qpat_x_assum `t = v` SUBST_ALL_TAC >>
  `v.vs_alloca_next = s.vs_alloca_next /\ v.vs_inst_idx = s.vs_inst_idx` by
    (qpat_assum `(v with vs_vars := s.vs_vars) = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `lookup_var addr v = SOME (n2w (B+p))` by simp[word_add_n2w] >>
  `!i. B <= i /\ i < B+L ==> i NOTIN tn.t_mem` by
    ((qpat_assum `abi_decode_ptr_window G tn s source _ _` mp_tac >>
     simp[abi_decode_ptr_window_def, w2n_n2w] >> (gvs[abi_decode_ptr_window_def, w2n_n2w]))) >>
  `abi_decode_ptr_window G1 tn1 v addr (n2w (B+p)) 32` by
    (simp[abi_decode_ptr_window_def, w2n_n2w, word_add_n2w] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!i. B <= i /\ _ ==> _` irule >> decide_tac) >>
  `sc.cs_next_var = sb.cs_next_var+1 /\ sb.cs_next_var = sa.cs_next_var+1 /\
   not_fresh_at sb addr /\ not_fresh_at sc cnt` by
    (imp_res_tac emit_op_facts >> gvs[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (simp[not_fresh_at_def] >> metis_tac[DECIDE ``a <= b ==> a <= b+1``]) >>
  `not_fresh_at sc addr` by
    (fs[not_fresh_at_def] >> metis_tac[DECIDE ``a <= b ==> a <= b+1``]) >>
  FIRST_ASSUM (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `inst_extends sa sb /\ inst_extends sb sc` by metis_tac[inst_extends_emit_op] >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `vpc = v with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sb)` >>
  `ptr_covers G1 tn1 addr vpc 32 /\ lookup_var addr vpc = SOME (n2w (B+p)) /\
   (!i. w2n (n2w (B+p):bytes32) <= i /\ i < w2n (n2w (B+p):bytes32)+32 ==>
       i NOTIN tn1.t_mem)` by
    fs[Abbr `vpc`, ptr_covers_inst_idx, lookup_var_def, abi_decode_ptr_window_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp vpc` by
    (`allocas_below_fmp vpc <=> allocas_below_fmp s` by
       (qpat_assum `(v with vs_vars := s.vs_vars) = s`
         (mp_tac o Q.AP_TERM `\z. allocas_below_fmp z`) >>
        simp[Abbr `vpc`, allocas_below_fmp_def]) >>
     simp[]) >>
  drule_all bodyPtrIfExpBytesCountedTheory.emit_mload_clean_seq_ptr >>
  disch_then (qspecl_then [`D`, `func`, `PG`]
    (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `upc` strip_assume_tac)))) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  qabbrev_tac `u = upc with vs_inst_idx := s.vs_inst_idx` >>
  `run_inst_seq (emitted_insts sa sc) s = OK u` by
    (qunabbrev_tac `u` >> qunabbrev_tac `vpc` >>
     drule_all run_inst_seq_append_advanced >> simp[]) >>
  `inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sc) s G2 tn2` by
    (qunabbrev_tac `vpc` >> drule_all bop_inst_seq_ptr_append >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule attr_add_prefix_mem_ok >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts sb sc) v` by
    (drule emit_mload_mem_ok >> disch_then irule >>
     qexists_tac `n2w (B+p)` >> simp[eval_operand_def, word_add_n2w, w2n_n2w] >>
     decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts sa sc) s` by
    (qpat_assum `emitted_insts sa sc = _ ++ _` (fn th => pure_rewrite_tac[th]) >>
     irule run_inst_seq_mem_ok_append >> pure_asm_rewrite_tac[] >>
     rpt strip_tac >> gvs[]) >>
  `(u with vs_vars := s.vs_vars) = s` by
    (qpat_assum `(v with vs_vars := s.vs_vars) = s` mp_tac >>
     qpat_assum `(upc with vs_vars := vpc.vs_vars) = vpc` mp_tac >>
     simp[Abbr `u`, Abbr `vpc`, venom_state_component_equality]) >>
  `!x. lookup_var x u = lookup_var x upc /\ lookup_var x vpc = lookup_var x v` by
    simp[Abbr `u`, Abbr `vpc`, lookup_var_def] >>
  `!x. not_fresh_at sb x ==> lookup_var x u = lookup_var x v /\
    FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (rpt strip_tac >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G2 x = FLOOKUP G x /\ op_taint tn2 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[]) >>
  `abi_decode_ptr_window G2 tn2 u source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     rpt strip_tac >> metis_tac[]) >>
  `abi_decode_ptr_window G2 tn2 u addr (n2w (B+p)) 32` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G1`, `v`, `tn1`] >>
     rpt strip_tac >> metis_tac[]) >>
  `lookup_var cnt u = SOME (mload (B+p) s)` by
    (qpat_assum `lookup_var cnt upc = SOME _` mp_tac >>
     simp[Abbr `u`, Abbr `vpc`, lookup_var_def, mload_def, w2n_n2w]) >>
  `EVERY (\i. i.inst_opcode <> ISTORE) (emitted_insts sa sc)` by
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[mk_inst_def]) >>
  `tn2.t_imm = tn.t_imm` by
    (drule_all inst_seq_ptr_immutable_frame >> simp[]) >>
  qexistsl_tac [`G2`, `tn2`, `u`] >> asm_rewrite_tac[]
QED

Theorem abi_decode_array_range_scalar[local]:
  compile_abi_decode_range_check src e hi sa = ((),sb) /\
  src IN A /\ e IN A /\ hi IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  (?B. bop_scalar_seq R A (emitted_insts sa sb) B) /\
  sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >>
  `!k. sa.cs_next_var <= k ==> STRING #"%" (toString k) NOTIN R` by
    (rpt strip_tac >>
     qpat_assum `!x. x IN R ==> not_fresh_at sa x`
       (drule_then (qspec_then `k` mp_tac o REWRITE_RULE[not_fresh_at_def])) >>
     simp[]) >>
  gvs[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
      emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, bop_scalar_seq_def, mk_inst_def]
QED

Theorem abi_decode_scalar_head_code[local]:
  abi_decode_bytes_head pos hi sa = (head,sb) /\ hi <> Lit 0w /\
  pos IN A /\ hi IN A /\ Lit 32w IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  (?C. bop_scalar_seq R A (emitted_insts sa sb) C /\ head IN C /\ A SUBSET C) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (?h. head = Var h /\ not_fresh_at sb h)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD [pos; Lit 32w] sa = (head,sm)` >>
  `bop_scalar_seq R A (emitted_insts sa sm) (head INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[pos; Lit 32w]`] >> simp[]) >>
  drule_then strip_assume_tac emit_op_facts >>
  `!x. x IN R ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  rename1 `compile_abi_decode_range_check pos head hi sm = ((),sb)` >>
  drule abi_decode_array_range_scalar >>
  disch_then (qspecl_then [`R`, `head INSERT A`] mp_tac) >> simp[] >>
  strip_tac >>
  `inst_extends sa sm /\ inst_extends sm sb` by
    metis_tac[inst_extends_emit_op, compile_abi_decode_range_check_shape] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `A SUBSET B /\ head IN B` by
    (drule bop_scalar_seq_available >> simp[SUBSET_DEF] >> metis_tac[]) >>
  conj_tac
  >- (qexists_tac `B` >> simp[] >> metis_tac[bop_scalar_seq_append]) >>
  irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]
QED

Theorem abi_decode_scalar_payload_code[local]:
  abi_decode_dynarray_payload_guard head cntop stride hi sa = ((),sb) /\
  hi <> Lit 0w /\ head IN A /\ cntop IN A /\ hi IN A /\ Lit (n2w stride) IN A /\
  (!x. x IN R ==> not_fresh_at sa x) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  (?C. bop_scalar_seq R A (emitted_insts sa sb) C)
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_dynarray_payload_guard _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_dynarray_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op MUL [cntop; Lit (n2w stride)] sa = (prod,sm)` >>
  rename1 `emit_op ADD [head;prod] sm = (e,se)` >>
  `bop_scalar_seq R A (emitted_insts sa sm) (prod INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`MUL`, `[cntop; Lit (n2w stride)]`] >> simp[]) >>
  `sm.cs_next_var = sa.cs_next_var+1 /\ se.cs_next_var = sm.cs_next_var+1` by
    metis_tac[emit_op_facts] >>
  `!x. x IN R ==> not_fresh_at sm x /\ not_fresh_at se x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `bop_scalar_seq R (prod INSERT A) (emitted_insts sm se) (e INSERT prod INSERT A)` by
    (irule bop_scalar_seq_emit_op >> simp[] >>
     qexistsl_tac [`ADD`, `[head;prod]`] >> simp[]) >>
  drule abi_decode_array_range_scalar >>
  disch_then (qspecl_then [`R`, `e INSERT prod INSERT A`] mp_tac) >> simp[] >>
  strip_tac >>
  `inst_extends sa sm /\ inst_extends sm se /\ inst_extends se sb` by
    metis_tac[inst_extends_emit_op, compile_abi_decode_range_check_shape] >>
  `inst_extends sm sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sm sb = emitted_insts sm se ++ emitted_insts se sb /\
   emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (rpt conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  qexists_tac `B` >> simp[] >> metis_tac[bop_scalar_seq_append]
QED

Theorem abi_decode_scalar_count_payload_code[local]:
  emit_op GT [cntop; Lit (n2w maxn)] sa = (bad,sm) /\
  emit_op ISZERO [bad] sm = (good,sn) /\
  emit_void ASSERT [good] sn = ((),se) /\
  abi_decode_dynarray_payload_guard head cntop stride hi se = ((),sb) /\
  hi <> Lit 0w /\ head IN A /\ cntop IN A /\ hi IN A /\
  (!w. Lit w IN A) /\ (!x. x IN R ==> not_fresh_at sa x) ==>
  sa.cs_next_var <= sb.cs_next_var /\ inst_extends sa sb /\
  (?C. bop_scalar_seq R A (emitted_insts sa sb) C)
Proof
  strip_tac >>
  `bop_scalar_seq R A (emitted_insts sa sn) (good INSERT bad INSERT A)` by
    (irule bop_scalar_seq_emit_iszero >> simp[] >>
     qexistsl_tac [`sm`, `GT`, `[cntop; Lit (n2w maxn)]`] >> simp[]) >>
  `bop_scalar_seq R (good INSERT bad INSERT A) (emitted_insts sn se)
     (good INSERT bad INSERT A)` by
    (irule bop_scalar_seq_emit_assert >> qexistsl_tac [`good`, `ASSERT`] >> simp[]) >>
  `inst_extends sa sm /\ inst_extends sm sn /\ inst_extends sn se /\
   inst_extends se sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void,
      abi_decode_dynarray_payload_guard_shape] >>
  `inst_extends sa sn /\ inst_extends sa se /\ inst_extends sa sb` by
    metis_tac[inst_extends_trans] >>
  `se.cs_next_var = sn.cs_next_var /\ sn.cs_next_var = sm.cs_next_var+1 /\
   sm.cs_next_var = sa.cs_next_var+1` by
    metis_tac[emit_op_facts, emitted_insts_emit_void] >>
  `!x. x IN R ==> not_fresh_at se x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule abi_decode_scalar_payload_code >>
  disch_then (qspecl_then [`R`, `good INSERT bad INSERT A`] mp_tac) >> simp[] >>
  strip_tac >>
  `emitted_insts sa se = emitted_insts sa sn ++ emitted_insts sn se /\
   emitted_insts sa sb = emitted_insts sa se ++ emitted_insts se sb` by
    (rpt conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[] >>
  qexists_tac `C` >> simp[] >> metis_tac[bop_scalar_seq_append]
QED

Theorem abi_decode_mload_prefix_opcodes[local]:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa =
    (addr,sb) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
    compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def,
    is_terminator_def]
QED

Theorem abi_decode_mload_prefix_cuts[local]:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa =
    (addr,sb) ==>
  ?head st1 ar st2 cnt st3 bad st4 good st5 st6.
    abi_decode_bytes_head pos hi sa = (head,st1) /\
    emit_op ADD [Var source;pos] st1 = (Var ar,st2) /\ addr = Var ar /\
    emit_op MLOAD [Var ar] st2 = (cnt,st3) /\
    emit_op GT [cnt;Lit (n2w maxn)] st3 = (bad,st4) /\
    emit_op ISZERO [bad] st4 = (good,st5) /\
    emit_void ASSERT [good] st5 = ((),st6) /\
    abi_decode_dynarray_payload_guard head cnt stride hi st6 = ((),sb) /\
    emitted_insts sa sb =
      emitted_insts sa st1 ++ emitted_insts st1 st3 ++ emitted_insts st3 sb /\
    st3.cs_next_var = st1.cs_next_var+2
Proof
  simp[abi_decode_dynarray_position_prefix_trace, compile_abi_dec_addr_def] >>
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac abi_decode_bytes_head_shape >>
  drule_then strip_assume_tac abi_decode_dynarray_payload_guard_shape >>
  imp_res_tac emit_op_facts >> gvs[] >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  rename1 `emit_op ADD _ st1 = (Var ar,st2)` >>
  rename1 `emit_op MLOAD _ st2 = (Var cnt,st3)` >>
  rename1 `emit_op GT _ st3 = (Var bad,st4)` >>
  rename1 `emit_op ISZERO _ st4 = (Var good,st5)` >>
  rename1 `emit_void ASSERT _ st5 = ((),st6)` >>
  `inst_extends st1 st3 /\ inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `inst_extends st3 st6 /\ inst_extends sa st3` by metis_tac[inst_extends_trans] >>
  `inst_extends st3 sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa st3 ++ emitted_insts st3 sb /\
   emitted_insts sa st3 = emitted_insts sa st1 ++ emitted_insts st1 st3` by
    (rpt conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  simp[APPEND_ASSOC]
QED

Theorem abi_decode_scalar_run_frame[local]:
  bop_scalar_seq R A code C /\ run_inst_seq code s = OK u /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?H th. inst_seq_ptr D 0 ctx func PG G tn code s H th /\
    run_inst_seq_mem_ok code s /\ u = s with vs_vars := u.vs_vars /\
    (!op. op IN C ==> op_prov H op = NONE /\ op_taint th op = {}) /\
    (!x. x IN R ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule_all bop_scalar_seq_run >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `run_inst_seq_mem_ok code s` by metis_tac[bodyFullAbiDecodeClampMemoryTheory.abi_decode_scalar_seq_mem_ok] >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  rpt strip_tac >> fs[lookup_var_def, op_taint_def]
QED

Theorem abi_decode_dynarray_position_prefix_fresh_ptr[local]:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa =
    (addr,sb) /\ run_inst_seq (emitted_insts sa sb) s = OK u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ hi <> Lit 0w /\
  not_fresh_at sa source /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p+32 <= L /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next ==>
  ?ar H th. addr = Var ar /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H th /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    abi_decode_ptr_window H th u source (n2w B) L /\
    abi_decode_ptr_window H th u ar (n2w (B+p)) 32 /\
    not_fresh_at sb ar /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm
Proof
  strip_tac >> drule_then strip_assume_tac abi_decode_mload_prefix_cuts >> gvs[] >>
  rename1 `emit_op ADD [Var source;pos] st1 = (Var ar,st2)` >>
  rename1 `emit_op MLOAD [Var ar] st2 = (cn,st3)` >>
  rename1 `abi_decode_bytes_head pos hi sa = (hd,st1)` >>
  qabbrev_tac `a = emitted_insts sa st1` >>
  qabbrev_tac `b = emitted_insts st1 st3` >>
  qabbrev_tac `c = emitted_insts st3 sb` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) a /\
   EVERY (\i. ~is_terminator i.inst_opcode) b /\
   EVERY (\i. ~is_terminator i.inst_opcode) c` by
    (drule abi_decode_mload_prefix_opcodes >> simp[EVERY_CONJ]) >>
  `?s1 s2. run_inst_seq a s = OK s1 /\ run_inst_seq b s1 = OK s2 /\
           run_inst_seq c s2 = OK u` by
    gvs[bodyPtrBopHashSuffixTheory.bop_run_inst_seq_append_ok] >>
  qabbrev_tac `R = {x | not_fresh_at sa x}` >>
  qabbrev_tac `A = {pos;hi} UNION IMAGE Lit UNIV` >>
  `?C. bop_scalar_seq R A a C /\ hd IN C /\ A SUBSET C /\
       sa.cs_next_var <= st1.cs_next_var /\
       ?h. hd = Var h /\ not_fresh_at st1 h` by
    (drule abi_decode_scalar_head_code >>
     disch_then (qspecl_then [`R`, `A`] mp_tac) >>
     simp[Abbr `R`, Abbr `A`, Abbr `a`] >> metis_tac[]) >>
  `!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}` by
    (simp[Abbr `A`, IN_IMAGE] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all abi_decode_scalar_run_frame >>
  disch_then (qspecl_then [`func`, `PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  suspend "load_and_tail"
QED

Resume abi_decode_dynarray_position_prefix_fresh_ptr[load_and_tail]:
  `!x. not_fresh_at sa x ==> not_fresh_at st1 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!x. not_fresh_at sa x ==> lookup_var x s1 = lookup_var x s /\
    FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)` by
    fs[Abbr `R`] >>
  `s1.vs_labels = s.vs_labels /\ s1.vs_alloca_next = s.vs_alloca_next` by
    fs[venom_state_component_equality] >>
  `eval_operand pos s1 = SOME (n2w p)` by
    (Cases_on `pos` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `pos IN C /\ hi IN C` by fs[SUBSET_DEF, Abbr `A`] >>
  `op_taint tn1 pos = {} /\ op_prov G1 hi = NONE /\ op_taint tn1 hi = {} /\
   op_prov G1 hd = NONE /\ op_taint tn1 hd = {}` by metis_tac[] >>
  qabbrev_tac `s1pc = s1 with vs_inst_idx := s.vs_inst_idx + LENGTH a` >>
  `abi_decode_ptr_window G1 tn1 s1pc source (n2w B) L` by
    (irule abi_decode_ptr_window_frame >> qexistsl_tac [`G`, `s`, `tn`] >>
     simp[Abbr `s1pc`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `eval_operand pos s1pc = SOME (n2w p) /\ B+L <= s1pc.vs_alloca_next` by
    (Cases_on `pos` >> fs[Abbr `s1pc`, eval_operand_def, lookup_var_def]) >>
  `not_fresh_at st1 source` by metis_tac[] >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
  qpat_x_assum `cn = Var _` SUBST_ALL_TAC >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s1pc` by
    (`allocas_below_fmp s1pc <=> allocas_below_fmp s` by
       (qunabbrev_tac `s1pc` >>
        qpat_assum `s1 = s with vs_vars := _` SUBST1_TAC >>
        simp[allocas_below_fmp_def]) >>
     simp[]) >>
  drule_all abi_decode_array_position_load_cut >>
  disch_then (qspecl_then [`func`, `PG`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2pc` strip_assume_tac)))) >>
  `s2pc = s2 with vs_inst_idx := s.vs_inst_idx + LENGTH a` by
    (qpat_assum `run_inst_seq _ _ = OK s2pc` mp_tac >>
     qpat_assum `Abbrev (b = _)` (fn th =>
       pure_rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
     qunabbrev_tac `s1pc` >>
     qpat_assum `EVERY _ b`
       (mp_then Any (fn th => pure_rewrite_tac[th]) fragExecTheory.run_inst_seq_inst_idx) >>
     simp[exec_result_map_def]) >>
  `run_inst_seq_mem_ok b s1` by
    ((qpat_assum `run_inst_seq_mem_ok _ s1pc` mp_tac >>
     simp[Abbr `b`, Abbr `s1pc`, run_inst_seq_mem_ok_inst_idx] >> (metis_tac[Abbr `b`, Abbr `s1pc`, run_inst_seq_mem_ok_inst_idx]))) >>
  `inst_seq_ptr D 0 ctx func PG G tn (a ++ b) s G2 tn2` by
    (qunabbrev_tac `s1pc` >> qunabbrev_tac `b` >>
     drule_all bop_inst_seq_ptr_append >> simp[]) >>
  `run_inst_seq_mem_ok (a ++ b) s /\ run_inst_seq (a ++ b) s = OK s2` by
    ((conj_tac >- (irule run_inst_seq_mem_ok_append >> simp[]) >>
     simp[run_inst_seq_append] >> (metis_tac[run_inst_seq_append, run_inst_seq_mem_ok_append]))) >>
  `!x. not_fresh_at st1 x ==> lookup_var x s2 = lookup_var x s1 /\
    FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x)` by
    (qpat_assum `!x. not_fresh_at st1 x ==> lookup_var x s2pc = _ /\ _` mp_tac >>
     qpat_assum `s2pc = _` SUBST1_TAC >> qunabbrev_tac `s1pc` >>
     simp[NoAsms, lookup_var_def]) >>
  `(op_prov G2 hi = NONE /\ op_taint tn2 hi = {}) /\
   (op_prov G2 hd = NONE /\ op_taint tn2 hd = {})` by
    (conj_tac >-
      (Cases_on `hi` >> gvs[op_prov_def, op_taint_def] >> metis_tac[]) >>
     Cases_on `hd` >> gvs[op_prov_def, op_taint_def] >> metis_tac[]) >>
  suspend "tail"
QED

Resume abi_decode_dynarray_position_prefix_fresh_ptr[tail]:
  qabbrev_tac `R2 = {x | not_fresh_at st3 x}` >>
  qabbrev_tac `A2 = {hd; Var out; hi} UNION IMAGE Lit UNIV` >>
  `st3.cs_next_var <= sb.cs_next_var /\ inst_extends st3 sb /\
   (?C2. bop_scalar_seq R2 A2 c C2)` by
    (qunabbrev_tac `c` >>
     `hd IN A2 /\ Var out IN A2 /\ hi IN A2 /\ (!w. Lit w IN A2) /\
      (!x. x IN R2 ==> not_fresh_at st3 x)` by simp[Abbr `R2`, Abbr `A2`] >>
     drule_all abi_decode_scalar_count_payload_code >> simp[]) >>
  `!op. op IN A2 ==> op_prov G2 op = NONE /\ op_taint tn2 op = {}` by
    (simp[Abbr `A2`, IN_IMAGE] >> rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  qabbrev_tac `entry = s2 with vs_inst_idx := s.vs_inst_idx + LENGTH (a ++ b)` >>
  `run_inst_seq c entry = OK (u with vs_inst_idx := s.vs_inst_idx + LENGTH (a ++ b))` by
    ((qunabbrev_tac `entry` >>
     qpat_assum `EVERY _ c`
       (mp_then Any (fn th => pure_rewrite_tac[th]) fragExecTheory.run_inst_seq_inst_idx) >>
     qpat_assum `run_inst_seq c s2 = OK u` (fn th => rewrite_tac[th, exec_result_map_def]) >> (simp[exec_result_map_def]))) >>
  `?G3 tn3. inst_seq_ptr D 0 ctx func PG G2 tn2 c entry G3 tn3 /\
     (!x. not_fresh_at st3 x ==> lookup_var x u = lookup_var x s2 /\
       FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tn3 (Var x) = op_taint tn2 (Var x)) /\
     tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\
     tn3.t_trans = tn2.t_trans /\ tn3.t_imm = tn2.t_imm` by
    (`ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
       (`allocas_below_fmp entry <=> allocas_below_fmp s1pc` by
          (qpat_assum `(s2pc with vs_vars := s1pc.vs_vars) = s1pc`
             (mp_tac o Q.AP_TERM `\z. allocas_below_fmp z`) >>
           qpat_assum `s2pc = _` SUBST1_TAC >>
           simp[Abbr `entry`, allocas_below_fmp_def]) >>
        simp[]) >>
     qpat_x_assum `run_inst_seq c s2 = OK u` kall_tac >>
     drule_all abi_decode_scalar_run_frame >>
     disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
     qexistsl_tac [`H`, `th`] >>
     simp[] >> fs[Abbr `R2`, Abbr `entry`, lookup_var_def]) >>
  `inst_seq_ptr D 0 ctx func PG G tn ((a ++ b) ++ c) s G3 tn3` by
    (qunabbrev_tac `entry` >>
     `EVERY (\i. ~is_terminator i.inst_opcode) (a ++ b)` by simp[] >>
     drule_all bop_inst_seq_ptr_append >> simp[]) >>
  `run_inst_seq_mem_ok c s2` by metis_tac[bodyFullAbiDecodeClampMemoryTheory.abi_decode_scalar_seq_mem_ok] >>
  `run_inst_seq_mem_ok ((a ++ b) ++ c) s` by
    (irule run_inst_seq_mem_ok_append >> simp[]) >>
  `!x. not_fresh_at st1 x ==> not_fresh_at st3 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    FLOOKUP G3 x = FLOOKUP G x /\ op_taint tn3 (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >> metis_tac[]) >>
  `!x. not_fresh_at st3 x ==> lookup_var x u = lookup_var x s2pc /\
    FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (qpat_assum `!x. not_fresh_at st3 x ==> lookup_var x u = lookup_var x s2 /\ _` mp_tac >>
     qpat_assum `s2pc = _` SUBST1_TAC >> simp[lookup_var_def]) >>
  `abi_decode_ptr_window G3 tn3 u source (n2w B) L /\
   abi_decode_ptr_window G3 tn3 u ar (n2w (B+p)) 32` by
    (conj_tac >> irule abi_decode_ptr_window_frame >>
     qexistsl_tac [`G2`, `s2pc`, `tn2`] >> simp[] >> metis_tac[]) >>
  `not_fresh_at sb ar` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qexistsl_tac [`G3`, `tn3`] >> simp[] >> metis_tac[]
QED

Finalise abi_decode_dynarray_position_prefix_fresh_ptr

Theorem abi_decode_dynarray_position_prefix_success_joint:
  abi_decode_dynarray_position_prefix pos MLOAD (Var source) hi maxn stride sa = (addr,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK u /\
  fn_has_code sa sb func /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa source /\
  (!x. pos = Var x ==> not_fresh_at sa x) /\
  (!x. hi = Var x ==> not_fresh_at sa x) /\
  hi <> Lit 0w /\
  abi_decode_ptr_window G tn s source (n2w B) L /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand hi s = SOME (n2w L) /\
  op_prov G pos = NONE /\ op_prov G hi = NONE /\
  op_taint tn pos = {} /\ op_taint tn hi = {} /\
  p < dimword (:256) /\ B+L < dimword (:256) /\ B+L <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ allocas_from lo s ==>
  ?ar G' tn'. addr = Var ar /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    u = s with vs_vars := u.vs_vars /\
    abi_decode_ptr_window G' tn' u source (n2w B) L /\
    abi_decode_ptr_window G' tn' u ar (n2w (B+p)) 32 /\
    not_fresh_at sb ar /\
    w2n (mload (B+p) s) <= maxn /\
    p+32+w2n (mload (B+p) s)*stride <= L /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\ allocas_from lo u
Proof
  strip_tac >>
  drule_then assume_tac abi_decode_mload_prefix_opcodes >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `w2n (mload (B+p) s) <= maxn /\ p+32+w2n (mload (B+p) s)*stride <= L` by
    (qabbrev_tac `ps = abi_decoder_prune_vars sa.cs_next_var s` >>
     `abi_decoder_operand_live sa.cs_next_var pos /\
      abi_decoder_operand_live sa.cs_next_var hi /\
      abi_decoder_operand_live sa.cs_next_var (Var source)` by
       (Cases_on `pos` >> Cases_on `hi` >>
        fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
     `eval_operand (Var source) s = SOME (n2w B)` by
       fs[abi_decode_ptr_window_def, eval_operand_def] >>
     `L < dimword (:256)` by decide_tac >>
     `eval_operand (Var source) ps = SOME (n2w B) /\
      eval_operand pos ps = SOME (n2w p) /\ eval_operand hi ps = SOME (n2w L) /\
      fresh_vars_wrt sa ps` by simp[Abbr `ps`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
     mp_tac (abi_malformed_dynarray_prefix_total |> Q.INST
       [`st` |-> `sa`, `en` |-> `sb`, `base_op` |-> `Var source`,
        `opc` |-> `MLOAD`, `s` |-> `ps`, `h` |-> `L`, `b` |-> `B`]) >>
     (impl_tac >- simp[]) >> strip_tac
     >- (qunabbrev_tac `ps` >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
     `B+p < dimword (:256)` by decide_tac >>
     `mload (B+p) ps = mload (B+p) s` by simp[Abbr `ps`, abi_decoder_prune_vars_def, mload_def] >>
     fs[abi_decode_load_def, w2n_n2w]) >>
  `p+32 <= L` by decide_tac >>
  drule_all abi_decode_dynarray_position_prefix_fresh_ptr >>
  disch_then (qspecl_then [`func`, `PG`,
    `<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>`]
    strip_assume_tac) >>
  `u = s with vs_vars := u.vs_vars` by (drule_all abi_malformed_dynarray_prefix_exact >> simp[]) >>
  `allocas_from lo u` by
    (qpat_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `inst_seq_ptr
    <|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>
    lo ctx func PG G tn (emitted_insts sa sb) s H th` by
    (irule (fragGasCopySeqLiftPropsTheory.inst_seq_ptr_lower_bound_transport |> Q.INST [`lo0` |-> `0`]) >> simp[]) >>
  `!explicit. gas_origin_ptr_path
     (<|d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {}|>,
      lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),H,th)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.emitted_origin_ptr_path >>
     simp[] >> qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     `MEM i (emitted_insts sa sb)` by simp[MEM_APPEND] >>
     qpat_assum `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) _`
       (drule_then mp_tac o REWRITE_RULE[EVERY_MEM]) >>
     Cases_on `i.inst_opcode = DALLOCA` >> simp[abi_decoder_reentry_opcode_def]) >>
  qexistsl_tac [`ar`, `H`, `th`] >> simp[] >>
  metis_tac[gas_origin_ptr_path_from_no_dead]
QED
