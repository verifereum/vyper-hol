(* RawCreate's post-allocation memory residual. *)
Theory bodyCreateRawMemoryRunMods
Ancestors
  context compileEnv emitHelper venomInst venomState venomExecSemantics
  finite_map pred_set words list arithmetic ptrDiscipline ptrSafeRun
  fragGasOriginPtr fragGasOriginPtrLoop fragExec unitTransformDefs memSafeRun
  bodyPtrMakeArrayEmission bodyPtrMakeArrayPrimitiveInstall
  emitHelperProps assignBasePtrStoragePath exprPtrCtorImmStore decoderNavigationPtr
  instMemFrontier typedCopyPtr decoderGhostFramePtr ptrSafetyTransport
  loweringShapeDefs exprLoweringProps assignTuplePtrCopyLen reasonCopySourcePtr
  bodyFullAbiEncodeCopy taintAgree codegenRel contextCodegenRel
  typedMemoryCopy bytesSnapshotMemory valueEncodingProps placeMemoryTypedPrimitive
  venomMemDefs abiAllocationHistory

Theorem clean_word_taint[local]:
  (!i. a <= i /\ i < a+32 ==> i NOTIN ts) ==> mem_word_taint ts a = {}
Proof
  strip_tac >> simp[mem_word_taint_def, EXTENSION] >> qx_gen_tac `k` >>
  Cases_on `k < 32` >> simp[] >>
  first_x_assum (qspec_then `a+k` mp_tac) >> simp[]
QED

Theorem raw_memory_load[local]:
  emit_op MLOAD [Var src] m = (len,ml) /\ fn_has_code m ml func /\
  eval_operand (Var src) j = SOME w /\ ptr_covers G tj src j 32 /\
  w2n w+32 <= j.vs_alloca_next /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tj.t_mem) /\
  allocas_from lo j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?v Gv tv.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) [] (OK v,Gv,tv)) /\
    v.vs_current_bb = ml.cs_current_bb /\ v.vs_inst_idx = LENGTH ml.cs_current_insts /\
    (v with <|vs_vars := j.vs_vars; vs_inst_idx := j.vs_inst_idx|>) = j /\
    eval_operand len v = SOME (mload (w2n w) j) /\ op_taint tv len = {} /\
    (tv with t_var := tj.t_var) = tj /\
    (!x. not_fresh_at m x ==> lookup_var x v = lookup_var x j /\
      FLOOKUP Gv x = FLOOKUP G x /\ op_taint tv (Var x) = op_taint tj (Var x))
Proof
  strip_tac >> drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  drule_then assume_tac clean_word_taint >>
  qabbrev_tac `u = update_var tmp (mload (w2n w) j) j` >>
  qabbrev_tac `i = mk_inst m.cs_next_id MLOAD [Var src] [tmp]` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) []
    (OK (u with vs_inst_idx := SUC j.vs_inst_idx),step_prov PG G i u,step_taint i j u tj)` by
    (gen_tac >> irule straight_line_step_origin >>
     qpat_assum `get_instruction _ _ = SOME i` (irule_at Any) >>
     simp[Abbr `i`, Abbr `u`, mk_inst_def, is_terminator_def, below_frontier_MLOAD,
          inst_dload_in_section_other, step_MLOAD, ptr_inst_ok_mload_lo]) >>
  qexistsl [`u with vs_inst_idx := SUC j.vs_inst_idx`,
            `step_prov PG G i u`,`step_taint i j u tj`] >>
  simp[Abbr `i`, Abbr `u`, assign_base_mload_ghost, update_var_def,
       lookup_var_def, eval_operand_def, op_taint_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  conj_tac >- simp[venom_state_component_equality] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `tmp = _` SUBST_ALL_TAC >>
  `x <> STRING #"%" (toString m.cs_next_var)` by simp[] >> simp[] >> metis_tac[]
QED

Theorem raw_memory_add[local]:
  emit_op ADD [len;Lit 32w] ml = (cnt,mc) /\ fn_has_code ml mc func /\
  eval_operand len v = SOME w /\ op_taint tv len = {} /\
  allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v) /\
  ~v.vs_halted /\ v.vs_current_bb = ml.cs_current_bb /\
  v.vs_inst_idx = LENGTH ml.cs_current_insts ==>
  ?t Jc tt.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK t,Jc,tt)) /\
    t.vs_current_bb = mc.cs_current_bb /\ t.vs_inst_idx = LENGTH mc.cs_current_insts /\
    (t with <|vs_vars := v.vs_vars; vs_inst_idx := v.vs_inst_idx|>) = v /\
    eval_operand cnt t = SOME (w+32w) /\ op_taint tt cnt = {} /\
    (tt with t_var := tv.t_var) = tv /\
    (!x. not_fresh_at ml x ==> lookup_var x t = lookup_var x v /\
      FLOOKUP Jc x = FLOOKUP Gv x /\ op_taint tt (Var x) = op_taint tv (Var x))
Proof
  strip_tac >> drule_all_then strip_assume_tac emit_op_fetch_boundary >>
  qabbrev_tac `u = update_var tmp (w+32w) v` >>
  qabbrev_tac `i = mk_inst ml.cs_next_id ADD [len;Lit 32w] [tmp]` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) []
    (OK (u with vs_inst_idx := SUC v.vs_inst_idx),step_prov PG Gv i u,step_taint i v u tv)` by
    (gen_tac >> irule straight_line_step_origin >>
     qpat_assum `get_instruction _ _ = SOME i` (irule_at Any) >>
     `ptr_inst_ok D lo 0 ctx func Gv tv i v` by
       (simp[Abbr `i`] >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
        qexists `0` >> simp[ptr_inst_ok_copy_len_binop, op_taint_def]) >>
     simp[Abbr `i`, Abbr `u`, mk_inst_def, is_terminator_def, step_inst_base_opcode_eqs,
          exec_pure2_def, eval_operand_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `op_taint (step_taint i v u tv) (Var tmp) = {} /\
   (!x. x <> tmp ==> FLOOKUP (step_prov PG Gv i u) x = FLOOKUP Gv x /\
     op_taint (step_taint i v u tv) (Var x) = op_taint tv (Var x))` by
    simp[Abbr `i`, Abbr `u`, copy_len_binop_ghost_frame] >>
  `(step_taint i v u tv with t_var := tv.t_var) = tv` by
    simp[Abbr `i`, Abbr `u`, stmtAppendStorageRunPtrTheory.scalar_add_taint, update_var_def] >>
  qexistsl [`u with vs_inst_idx := SUC v.vs_inst_idx`,
            `step_prov PG Gv i u`,`step_taint i v u tv`] >>
  simp[Abbr `u`, update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE] >>
  conj_tac >- simp[venom_state_component_equality] >>
  conj_tac
  >- simp[Abbr `i`, stmtAppendStorageRunPtrTheory.scalar_add_taint,
          op_taint_def, FLOOKUP_UPDATE] >>
  gen_tac >> strip_tac >> qpat_x_assum `tmp = _` SUBST_ALL_TAC >>
  `x <> STRING #"%" (toString ml.cs_next_var)` by simp[] >> simp[] >> metis_tac[]
QED

Theorem raw_memory_mcopy[local]:
  compile_copy_memory_dynamic (Var root) (Var src) cnt mc = ((),b) /\
  fn_has_code mc b func /\ lookup_var root t = SOME (n2w pbase) /\
  lookup_var src t = SOME (n2w srcp) /\ eval_operand cnt t = SOME (n2w n) /\
  op_taint tt cnt = {} /\ ptr_covers Jc tt root t n /\ ptr_covers Jc tt src t n /\
  pbase < dimword (:256) /\ srcp < dimword (:256) /\ n < dimword (:256) /\
  pbase+n <= t.vs_alloca_next /\ srcp+n <= t.vs_alloca_next /\
  (!i. srcp <= i /\ i < srcp+n ==> i NOTIN tt.t_mem) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\
  ~t.vs_halted /\ t.vs_current_bb = mc.cs_current_bb /\
  t.vs_inst_idx = LENGTH mc.cs_current_insts ==>
  t.vs_current_bb = b.cs_current_bb /\
  !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Jc,tt) []
    (OK (mcopy pbase srcp n t with vs_inst_idx := LENGTH b.cs_current_insts),Jc,
     tt with t_mem := tt.t_mem DIFF {i | pbase <= i /\ i < pbase+n})
Proof
  strip_tac >>
  qpat_assum `compile_copy_memory_dynamic _ _ _ _ = _`
    (assume_tac o REWRITE_RULE[compile_copy_memory_dynamic_def]) >>
  drule_all_then strip_assume_tac emit_void_fetch_boundary >>
  `w2n (n2w pbase:bytes32) = pbase /\ w2n (n2w srcp:bytes32) = srcp /\
   w2n (n2w n:bytes32) = n` by simp[w2n_n2w, LESS_MOD] >>
  qabbrev_tac `i = mk_inst mc.cs_next_id MCOPY [Var root;Var src;cnt] []` >>
  `{pbase+q | q < n /\ q+srcp IN tt.t_mem} = {}` by
    (simp[EXTENSION] >> qx_gen_tac `k` >>
     Cases_on `k < n` >> simp[] >>
     qpat_assum `!i. srcp <= i /\ i < srcp+n ==> _` (qspec_then `k+srcp` mp_tac) >> simp[]) >>
  `i.inst_opcode = MCOPY /\ i.inst_outputs = [] /\
   i.inst_operands = [Var root;Var src;cnt] /\
   eval_operand (Var root) t = SOME (n2w pbase) /\
   eval_operand (Var src) t = SOME (n2w srcp)` by simp[Abbr `i`, mk_inst_def, eval_operand_def] >>
  `step_taint i t (mcopy pbase srcp n t) tt =
      tt with t_mem := tt.t_mem DIFF {k | pbase <= k /\ k < pbase+n}` by
    (drule_all step_taint_mcopy >> simp[]) >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb t.vs_inst_idx = SOME i` by simp[Abbr `i`] >>
  `inst_mem_below_frontier i t /\ inst_dload_in_section i t` by
    simp[Abbr `i`, below_frontier_MCOPY, inst_dload_in_section_other, mk_inst_def, eval_operand_def] >>
  conj_tac >- simp[] >> gen_tac >>
  qpat_x_assum `Abbrev (i = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `ptr_covers Jc tt root t (w2n (n2w n:bytes32)) /\
   ptr_covers Jc tt src t (w2n (n2w n:bytes32))` by simp[] >>
  drule_all abi_encode_mcopy_origin_path >> simp[]
QED

(* The scalar prefix changes only the cursor and its own fresh registers. *)
Theorem raw_memory_count[local]:
  emit_op MLOAD [Var src] m = (len,ml) /\ fn_has_code m ml func /\
  emit_op ADD [len;Lit 32w] ml = (cnt,mc) /\ fn_has_code ml mc func /\
  lookup_var src j = SOME (n2w srcp) /\ srcp < dimword (:256) /\
  ptr_covers G tj src j (32+LENGTH bs) /\ srcp+32+LENGTH bs <= j.vs_alloca_next /\
  mload srcp j = n2w (LENGTH bs) /\
  (!i. srcp <= i /\ i < srcp+32+LENGTH bs ==> i NOTIN tj.t_mem) /\
  allocas_from lo j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?t Jc tt.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) [] (OK t,Jc,tt)) /\
    t.vs_current_bb = mc.cs_current_bb /\ t.vs_inst_idx = LENGTH mc.cs_current_insts /\
    (t with <|vs_vars := j.vs_vars; vs_inst_idx := j.vs_inst_idx|>) = j /\
    eval_operand cnt t = SOME (n2w (32+LENGTH bs)) /\ op_taint tt cnt = {} /\
    (tt with t_var := tj.t_var) = tj /\
    (!x. not_fresh_at m x ==> lookup_var x t = lookup_var x j /\
      FLOOKUP Jc x = FLOOKUP G x /\ op_taint tt (Var x) = op_taint tj (Var x))
Proof
  strip_tac >>
  `w2n (n2w srcp:bytes32) = srcp` by simp[w2n_n2w, LESS_MOD] >>
  `ptr_covers G tj src j 32` by
    (irule ptr_covers_mono >> qexists `32+LENGTH bs` >> simp[]) >>
  `eval_operand (Var src) j = SOME (n2w srcp)` by simp[eval_operand_def] >>
  `w2n (n2w srcp:bytes32)+32 <= j.vs_alloca_next` by simp[] >>
  `!i. w2n (n2w srcp:bytes32) <= i /\ i < w2n (n2w srcp:bytes32)+32 ==>
       i NOTIN tj.t_mem` by
    (gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
  drule_all raw_memory_load >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS))) >>
  `eval_operand len v = SOME (n2w (LENGTH bs))` by gvs[] >>
  `~v.vs_halted /\ allocas_from lo v /\ (ctx_has_dalloca ctx ==> allocas_below_fmp v)` by
    (qpat_assum `v with <|vs_vars := _;vs_inst_idx := _|> = j`
      (fn th => qpat_assum `allocas_from lo j` mp_tac >>
                qpat_assum `ctx_has_dalloca ctx ==> _` mp_tac >>
                qpat_assum `~j.vs_halted` mp_tac >>
                pure_once_rewrite_tac[GSYM th]) >> simp[NoAsms, allocas_from_def, allocas_below_fmp_def] >>
     rpt strip_tac >> metis_tac[]) >>
  drule_all raw_memory_add >>
  disch_then (qspecl_then [`explicit`,`PG`,`Gv`]
    (qx_choosel_then [`t`,`Jc`,`tt`] (map_every assume_tac o CONJUNCTS))) >>
  qexistsl [`t`,`Jc`,`tt`] >>
  conj_tac
  >- (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gv`,`v`,`tv`] >> simp[]) >>
  `!x. not_fresh_at m x ==> not_fresh_at ml x` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND, not_fresh_at_mono] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `t with <|vs_vars := v.vs_vars;vs_inst_idx := v.vs_inst_idx|> = v`
      (fn th => qpat_assum `v with <|vs_vars := j.vs_vars;vs_inst_idx := j.vs_inst_idx|> = j` mp_tac >>
                pure_once_rewrite_tac[GSYM th]) >> simp[] >> NO_TAC) >>
  TRY (qpat_assum `eval_operand cnt t = _` mp_tac >> simp[NoAsms, word_add_n2w, ADD_COMM] >> NO_TAC) >>
  TRY (qpat_assum `tt with t_var := _ = tv` (fn th =>
         qpat_assum `tv with t_var := _ = tj` mp_tac >> pure_once_rewrite_tac[GSYM th]) >> simp[] >> NO_TAC) >>
  gen_tac >> strip_tac >>
  `not_fresh_at ml x` by simp[] >>
  qpat_assum `!x. not_fresh_at ml x ==> lookup_var x t = _ /\ _` (drule_then strip_assume_tac) >>
  qpat_assum `!x. not_fresh_at m x ==> lookup_var x v = _ /\ _` (drule_then strip_assume_tac) >> simp[]
QED

Theorem raw_memory_count_effect[local]:
  (t with <|vs_vars := j.vs_vars;vs_inst_idx := j.vs_inst_idx|>) = j ==>
  t.vs_memory = j.vs_memory /\ t.vs_alloca_next = j.vs_alloca_next /\
  t.vs_halted = j.vs_halted /\ allocas_from lo t = allocas_from lo j /\
  allocas_below_fmp t = allocas_below_fmp j
Proof
  disch_then (fn th => pure_once_rewrite_tac[GSYM th]) >>
  simp[allocas_from_def, allocas_below_fmp_def]
QED

(* The count is 32 plus the live byte length, not the ALLOCA capacity. *)
Theorem raw_create_memory_run_mods:
  emit_op MLOAD [Var src] m = (len,ml) /\
  emit_op ADD [len;Lit 32w] ml = (cnt,mc) /\
  compile_copy_memory_dynamic (Var root) (Var src) cnt mc = ((),b) /\
  fn_has_code m b func /\ fn_inst_ids_distinct func /\
  not_fresh_at m src /\ not_fresh_at m root /\
  lookup_var src j = SOME (n2w srcp) /\ srcp < dimword (:256) /\
  ptr_covers G tj src j (32+LENGTH bs) /\ srcp+32+LENGTH bs <= j.vs_alloca_next /\
  mload srcp j = n2w (LENGTH bs) /\ read_memory (srcp+32) (LENGTH bs) j = bs /\
  (!i. srcp <= i /\ i < srcp+32+LENGTH bs ==> i NOTIN tj.t_mem) /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  lookup_var root j = SOME (n2w pbase) /\ ptr_covers G tj root j cap /\
  32+LENGTH bs <= cap /\ pbase+cap < dimword (:256) /\ pbase+cap <= j.vs_alloca_next /\
  allocas_from lo j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\
  alloca_history func j /\ alloca_inv j /\
  ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\
  j.vs_inst_idx = LENGTH m.cs_current_insts ==>
  ?u Gu tu.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) [] (OK u,Gu,tu)) /\
    ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\
    u.vs_inst_idx = LENGTH b.cs_current_insts /\
    FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
    lookup_var root u = SOME (n2w pbase) /\ ptr_covers Gu tu root u cap /\
    pbase+cap <= u.vs_alloca_next /\
    mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
    (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
    typed_copy_state_frame m pbase cap j u /\
    typed_copy_frame pbase cap j.vs_memory u.vs_memory /\
    (!i. i < pbase \/ pbase+32+LENGTH bs <= i ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
    (!x. not_fresh_at m x ==> lookup_var x u = lookup_var x j /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tj (Var x)) /\
    u.vs_allocas = j.vs_allocas /\ u.vs_alloca_next = j.vs_alloca_next /\
    u.vs_data_section = j.vs_data_section /\ u.vs_accounts = j.vs_accounts /\
    u.vs_call_ctx = j.vs_call_ctx /\ u.vs_transient = j.vs_transient /\
    u.vs_immutables = j.vs_immutables /\
    tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\ tu.t_imm = tj.t_imm /\
    allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    alloca_history func u
Proof
  strip_tac >>
  `ci_mono m ml /\ ci_mono ml mc /\ ci_mono mc b` by
    metis_tac[ci_mono_emit_op, ci_mono_compile_copy_memory_dynamic, pairTheory.SND] >>
  `fn_has_code m ml func /\ fn_has_code ml mc func /\ fn_has_code mc b func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  drule_all raw_memory_count >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`t`,`Jc`,`tt`] (map_every assume_tac o CONJUNCTS))) >>
  drule raw_memory_count_effect >> disch_then (qspec_then `lo` strip_assume_tac) >>
  qabbrev_tac `n = 32 + LENGTH bs` >>
  `srcp+n = srcp+32+LENGTH bs` by (simp[NoAsms, Abbr `n`] >> decide_tac) >>
  `srcp+n <= j.vs_alloca_next` by simp[] >>
  `pbase < dimword (:256) /\ n < dimword (:256) /\ pbase+n <= t.vs_alloca_next` by decide_tac >>
  `!x k. not_fresh_at m x /\ ptr_covers G tj x j k ==> ptr_covers Jc tt x t k` by
    (rpt gen_tac >> strip_tac >> irule ptr_covers_lookup_frame >>
     qpat_assum `ptr_covers G tj x j k` (irule_at Any) >> simp[]) >>
  `lookup_var src t = SOME (n2w srcp) /\ lookup_var root t = SOME (n2w pbase)` by simp[] >>
  `ptr_covers Jc tt src t n /\ ptr_covers Jc tt root t cap` by simp[Abbr `n`] >>
  `ptr_covers Jc tt root t n` by
    (irule ptr_covers_mono >> qexists `cap` >> simp[]) >>
  `tt.t_mem = tj.t_mem /\ tt.t_stor = tj.t_stor /\ tt.t_trans = tj.t_trans /\ tt.t_imm = tj.t_imm` by
    (qpat_assum `tt with t_var := _ = tj` (fn th => pure_once_rewrite_tac[GSYM th]) >> simp[]) >>
  `!i. srcp <= i /\ i < srcp+n ==> i NOTIN tt.t_mem` by simp[] >>
  `allocas_from lo t` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by metis_tac[] >>
  `~t.vs_halted /\ srcp+n <= t.vs_alloca_next` by simp[] >>
  drule_all raw_memory_mcopy >>
  disch_then (qspecl_then [`explicit`,`PG`] (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `u = mcopy pbase srcp n t with vs_inst_idx := LENGTH b.cs_current_insts` >>
  qabbrev_tac `tu = tt with t_mem := tt.t_mem DIFF {i | pbase <= i /\ i < pbase+n}` >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Jc,tt) [] (OK u,Jc,tu)` by
    simp[Abbr `u`,Abbr `tu`] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) [] (OK u,Jc,tu)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Jc`,`t`,`tt`] >> simp[]) >>
  suspend "memory_end"
QED

Resume raw_create_memory_run_mods[memory_end]:
  `!x. lookup_var x u = lookup_var x t /\ op_taint tu (Var x) = op_taint tt (Var x)` by
    simp[Abbr `u`, Abbr `tu`, lookup_var_def, op_taint_def,
         mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
  `ptr_covers Jc tu root u cap` by
    (irule ptr_covers_lookup_frame >> qpat_assum `ptr_covers Jc tt root t cap` (irule_at Any) >> simp[]) >>
  `mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs` by
    (`mload srcp t = n2w (LENGTH bs) /\ read_memory (srcp+32) (LENGTH bs) t = bs` by
       (qpat_assum `mload srcp j = _` mp_tac >>
        qpat_assum `read_memory (srcp+32) (LENGTH bs) j = _` mp_tac >>
        qpat_assum `t.vs_memory = j.vs_memory`
          (fn th => simp[NoAsms,mload_def,read_memory_def,th])) >>
     `mload pbase (mcopy pbase srcp n t) = n2w (LENGTH bs) /\
      read_memory (pbase+32) (LENGTH bs) (mcopy pbase srcp n t) = bs` by
       (qspecl_then [`pbase`,`srcp`,`n`,`LENGTH bs`,`t`] mp_tac mcopy_live_bytestring_reads >>
        simp[Abbr `n`]) >>
     qpat_assum `mload pbase (mcopy _ _ _ _) = _` mp_tac >>
     qpat_assum `read_memory (pbase+32) _ (mcopy _ _ _ _) = _` mp_tac >>
     simp[NoAsms, Abbr `u`, mload_def, read_memory_def]) >>
  `typed_copy_frame pbase cap j.vs_memory u.vs_memory` by
    (simp[typed_copy_frame_def, Abbr `u`] >>
     qpat_assum `t.vs_memory = j.vs_memory` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     conj_tac >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> decide_tac) >>
     irule mcopy_memory_length) >>
  `!x. not_fresh_at m x ==> lookup_var x u = lookup_var x j /\
     FLOOKUP Jc x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tj (Var x)` by simp[] >>
  `u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
   (u with <|vs_vars := j.vs_vars;vs_memory := j.vs_memory;vs_prev_bb := j.vs_prev_bb;
             vs_current_bb := j.vs_current_bb;vs_inst_idx := j.vs_inst_idx|>) = j` by
    (simp[Abbr `u`, mcopy_def, write_memory_with_expansion_def, write_memory_def] >>
     qpat_assum `t with <|vs_vars := _;vs_inst_idx := _|> = j` mp_tac >>
     simp[venom_state_component_equality]) >>
  `alloca_history func u` by
    (irule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (j,G,tj) [] (OK u,Jc,tu)`
       (irule_at Any) >> simp[]) >>
  qexistsl [`u`,`Jc`,`tu`] >>
  simp[typed_copy_state_frame_def, Abbr `tu`, Abbr `n`, IN_DIFF, GSPECIFICATION] >>
  suspend "memory_fields"
QED

Resume raw_create_memory_run_mods[memory_fields]:
  qpat_assum `u with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;
                         vs_current_bb := _;vs_inst_idx := _|> = j` mp_tac >>
  simp[venom_state_component_equality] >> strip_tac >>
  simp[allocas_from_def, allocas_below_fmp_def, ADD_COMM] >>
  conj_tac
  >- qpat_assum `allocas_from lo j` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def]) >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp j`
    (ACCEPT_TAC o REWRITE_RULE [allocas_below_fmp_def])
QED

Finalise raw_create_memory_run_mods
