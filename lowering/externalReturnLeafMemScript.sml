Theory externalReturnLeafMem
Ancestors
  externalReturnBounds entryHaltMem rawReturnMem fragExecMem bodyMemoryDefs
  stmtSimDefs stmtSimProps loweringPosts exprSimDefs exprSimProps compileEnv stmtLowering rawReturnValue loweringHalt
  fragExec venomExecSemantics venomInst venomMemDefs allocaFootprint
  exprLoweringProps externalReturnNormalizeRun externalReturnNormalizeMem
  valueCopy valueCopyBytes memContinuation memContinuationExit
  typedCopyAgreement exprSimMemDefs allocaSiteResource stmtSimDeclPath
  stmtLoweringMono actualAllocExec valueEncodingTyping valueEncodingProps
  venomState vyperTyping vyperValue

(* A raw suffix consumes the expression value directly, with no assumption
   about a fresh allocation site or declared bytestring capacity. *)
Theorem external_return_raw_value_mem:
  compile_external_return (SOME op) prim T ei msz F nkey ut iv st =
    (x, st') /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  stmt_state_rel H ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  expr_val_rel cx ty v op s /\ is_bytestring_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F)
    (\r. ?ss. r = Halt ss)
Proof
  strip_tac >> drule_all expr_val_at_raw_frontier >> strip_tac >>
  irule compile_external_return_raw_unlock_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`bs`, `p`] >> gvs[]
QED

Theorem return_first_inst_mem[local]:
  fn_has_code st st' func /\ st'.cs_current_bb = st.cs_current_bb /\
  st'.cs_current_insts = st.cs_current_insts ++ inst::tail ==>
  MEM inst (fn_insts func)
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH st.cs_current_insts) = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  irule lookup_block_fn_insts >> goal_assum drule >>
  gvs[get_instruction_def] >> metis_tac[listTheory.EL_MEM]
QED

Theorem external_return_word_value_mem:
  compile_external_return (SOME op) T F ei msz F nkey ut iv st =
    (x, st') /\ fn_has_code st st' func /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  stmt_state_rel H ctx func cenv cx es s /\ eval_operand op s = SOME w ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F) (\r. ?ss. r = Halt ss)
Proof
  strip_tac >>
  `?buf. ~not_fresh_at st buf /\
    st'.cs_current_bb = st.cs_current_bb /\
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf];
       mk_inst (st.cs_next_id + 1) MSTORE [Var buf; op] [];
       mk_inst (st.cs_next_id + 2) RETURN [Var buf; Lit 32w] []]` by
    (irule compile_external_return_word_parts >> goal_assum drule >> simp[]) >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w] [buf]) (fn_insts func)` by
    (irule return_first_inst_mem >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id 32 s).vs_allocas
       st.cs_next_id = SOME (b,32)` by
    (drule stmt_state_rel_alloca_site >> disch_then drule >>
     simp[mk_inst_def, wordsTheory.dimword_def]) >>
  irule compile_external_return_word_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `w` >> gvs[stmt_state_rel_def, alloca_inv_def]
QED

Theorem external_return_static_value_mem:
  compile_external_return (SOME op) F F (AbiCopy m) msz F nkey ut iv st =
    (x, st') /\ fn_has_code st st' func /\
  (!y. op = Var y ==> not_fresh_at st y) /\
  m <= msz /\ msz < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  expr_val_at cenv cx ty sa st es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_footprint tv v = m ==>
  frag_exec_mem ctx st st' (\t. t = s) (\t. F) (\r. ?ss. r = Halt ss)
Proof
  strip_tac >>
  drule compile_external_return_copy_parts >> simp[] >> strip_tac >>
  `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w msz)] [buf])
       (fn_insts func)` by
    (irule return_first_inst_mem >> goal_assum drule >> simp[] >> metis_tac[]) >>
  `?b. FLOOKUP (abi_builtin_allocate_state st.cs_next_id msz s).vs_allocas
       st.cs_next_id = SOME (b,msz)` by
    (drule stmt_state_rel_alloca_site >> disch_then drule >>
     simp[mk_inst_def]) >>
  drule_all expr_val_at_frontier >> strip_tac >>
  irule compile_external_return_copy_frag_mem >>
  goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
  gvs[stmt_state_rel_def, alloca_inv_def] >> metis_tac[]
QED

(* The raw suffix of a valued Return: the value is first copied into a fresh
   buffer sized for the declared return type, then returned raw from there. *)
Theorem raw_copy_alloc_step[local]:
  compile_alloc_buffer n st = (buf,sm) /\ fn_has_code st sm func /\
  stmt_state_rel ctx func cenv cx es s /\ n < dimword (:256) /\
  (!y. op = Var y ==> not_fresh_at st y) /\ eval_operand op s = SOME a /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u b. mem_cont_sim ctx func s u /\ ~u.vs_halted /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    eval_operand op u = SOME a /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    b + n <= u.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_alloca_next < dimword (:256) /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM ins (fn_insts func)` >>
  `ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit (n2w n)] /\
   ins.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   ins.inst_id = st.cs_next_id` by simp[Abbr `ins`, mk_inst_def] >>
  `alloca_room ctx func s /\ alloca_inv s` by fs[stmt_state_rel_def] >>
  `w2n (n2w n : bytes32) = n` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     decide_tac) >>
  `!b sz. FLOOKUP s.vs_allocas ins.inst_id = SOME (b,sz) ==>
     sz = w2n (n2w n : bytes32)` by
    (rpt strip_tac >> qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     rewrite_tac[stmt_state_rel_def] >> strip_tac >>
     qpat_x_assum `!inst n base sz. _`
       (qspecl_then [`ins`, `n2w n`, `b`, `sz`] mp_tac) >>
     asm_rewrite_tac[]) >>
  drule_all alloca_site_execute >> strip_tac >>
  `t.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `op <> Var (STRING #"%" (toString st.cs_next_var))` by metis_tac[] >>
  `eval_operand op t = eval_operand op s` by
    (drule exec_alloca_operand_frame >> simp[] >>
     disch_then (qspec_then `op` mp_tac) >> simp[]) >>
  qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
  simp[Abbr `ins`] >> strip_tac >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `eval_operand op (t with vs_inst_idx := LENGTH sm.cs_current_insts) =
     SOME a` by
    (qpat_x_assum `eval_operand op t = _` mp_tac >>
     qpat_x_assum `eval_operand op s = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `op` >> simp[eval_operand_def, lookup_var_def]) >>
  `eval_operand buf.buf_operand
     (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME (n2w b)` by
    (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
     qpat_x_assum `lookup_var _ t = _` mp_tac >>
     simp[eval_operand_def, lookup_var_def]) >>
  `b + n <= t.vs_alloca_next` by
    (qpat_x_assum `b + w2n _ <= _` mp_tac >>
     qpat_x_assum `w2n _ = n` (fn th => rewrite_tac[th])) >>
  qpat_x_assum `mem_cont_sim _ _ _ _` mp_tac >>
  qpat_x_assum `~(t with vs_inst_idx := _).vs_halted` mp_tac >>
  qpat_x_assum `(t with vs_inst_idx := _).vs_current_bb = _` mp_tac >>
  qpat_x_assum `eval_operand op (t with vs_inst_idx := _) = _` mp_tac >>
  qpat_x_assum `eval_operand buf.buf_operand _ = _` mp_tac >>
  qpat_x_assum `b + n <= _` mp_tac >>
  qpat_x_assum `s.vs_alloca_next <= _` mp_tac >>
  qpat_x_assum `t.vs_alloca_next < _` mp_tac >>
  qpat_x_assum `t.vs_memory = _` mp_tac >>
  qpat_x_assum `buf.buf_operand = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`, `b`] >>
  qpat_x_assum `buf.buf_operand = _` (fn th => fs[th])
QED

Theorem raw_copy_store_step[local]:
  !ctx func op dst sm sn u a d len.
  compile_store_bytestring op dst sm = ((),sn) /\ fn_has_code sm sn func /\
  (!y. op = Var y \/ dst = Var y ==> not_fresh_at sm y) /\
  eval_operand op u = SOME a /\ eval_operand dst u = SOME d /\
  mload (w2n a) u = n2w len /\ 32 + 32 * word_size len < dimword (:256) /\
  w2n a + (32 + 32 * word_size len) <= u.vs_alloca_next /\
  w2n d + (32 + 32 * word_size len) <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?q. mem_cont_sim ctx func u q /\ ~q.vs_halted /\
    q.vs_current_bb = sn.cs_current_bb /\
    q.vs_inst_idx = LENGTH sn.cs_current_insts /\
    q.vs_memory =
      (mcopy (w2n d) (w2n a) (32 + 32 * word_size len) u).vs_memory /\
    q.vs_alloca_next = u.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x u)
Proof
  rpt gen_tac >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sn) u` by
    (irule store_bytestring_mem_ok >> metis_tac[]) >>
  `(!x. op = Var x ==> not_fresh_at sm x) /\
   (!x. dst = Var x ==> not_fresh_at sm x)` by metis_tac[] >>
  `mem_word_at (w2n a) u.vs_memory = n2w len` by
    simp[mem_word_at_eq_mload] >>
  drule_all store_bytestring_run_exact >> strip_tac >>
  `frag_exec_mem ctx sm sn (\x. x = u)
     (\x. x = t with vs_inst_idx := LENGTH sn.cs_current_insts) (K F)` by
    (irule fragExecMemTheory.frag_exec_mem_run_inst_seq >>
     fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  drule mem_cont_sim_from_fragment >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[lookup_var_def] >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u`
    (mp_tac o AP_TERM ``\z. z.vs_alloca_next``) >>
  simp[] >> strip_tac >>
  fs[lookup_var_def]
QED

Theorem raw_copy_return_exit[local]:
  !ctx func dst prim ei msz nkey ut iv sn x st' bs q p.
  compile_external_return (SOME dst) prim T ei msz F nkey ut iv sn =
    (x,st') /\ fn_has_code sn st' func /\
  (!y. dst = Var y ==> not_fresh_at sn y) /\
  LENGTH bs < dimword (:256) /\ eval_operand dst q = SOME p /\
  mload (w2n p) q = n2w (LENGTH bs) /\
  read_memory (w2n (p + 32w)) (LENGTH bs) q = bs /\
  w2n p + 32 <= q.vs_alloca_next /\
  w2n (p + 32w) + LENGTH bs <= q.vs_alloca_next /\
  ~q.vs_halted /\ q.vs_current_bb = sn.cs_current_bb /\
  q.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?fuel r. run_from fuel ctx func q = r /\ exit_result r /\
           mem_safe_run fuel ctx func q
Proof
  rpt gen_tac >> strip_tac >>
  `frag_exec_mem ctx sn st' (\z. z = q) (\z. F) (K T)` by
    (irule compile_external_return_raw_unlock_frag_mem >>
     goal_assum (drule_at (Pat `compile_external_return _ _ _ _ _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`bs`, `p`] >> simp[]) >>
  fs[frag_exec_mem_def] >>
  first_x_assum (qspecl_then [`func`, `q`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Theorem external_return_raw_copy_mem:
  !ctx func cenv cx es s st st' sm sn buf op dty sty lty prim ei msz nkey ut iv
   x v tv.
  compile_alloc_buffer (type_memory_bytes cenv dty) st = (buf,sm) /\
  compile_store_memory_typed cenv buf.buf_operand dty op lty sm = ((),sn) /\
  compile_external_return (SOME buf.buf_operand) prim T ei msz F nkey ut iv sn =
    (x,st') /\
  fn_has_code st st' func /\ (!y. op = Var y ==> not_fresh_at st y) /\
  stmt_state_rel ctx func cenv cx es s /\
  expr_val_rel cx sty v op s /\ expr_store_bound cx sty v op s /\
  is_bytestring_type sty /\ is_bytestring_type lty /\ is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME tv /\ value_has_type tv v /\
  val_store_size tv v <= type_memory_bytes cenv dty /\
  type_memory_bytes cenv dty < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel r. run_from fuel ctx func s = r /\ exit_result r /\
           mem_safe_run fuel ctx func s
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends st sm` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_def, pairTheory.SND] >>
  `cs_extends sm sn` by
    metis_tac[cj 1 ci_mono_typed_memory_family, ci_mono_def, pairTheory.SND] >>
  `cs_extends sn st'` by
    metis_tac[cj 3 ci_mono_return_helpers, ci_mono_def, pairTheory.SND] >>
  `fn_has_code st sm func /\ fn_has_code sm st' func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code sm sn func /\ fn_has_code sn st' func` by
    metis_tac[fn_has_code_split] >>
  suspend "source"
QED

Resume external_return_raw_copy_mem[source]:
  `~is_word_type sty` by metis_tac[is_bytestring_word_type] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  rename1 `eval_operand op s = SOME a` >>
  `val_in_memory tv v (w2n a) s.vs_memory` by
    (qpat_x_assum `!tv. _` drule >>
     qpat_x_assum `~is_word_type sty` (fn th => simp[th])) >>
  `0 < val_footprint tv v` by
    (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, val_footprint_def]) >>
  `val_footprint tv v <= val_store_size tv v` by
    simp[val_footprint_le_store_size] >>
  `w2n a + val_store_size tv v <= s.vs_alloca_next` by
    (qpat_x_assum `expr_store_bound _ _ _ _ _` mp_tac >>
     simp[expr_store_bound_def] >> disch_then drule_all >> simp[]) >>
  `s.vs_alloca_next < dimword (:256)` by
    (`alloca_room ctx func s` by fs[stmt_state_rel_def] >>
     metis_tac[alloca_room_next_lt]) >>
  `w2n a + val_footprint tv v <= dimword (:256)` by decide_tac >>
  drule_all raw_return_value_read >> strip_tac >>
  `val_footprint tv v = 32 + LENGTH bs /\
   val_store_size tv v = 32 + 32 * word_size (LENGTH bs)` by
    (drule_all bytestring_type_value >> strip_tac >> Cases_on `v` >>
     gvs[value_has_type_def, raw_return_bytes_def, val_footprint_def,
         val_store_size_def, string_to_bytes_def]) >>
  suspend "alloc"
QED

Resume external_return_raw_copy_mem[alloc]:
  drule_at (Pat `compile_alloc_buffer _ _ = _`) raw_copy_alloc_step >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op s = _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `compile_store_bytestring op buf.buf_operand sm = ((),sn)` by
    metis_tac[compile_store_memory_typed_bytes] >>
  `b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by
    (simp[wordsTheory.w2n_n2w] >> irule arithmeticTheory.LESS_MOD >>
     decide_tac) >>
  `mload (w2n a) u = n2w (LENGTH bs)` by
    (qpat_x_assum `mload (w2n a) s = _` (SUBST1_TAC o SYM) >>
     simp[mload_def]) >>
  suspend "copy"
QED

Resume external_return_raw_copy_mem[copy]:
  `!y. op = Var y \/ buf.buf_operand = Var y ==> not_fresh_at sm y` by
    (qpat_x_assum `buf.buf_operand = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `!y. op = Var y ==> _` mp_tac >>
     qpat_x_assum `!y. not_fresh_at st y ==> _` mp_tac >>
     qpat_x_assum `not_fresh_at sm _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
  `32 + 32 * word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  `w2n a + (32 + 32 * word_size (LENGTH bs)) <= u.vs_alloca_next` by
    decide_tac >>
  `w2n (n2w b : bytes32) + (32 + 32 * word_size (LENGTH bs)) <=
     u.vs_alloca_next` by decide_tac >>
  qspecl_then [`ctx`, `func`, `op`, `buf.buf_operand`, `sm`, `sn`, `u`, `a`,
    `n2w b`, `LENGTH bs`] mp_tac raw_copy_store_step >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `val_wf tv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `val_in_memory tv v (w2n a) u.vs_memory` by
    (qpat_x_assum `u.vs_memory = _` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `val_footprint tv v <= 32 + 32 * word_size (LENGTH bs)` by decide_tac >>
  `val_in_memory tv v b q.vs_memory` by
    (qpat_x_assum `q.vs_memory = _` SUBST1_TAC >>
     qpat_x_assum `w2n (n2w b : bytes32) = b` (fn th => rewrite_tac[th]) >>
     irule mcopy_val_in_memory >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `val_in_memory tv v (w2n (n2w b : bytes32)) q.vs_memory` by
    (qpat_x_assum `w2n (n2w b : bytes32) = b` (fn th => rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `w2n (n2w b : bytes32) + val_footprint tv v <= dimword (:256)` by
    (qpat_x_assum `w2n (n2w b : bytes32) = b` (fn th => rewrite_tac[th]) >>
     decide_tac) >>
  qspecl_then [`get_tenv cx`, `sty`, `tv`, `v`, `n2w b`, `q`] mp_tac
    raw_return_value_read >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `raw_return_bytes v = SOME bs2` >>
  `bs2 = bs` by
    (qpat_x_assum `raw_return_bytes v = SOME bs2` mp_tac >>
     qpat_x_assum `raw_return_bytes v = SOME bs` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `bs2 = bs` SUBST_ALL_TAC >>
  suspend "exit"
QED

Resume external_return_raw_copy_mem[exit]:
  `w2n (n2w b + 32w : bytes32) = b + 32` by
    (simp[wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `eval_operand buf.buf_operand q = SOME (n2w b)` by
    (qpat_x_assum `eval_operand buf.buf_operand u = _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` mp_tac >>
     qpat_x_assum `not_fresh_at sm _` mp_tac >>
     qpat_x_assum `buf.buf_operand = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_x_assum `buf.buf_operand = _` (fn th => fs[th, eval_operand_def]) >>
     first_x_assum drule >> strip_tac >> fs[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`cenv`, `buf.buf_operand`, `dty`, `op`, `lty`, `sm`] mp_tac
       (cj 1 ci_mono_typed_memory_family) >>
     qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
       (fn th => rewrite_tac[th]) >> simp[]) >>
  `!y. buf.buf_operand = Var y ==> not_fresh_at sn y` by
    (qpat_x_assum `buf.buf_operand = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `not_fresh_at sm _` mp_tac >>
     qpat_x_assum `ci_mono sm sn` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ci_mono_def, loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `w2n (n2w b : bytes32) + (32 + 32 * word_size (LENGTH bs)) <=
     q.vs_alloca_next /\ 32 + LENGTH bs <= 32 + 32 * word_size (LENGTH bs)` by
    (qpat_x_assum `q.vs_alloca_next = _` SUBST1_TAC >>
     qpat_x_assum `val_footprint tv v = _` (fn th =>
       qpat_x_assum `val_footprint tv v <= _` (mp_tac o REWRITE_RULE [th])) >>
     qpat_x_assum `w2n (n2w b : bytes32) + (32 + _) <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> decide_tac) >>
  `w2n (n2w b : bytes32) + 32 <= q.vs_alloca_next` by
    (pop_assum mp_tac >> pop_assum mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> decide_tac) >>
  `w2n (n2w b + 32w : bytes32) + LENGTH bs <= q.vs_alloca_next` by
    (qpat_x_assum `w2n (n2w b + 32w : bytes32) = _` SUBST1_TAC >>
     qpat_x_assum `32 + LENGTH bs <= _` mp_tac >>
     qpat_x_assum `w2n (n2w b : bytes32) = b` (fn th =>
       qpat_x_assum `w2n (n2w b : bytes32) + (32 + _) <= q.vs_alloca_next`
         (mp_tac o REWRITE_RULE [th])) >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> decide_tac) >>
  qspecl_then [`ctx`, `func`, `buf.buf_operand`, `prim`, `ei`, `msz`, `nkey`,
    `ut`, `iv`, `sn`, `x`, `st'`, `bs`, `q`, `n2w b`] mp_tac
    raw_copy_return_exit >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `mem_cont_sim ctx func s q` by metis_tac[mem_cont_sim_trans] >>
  metis_tac[mem_cont_sim_safe_exit]
QED

Finalise external_return_raw_copy_mem
