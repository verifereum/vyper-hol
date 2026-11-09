(* Successful builtin setup, with a framed output allocation. *)
Theory abiDecodePtrReady
Ancestors
  abiDecodePtrHeaderFrame abiDecodePtrInputWindow abiBuiltinDecodeSetup abiBuiltinDecodeHeader
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaAllocInput
  bodyPtrHashBuiltinsShaAllocPath venomInstProofs venomExecSemantics stmtReasonLitFragMemory
  venomInst assignTuplePtrCopyEndpoint
  loweringHalt fragExec fragGasPathPtr emitHelperProps exprLoweringProps
  compileEnv freshWrites bodyPtrDefs ptrDiscipline venomState list rich_list

Theorem abi_builtin_decode_phased_ready_ptr:
  abi_builtin_decode_header (Var p) mn mx sa = ((len,src),sh) /\
  compile_alloc_buffer outsz sh = (buf,ready) /\
  fn_has_code sa ready func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_var p s = SOME w /\ not_fresh_at sa p /\
  ptr_covers G tn p s (32+n) /\
  w2n w + 32+n < dimword (:256) /\
  (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tn.t_mem) /\
  mload (w2n w) s = n2w cnt /\ mn <= cnt /\ cnt <= mx /\
  mx < dimword (:256) /\ abi_decoder_operand_live sa.cs_next_var (Var p) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  fn_inst_ids_distinct func /\ outsz < dimword (:256) ==>
  ?u G2 tn2 out q r wout.
    buf.buf_operand = Var out /\ src = Var q /\ len = Var r /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G2 tn2 (OK u) /\
    stmt_state_rel ctx func cenv cx es u /\ ghost_inv d cenv cx es G2 tn2 u /\
    ptr_covers G2 tn2 out u outsz /\ lookup_var out u = SOME wout /\
    w2n wout+outsz < dimword (:256) /\
    ptr_covers G2 tn2 q u n /\ lookup_var q u = SOME (w+32w) /\
    eval_operand (Var r) u = SOME (n2w cnt) /\
    op_prov G2 (Var r) = NONE /\ op_taint tn2 (Var r) = {} /\
    ~u.vs_halted /\ u.vs_current_bb = ready.cs_current_bb /\
    u.vs_inst_idx = LENGTH ready.cs_current_insts /\
    FLOOKUP u.vs_allocas sh.cs_next_id = SOME (w2n wout,outsz) /\
    u.vs_memory = s.vs_memory /\ sh.cs_next_id < ready.cs_next_id /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sh.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
       regions_disjoint (w2n wout) outsz b k) /\
    (!name b k. local_region cenv es.scopes u name b k ==>
       regions_disjoint (w2n wout) outsz b k) /\
    not_fresh_at ready out /\ not_fresh_at ready q /\ not_fresh_at ready r /\
    fresh_vars_wrt limit_st u /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n wout) outsz) /\
    (((?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
         aid < sh.cs_next_id /\ b <= w2n w /\ w2n w+32+n <= b+k) \/
      (?name b k. local_region cenv es.scopes s name b k /\
         b <= w2n w /\ w2n w+32+n <= b+k)) ==>
      (!i. w2n (w+32w) <= i /\ i < w2n (w+32w)+n ==> i NOTIN tn2.t_mem) /\
      regions_disjoint (w2n wout) outsz (w2n (w+32w)) n)
Proof
  strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `cs_extends sa sh` by
    (fs[inst_extends_def, cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `sh.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_builtin_decode_header_frame_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK h)` >>
  `local_ptrs_reserved cenv sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sh x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  `MEM (mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
     [STRING #"%" (toString sh.cs_next_var)]) (fn_insts func)` by simp[] >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "compose"
QED

Resume abi_builtin_decode_phased_ready_ptr[compose]:
  `emitted_insts sh ready = [mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
     [STRING #"%" (toString sh.cs_next_var)]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_APPEND] >>
  `lookup_block h.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sh ready) (DROP h.vs_inst_idx bb.bb_instructions)` by
    (conj_tac >- metis_tac[] >>
     qpat_x_assum `[_] ≼ _` mp_tac >> simp[]) >>
  drule_all hash_literal_alloc_counted_path >>
  disch_then assume_tac >>
  `step_inst 0 ctx (mk_inst sh.cs_next_id ALLOCA [Lit (n2w outsz)]
     [STRING #"%" (toString sh.cs_next_var)]) h = OK t` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     qpat_x_assum `run_inst_seq _ h = OK t` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, AllCaseEqs()]) >>
  `t.vs_current_bb = h.vs_current_bb /\ t.vs_halted = h.vs_halted` by
    (drule step_preserves_control_flow >> simp[mk_inst_def, is_terminator_def] >>
     strip_tac >> drule step_preserves_halted >> simp[mk_inst_def, is_terminator_def]) >>
  `ptr_covers G1 tn1 q t n` by
    (irule hash_old_pointer_frame >>
     goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `lookup_var q t = SOME (w+32w) /\ eval_operand (Var r) t = SOME (n2w cnt) /\
   op_prov G1 (Var r) = NONE /\ op_taint tn1 (Var r) = {}` by
    (fs[ghost_kept_def, op_prov_def, eval_operand_def] >> simp[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH ready.cs_current_insts`,
    `G1`, `tn1`, `p'`, `q`, `r`, `w'`] >>
  simp[stmt_state_rel_inst_idx, ghost_inv_inst_idx, ptr_covers_def,
       lookup_var_def, eval_operand_def] >>
  suspend "path"
QED

Resume abi_builtin_decode_phased_ready_ptr[path]:
  qpat_x_assum `!D PG G tn. gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`D`, `PG`, `H`, `tm`] mp_tac) >>
  simp[arithmeticTheory.ADD1] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK h)` mp_tac >>
      qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ h _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rpt strip_tac >> drule_all gas_path_ptr_then >> simp[]) >>
  gvs[lookup_var_def, eval_operand_def, local_region_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
  qpat_x_assum `run_inst_seq [_] h = OK t` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_alloca_def, mk_inst_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[fresh_vars_wrt_def, update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  metis_tac[fresh_var_distinct, arithmeticTheory.LESS_EQ_TRANS,
            arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac >- suspend "immutable" >> suspend "input"
QED

Resume abi_builtin_decode_phased_ready_ptr[immutable]:
  qpat_x_assum `stmt_state_rel ctx func cenv cx es t` mp_tac >>
  simp_tac bool_ss [stmt_state_rel_def, immutable_alloca_sep_def] >>
  rpt strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >> strip_tac >>
  qpat_x_assum `!name tv v off. _` drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. _` (qspec_then
    `mk_inst sh.cs_next_id ALLOCA [Lit (n2w buf.buf_size)]
      [STRING #"%" (toString sh.cs_next_var)]` mp_tac) >>
  qpat_x_assum `MEM (mk_inst _ _ _ _) (fn_insts func)` mp_tac >>
  simp[mk_inst_def]
QED

Resume abi_builtin_decode_phased_ready_ptr[input]:
  disch_tac >>
  `w2n (w+32w) = w2n w+32` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
     irule arithmeticTheory.LESS_MOD >> decide_tac) >>
  `!name b k. local_region cenv es.scopes s name b k ==>
    local_region cenv es.scopes t name b k` by
    (simp_tac bool_ss [local_region_def] >> rpt strip_tac >>
     rename1 `FLOOKUP cenv.ce_vars nm = SOME (PtrVar (Var lp) ks)` >>
     `not_fresh_at sh lp /\ not_fresh_at sa lp` by
       (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_x_assum `!x. not_fresh_at sh x ==> FLOOKUP t.vs_vars x = _`
       (qspec_then `lp` mp_tac) >>
     qpat_x_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
       (qspec_then `lp` mp_tac) >>
     simp[lookup_var_def] >> rpt strip_tac >>
     gvs[lookup_var_def]) >>
  `!name b k. local_region cenv es.scopes t name b k ==>
     regions_disjoint (w2n w') buf.buf_size b k` by
    (simp_tac bool_ss [local_region_def, lookup_var_def] >>
     first_assum ACCEPT_TAC) >>
  `regions_disjoint (w2n w') buf.buf_size (w2n w) (32+n)` by
    (irule abi_decode_physical_window_disjoint >>
     qexistsl_tac [`cenv`, `es`, `s`, `sh`] >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!name b k. local_region cenv es.scopes t name b k ==> _` irule >>
       qexists_tac `name` >>
       qpat_x_assum `!name b k. local_region cenv es.scopes s name b k ==> _` drule >>
       simp[]) >>
     conj_tac >- (rpt strip_tac >>
       qpat_x_assum `!aid b k. _ /\ FLOOKUP s.vs_allocas aid = _ ==> _`
         irule >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
     `w2n w + (32+n) = n + (w2n w+32)` by decide_tac >>
     asm_rewrite_tac [] >>
     qpat_x_assum `_ \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [local_region_def, lookup_var_def]) >>
  reverse conj_tac
  >- (qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
      qpat_x_assum `w2n (w+32w) = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  suspend "clean"
QED

Resume abi_builtin_decode_phased_ready_ptr[clean]:
  `run_inst_seq (emitted_insts sh ready) h = OK t` by
    (asm_rewrite_tac []) >>
  drule hash_literal_alloc_memory_taint >>
  simp[] >>
  disch_then (qspec_then `tm` assume_tac) >>
  `n + (w2n w+32) = (w2n w+32)+n` by decide_tac >>
  once_asm_rewrite_tac [] >>
  ho_match_mp_tac (Q.INST [`tn` |-> `tm`, `out` |-> `w2n (w':256 word)`,
    `m` |-> `buf.buf_size`] hash_clean_window_allocation_taint) >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      asm_rewrite_tac [] >>
      qpat_x_assum `!i. w2n w <= i /\ _ ==> _` irule >>
      asm_rewrite_tac [] >> decide_tac) >>
  conj_tac
  >- (qpat_x_assum `regions_disjoint _ _ _ _` mp_tac >>
      qpat_x_assum `w2n (w+32w) = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp_tac bool_ss [regions_disjoint_def] >> decide_tac) >>
  qpat_x_assum `!t' s'' fn es' cx' ctx' cenv' b. _` irule >>
  asm_rewrite_tac [] >>
  qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >>
  asm_rewrite_tac []
QED

Finalise abi_builtin_decode_phased_ready_ptr
