Theory bodyFullBuiltinPrecompileSuffixFrame
Ancestors
  bodyPtrPrecompileBuiltinsSuffixFrame bodyPtrPrecompileBuiltinsFreshFrame
  bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsSuffixReady
  exprSimPrecompiles exprLoweringProps bodyPtrDefs robustCopyTransportPtr
  ptrDiscipline venomInstProofs venomExecSemantics venomInst venomState
  venomCallOracleDefs exprSimHash compileEnv loweringStateRelDefs
  finite_map pred_set list rich_list freshWrites valueCopy

Theorem precompile_suffix_ghost_output_at:
  ((addr = 1w /\ an = 128w /\ rn = 32w) \/
   (addr = 6w /\ an = 128w /\ rn = 64w) \/
   (addr = 7w /\ an = 96w /\ rn = 64w)) /\
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  precompile_result (venom_call_request s addr 0w wi an T).cr_target
    (venom_call_request s addr 0w wi an T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  src <> gv /\ dst <> gv /\ dst <> cv /\
  ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
  sf.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (lo <> 0 ==> !x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sm x) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  local_ptrs_rel fn cenv es.scopes s /\ ptr_covers G tn dst s (w2n rn) /\
  lo <= w2n wo /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n wo) (w2n rn) b sz) /\
  (addr = 1w ==> !i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
  (addr <> 1w ==> 64 <= LENGTH data) ==>
  ghost_inv_at D lo d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes))
    G2 tn2 (q with vs_inst_idx := s.vs_inst_idx + 3) /\
  ghost_kept_at lo cenv es sf G tn s G2 tn2 /\
  ptr_covers G2 tn2 dst (q with vs_inst_idx := s.vs_inst_idx + 3) (w2n rn) /\
  (!i. w2n wo <= i /\ i < w2n wo + w2n rn ==> i NOTIN tn2.t_mem) /\
  eval_operand (Var dst) (q with vs_inst_idx := s.vs_inst_idx + 3) = SOME wo /\
  q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n rn) data) s).vs_memory /\
  q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
  q.vs_immutables = s.vs_immutables /\
  (!x. not_fresh_at sm x ==> lookup_var x (q with vs_inst_idx := s.vs_inst_idx + 3) = lookup_var x s)
Proof
  strip_tac >>
  `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
      (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` by gvs[step_GAS] >>
  `venom_call_request u addr 0w wi an T = venom_call_request s addr 0w wi an T` by
    simp[update_var_def, venom_call_request_def, read_memory_def] >>
  `exec_ext_call ci u (HD (s.vs_gas_readings ++ [0w])) addr 0w wi an wo rn T =
    OK (update_var cv 1w ((write_memory_with_expansion (w2n wo)
       (TAKE (w2n rn) data) u) with
       <|vs_returndata := data; vs_outcomes := DROP 1 u.vs_outcomes|>))` by
    (irule computed_static_exec_success >> gvs[mk_inst_def, update_var_def]) >>
  `v = update_var cv 1w ((write_memory_with_expansion (w2n wo)
       (TAKE (w2n rn) data) u) with
       <|vs_returndata := data; vs_outcomes := DROP 1 u.vs_outcomes|>)` by
    (qpat_x_assum `step_inst_base ci u = OK v` mp_tac >>
     gvs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
          update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `q = v` by
    gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
        AllCaseEqs(), eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `q.vs_memory = (write_memory_with_expansion (w2n wo)
       (TAKE (w2n rn) data) s).vs_memory /\
   q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_immutables = s.vs_immutables /\ q.vs_returndata = data /\
   (!x. x <> gv /\ x <> cv ==> lookup_var x q = lookup_var x s)` by
    gvs[update_var_def, write_memory_with_expansion_def, lookup_var_def,
        FLOOKUP_UPDATE] >>
  `q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
   q.vs_transient = s.vs_transient /\
   tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
   tn2.t_mem = tn.t_mem DIFF
     {i | w2n wo <= i /\ i < w2n wo + MIN (w2n rn) (LENGTH data)} /\
   (!x. x <> gv /\ x <> cv ==> FLOOKUP G2 x = FLOOKUP G x /\
        op_taint tn2 (Var x) = op_taint tn (Var x))` by
    (drule_all suffix_same_endpoint_effects >> gvs[]) >>
  `!x. not_fresh_at sm x ==> FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x) /\ lookup_var x q = lookup_var x s` by
    metis_tac[] >>
  `tn2.t_mem SUBSET tn.t_mem` by (simp[SUBSET_DEF, IN_DIFF]) >>
  `ptr_covers G2 tn2 dst (q with vs_inst_idx := s.vs_inst_idx + 3) (w2n rn)` by
    (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sf G tn s G2 tn2` by
    (pure_rewrite_tac[ghost_kept_at_def] >>
     conj_tac >- (rpt strip_tac >>
       `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
       first_assum (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
     rpt conj_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `tn2.t_mem SUBSET tn.t_mem` mp_tac >>
     pure_rewrite_tac[SUBSET_DEF] >> disch_then irule >> asm_rewrite_tac[]) >>
  `!i. w2n wo <= i /\ i < w2n wo + w2n rn ==> i NOTIN tn2.t_mem` by
    suspend "clean" >>
  `!i. ~(w2n wo <= i /\ i < w2n wo + w2n rn) ==>
       mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mem_bytes_at_write_disjoint >>
     `LENGTH (TAKE (w2n rn) data) <= w2n rn` by simp[LENGTH_TAKE_EQ] >> gvs[]) >>
  `ghost_inv_at D lo d cenv cx
     (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2
     (q with vs_inst_idx := s.vs_inst_idx + 3)` by suspend "ghost" >>
  qpat_x_assum `eval_operand (Var dst) s = SOME wo`
    (assume_tac o REWRITE_RULE[eval_operand_def, lookup_var_def]) >>
  simp[eval_operand_def, lookup_var_def, write_memory_with_expansion_def,
       update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> metis_tac[]
QED

Resume precompile_suffix_ghost_output_at[clean]:
  markerLib.RESUME_TAC >> rpt gen_tac >>
  qpat_x_assum `tn2.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
  simp[IN_DIFF, GSPECIFICATION] >>
  qpat_x_assum `addr <> 1w ==> _` mp_tac >>
  simp[wordsTheory.dimword_def, wordsTheory.n2w_11] >>
  strip_tac >> simp[arithmeticTheory.MIN_DEF] >> decide_tac
QED

Resume precompile_suffix_ghost_output_at[ghost]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `q = v` kall_tac >>
  qpat_x_assum `v = _` kall_tac >>
  qpat_x_assum `u = _` kall_tac >>
  qpat_x_assum `G2 = _` kall_tac >>
  qpat_x_assum `tn2 = _` kall_tac >>
  `!x sz. not_fresh_at sm x ==>
    (ptr_covers G2 tn2 x q sz <=> ptr_covers G tn x s sz)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sm x ==> _`
       (drule_then strip_assume_tac) >> simp[ptr_covers_def]) >>
  `mem_bytes_at 0 lo q.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (simp[] >> irule mem_bytes_at_write_disjoint >> simp[]) >>
  qpat_x_assum `ghost_inv_at D lo d cenv cx es G tn s`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  pure_rewrite_tac[ghost_inv_at_def] >>
  (simp[NoAsms] >> conj_tac >- suspend "locals" >>
   conj_tac >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
     PairCases_on `x` >> fs[return_buf_ptr_def] >>
     simp[return_buf_ptr_def, lookup_var_def] >> metis_tac[lookup_var_def]) >>
   conj_tac >- (rpt strip_tac >> metis_tac[]) >>
   conj_tac >- (fs[stor_taint_ok_at_def] >> simp[stor_taint_ok_at_def]) >>
   conj_tac >- (rpt strip_tac >>
     `i IN tn.t_mem` by metis_tac[SUBSET_DEF] >>
     qpat_x_assum `mem_bytes_at 0 lo q.vs_memory = _`
       (fn th => rewrite_tac[th]) >> metis_tac[]) >>
   conj_tac >- (rpt strip_tac >> metis_tac[]) >>
   fs[allocas_from_def] >> metis_tac[])
QED

Resume precompile_suffix_ghost_output_at[locals]:
  markerLib.RESUME_TAC >> rpt gen_tac >> strip_tac >>
  `not_fresh_at sm p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qpat_assum `!x. not_fresh_at sm x ==> _` (drule_then strip_assume_tac) >>
  (conj_tac >- metis_tac[] >>
   rpt gen_tac >> strip_tac >>
   `lookup_var p s = SOME w` by fs[lookup_var_def] >>
   drule_all scoped_footprint_exterior >> strip_tac >>
   irule robust_val_in_memory_exterior_frame >>
   conj_tac >- simp[] >>
   qexistsl [`s.vs_memory`, `q.vs_memory`, `tn.t_mem`, `tn2.t_mem`,
     `{j | w2n wo <= j /\ j < w2n wo + w2n rn}`] >>
   simp[] >> (conj_tac >- metis_tac[] >>
     rpt strip_tac >> simp[arithmeticTheory.MIN_DEF] >> decide_tac))
QED

Finalise precompile_suffix_ghost_output_at
