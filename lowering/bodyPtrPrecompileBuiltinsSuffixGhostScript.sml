Theory bodyPtrPrecompileBuiltinsSuffixGhost
Ancestors bodyPtrPrecompileBuiltinsEmittedSuffix decoderGhostFramePtr
          bodyPtrPrecompileBuiltinsSuffix fragGasSeqPtr instIdxIndep
          venomInst venomState venomExecSemantics ptrDiscipline
          ghostPcTransportPtr bodyPtrDefs finite_map context pred_set
          robustCopyTransportPtr compileEnv valueEncoding loweringPosts

Theorem suffix_final_ghost:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s G' tn' ==>
  G' = step_prov PG (step_prov PG G gi u) ci v /\
  tn' = step_taint ci u v (step_taint gi s u tn)
Proof
  strip_tac >>
  `~is_terminator ci.inst_opcode /\
   ~is_terminator ai.inst_opcode` by simp[mk_inst_def, is_terminator_def] >>
  qpat_x_assum `gi = _` kall_tac >>
  qpat_x_assum `ci = _` kall_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[inst_seq_ptr_def, step_inst_inst_idx_indep, exec_result_map_def] >>
  qpat_x_assum `ai = _` SUBST_ALL_TAC >>
  Cases_on `eval_operand (Var cv) v`
  >- (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_result_map_def] >>
      metis_tac[]) >>
  rename1 `eval_operand (Var cv) v = SOME w` >>
  Cases_on `w = 0w` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_result_map_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[assert_step_ghost] >> metis_tac[]
QED

Theorem suffix_old_variable:
  gi.inst_outputs = [gv] /\ ci.inst_outputs = [cv] /\
  x <> gv /\ x <> cv /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  FLOOKUP G2 x = FLOOKUP G x /\
  op_taint tn2 (Var x) = op_taint tn (Var x)
Proof
  strip_tac >>
  `~MEM x gi.inst_outputs /\ ~MEM x ci.inst_outputs` by simp[] >>
  gvs[step_prov_other_output, step_taint_other_output]
QED

Theorem suffix_ptr_covers:
  gi.inst_outputs = [gv] /\ ci.inst_outputs = [cv] /\
  x <> gv /\ x <> cv /\ lookup_var x v = lookup_var x s /\
  ptr_covers G tn x s sz /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  ptr_covers G2 tn2 x v sz
Proof
  strip_tac >> drule_all suffix_old_variable >> strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_covers_def]
QED

Theorem ghost_kept_memory_subset:
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[bodyPtrDefsTheory.ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ghost_kept_subset_trans:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[bodyPtrDefsTheory.ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem suffix_memory_taint:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  step_inst_base gi s = OK u /\
  eval_operand (Var gv) u = SOME gas /\
  eval_operand (Var src) u = SOME wi /\
  eval_operand (Var dst) u = SOME wo /\
  v.vs_allocas = u.vs_allocas /\ v.vs_fmp = u.vs_fmp /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  tn2.t_mem = tn.t_mem DIFF
    {i | w2n wo <= i /\ i < w2n wo + MIN (w2n rn) (LENGTH v.vs_returndata)}
Proof
  strip_tac >>
  `step_taint gi s u tn = tn with t_var := tn.t_var |+ (gv,{})` by
    metis_tac[gas_step_taint] >>
  drule_all bodyPtrPrecompileBuiltinsBoundaryTheory.staticcall_mem_taint >>
  simp[]
QED

Theorem suffix_memory_subset:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  step_inst_base gi s = OK u /\
  eval_operand (Var gv) u = SOME gas /\
  eval_operand (Var src) u = SOME wi /\
  eval_operand (Var dst) u = SOME wo /\
  v.vs_allocas = u.vs_allocas /\ v.vs_fmp = u.vs_fmp /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  tn2.t_mem SUBSET tn.t_mem
Proof
  strip_tac >> drule_all suffix_memory_taint >> SET_TAC[]
QED

Theorem ghost_inv_exterior_frame:
  ghost_inv d cenv cx es G tn s /\
  (!p sz. ((?name. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)) \/
            cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
            cenv.ce_return_pc = SOME (PtrVar (Var p) sz)) ==>
     FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p) /\
     lookup_var p t = lookup_var p s) /\
  (!name entry p sz w.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
     lookup_var p s = SOME w ==>
     val_wf entry.type entry.value /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
          i NOTIN writes)) /\
  (!i. i NOTIN writes ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!i. i NOTIN writes ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' t
Proof
  strip_tac >>
  gvs[ghost_inv_def, stor_taint_ok_def] >>
  conj_tac
  >- (rpt strip_tac
      >- (gvs[ptr_covers_def] >> metis_tac[]) >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
            i NOTIN writes)` by metis_tac[] >>
      irule robustCopyTransportPtrTheory.robust_val_in_memory_exterior_frame >>
      simp[] >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`, `writes`] >>
      metis_tac[]) >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem computed_static_state_frame:
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  inst.inst_outputs = [out] /\
  exec_ext_call inst s gas addr 0w wi an ro rn T = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\
  (!x. x <> out ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule_all bodyPtrPrecompileBuiltinsRuntimeTheory.computed_static_exec_eq >>
  strip_tac >> gvs[update_var_def, write_memory_with_expansion_def,
                   lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem suffix_ghost_kept:
  gi.inst_outputs = [gv] /\ ci.inst_outputs = [cv] /\
  ~not_fresh_at sa gv /\ ~not_fresh_at sa cv /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) /\
  tn2.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G tn s G2 tn2
Proof
  strip_tac >> irule ghost_kept_memory_subset >> simp[] >>
  rpt strip_tac >> metis_tac[suffix_old_variable]
QED

Theorem returned_prefix_clean:
  tn2.t_mem = tn.t_mem DIFF
    {i | (off:num) <= i /\ i < off + MIN cap len} /\
  (!i. off + MIN cap len <= i /\ i < off + cap ==> i NOTIN tn.t_mem) ==>
  !i. off <= i /\ i < off + cap ==> i NOTIN tn2.t_mem
Proof
  simp[IN_DIFF] >> rpt strip_tac >>
  Cases_on `i < off + MIN cap len` >> gvs[]
QED

Theorem suffix_checked_ghost:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  (?G' tn'. inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s G' tn') ==>
  inst_seq_ptr D lo ctx fn PG G tn [gi;ci;ai] s
    (step_prov PG (step_prov PG G gi u) ci v)
    (step_taint ci u v (step_taint gi s u tn))
Proof
  strip_tac >> drule_all suffix_final_ghost >> strip_tac >> gvs[]
QED
