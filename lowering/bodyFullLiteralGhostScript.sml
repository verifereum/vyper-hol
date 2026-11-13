Theory bodyFullLiteralGhost
Ancestors
  bodyFullLiteralBuffer bodyPtrDefs robustCopyTransportPtr
  exprSimLiteralBuffer exprSimPtrLiteralBuffer ptrSafetyTransport loweringStateRelDefs
  localPtrsProps valueEncodingProofs finite_map pred_set words
  ptrDiscipline venomState loweringPosts venomExecSemantics venomInst
  exprSimPtrLiteralPayload exprLoweringProps list

Theorem literal_bytelike_full_ghost_post:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  stmt_state_rel H ctx func cenv cx es u /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
    lookup_var x t = lookup_var x u /\ FLOOKUP G' x = FLOOKUP G x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
  (!name a len. local_region cenv es.scopes u name a len ==>
    regions_disjoint b (32+32*word_size (LENGTH bs)) a len) /\
  u.vs_memory = s.vs_memory /\ lo <= b /\
  (!a len. a+len <= b \/ b+32+32*word_size (LENGTH bs) <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
  tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at D lo d cenv cx es G' tn'
    (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ghost_kept_at lo cenv es sa G tn s G' tn'
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
       FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (simp[op_taint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (simp[ghost_kept_at_def] >> SET_TAC[]) >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
       ptr_covers G' tn' x t sz` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_x_assum `!a len. _ ==> _` (qspecl_then [`0`, `lo`] mp_tac) >> simp[]) >>
  fs[ghost_inv_at_def, stor_taint_ok_at_def, allocas_from_def,
     lookup_var_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac
      >- (`ptr_covers G' tn' p t sz` by metis_tac[] >>
          qpat_x_assum `ptr_covers G' tn' p t sz` mp_tac >>
          simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def]) >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p u = SOME w` by metis_tac[lookup_var_def] >>
      drule_all literal_ptr_local_footprint_exterior >> strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`,
        `tn'.t_mem`, `{i | b <= i /\ i < b+32*word_size (LENGTH bs)+32}`] >>
      asm_simp_tac (srw_ss()) [] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (simp_tac (srw_ss() ++ ARITH_ss) []) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!a len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
            (qspecl_then [`i`, `1`] mp_tac) >>
          asm_simp_tac (srw_ss()) [] >> (impl_tac >- decide_tac) >> simp_tac bool_ss []) >>
      asm_simp_tac (srw_ss() ++ ARITH_ss) [] >>
      qpat_x_assum `!i. _ ==> i NOTIN _` mp_tac >>
      simp_tac (srw_ss()) [])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >>
      `not_fresh_at sa x` by metis_tac[] >>
      `ptr_covers G' tn' x t bc1` by metis_tac[] >>
      conj_tac
      >- (simp_tac (srw_ss()) [lookup_var_def] >> metis_tac[lookup_var_def]) >>
      qpat_x_assum `ptr_covers G' tn' x t bc1` mp_tac >>
      simp_tac (srw_ss()) [ptr_covers_def, lookup_var_def]) >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem literal_bytelike_full_run_allocas_from:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (irule step_inst_allocas_from >>
     qexistsl_tac [`ctx`, `0`, `mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]`, `s`] >>
     simp[step_inst_non_invoke, mk_inst_def]) >>
  `run_inst_seq (mk_inst sm.cs_next_id MSTORE
      [Var p; Lit (n2w (LENGTH bs))] [] :: emitted_insts sh sb) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     pure_asm_rewrite_tac [APPEND] >>
     once_rewrite_tac [run_inst_seq_def] >>
     gvs[mk_inst_def, is_terminator_def] >>
     simp[run_inst_seq_def, is_terminator_def]) >>
  `lookup_var p u = SOME (n2w (w2n w))` by
    gvs[eval_operand_def, wordsTheory.n2w_w2n] >>
  `w2n w+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = u` mp_tac >>
  simp[Once venom_state_component_equality] >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED
