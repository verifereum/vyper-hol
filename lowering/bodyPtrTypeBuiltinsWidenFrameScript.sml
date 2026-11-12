Theory bodyPtrTypeBuiltinsWidenFrame
Ancestors
  bodyPtrTypeBuiltinsWidenCopyShape exprSimConvertBytes exprSimAlloc
  exprSimBufferStore exprSimHash exprLoweringProps emitHelperProps
  loweringPosts exprLowering compileEnv loweringStateRelDefs venomState venomExecSemantics
  context fragExec

(* Normalize a supplied run to its concrete allocation/copy endpoint while
   retaining the allocation's frame. This lemma does not assert run existence. *)
Theorem widen_copy_run_frame_split:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a ==>
  ?mid u w p inst.
    op = Var p /\ t = mcopy (w2n w) (w2n a) n u /\
    stmt_state_rel ctx fn cenv cx es u /\
    lookup_var p u = SOME w /\ u.vs_memory = s.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,capacity) /\
    MEM inst (fn_insts fn) /\ inst.inst_id = sa.cs_next_id /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    ~not_fresh_at sa p /\ sa.cs_next_id < mid.cs_next_id /\
    mid.cs_next_id <= sb.cs_next_id /\
    (!z. not_fresh_at sa z ==> lookup_var z u = lookup_var z s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) capacity b len) /\
    (!name b len. local_region cenv es.scopes u name b len ==>
      regions_disjoint (w2n w) capacity b len)
Proof
  strip_tac >> drule_all convert_widen_copy_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa mid) s = OK u` >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x u = SOME a` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `n < dimword(:256)` by decide_tac >>
  `run_inst_seq (emitted_insts mid sb) u = OK (mcopy (w2n w) (w2n a) (w2n (n2w n : bytes32)) u)` by
    (irule buffer_emit_mcopy_run >> qexistsl_tac [`Var p`,`x`,`Lit (n2w n)`] >>
     gvs[eval_operand_def]) >>
  gvs[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (drule_all widen_copy_code_split >> strip_tac >>
     `sm = mid` by metis_tac[pairTheory.SND] >> simp[]) >>
  `t = mcopy (w2n w) (w2n a) n u` by
    (qpat_assum `run_inst_seq (emitted_insts sa mid) s = OK u`
       (mp_then Any mp_tac run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts mid sb` mp_tac) >> simp[] >>
     gvs[]) >>
  qexistsl_tac [`mid`,`u`,`w`,`inst`] >> fs[ci_mono_def, eval_operand_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem widen_copy_run_wb_frame:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a ==>
  wb_frame cenv es es sa s t
Proof
  strip_tac >> drule_all widen_copy_run_frame_split >> strip_tac >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >>
      simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
      metis_tac[lookup_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _` drule_all >>
      simp[regions_disjoint_def] >> strip_tac >>
      `mem_bytes_at off sz (mcopy (w2n w) (w2n a) n u).vs_memory =
       mem_bytes_at off sz u.vs_memory` by
        (irule buffer_mcopy_exterior >> decide_tac) >> simp[]) >>
  irule exprSimPropsTheory.locals_kept_regions >> rpt strip_tac >>
  `local_region cenv es.scopes u n' b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[]) >>
  qpat_x_assum `!name b len. _` drule_all >>
  simp[regions_disjoint_def] >> strip_tac >>
  `mem_bytes_at b sz (mcopy (w2n w) (w2n a) n u).vs_memory =
   mem_bytes_at b sz u.vs_memory` by
    (irule buffer_mcopy_exterior >> decide_tac) >> simp[]
QED

(* The widen copy writes only inside its own fresh allocation. *)
Theorem widen_copy_run_pure_frame[local]:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a ==>
  pure_frame cenv fn es sa s t
Proof
  strip_tac >> drule_all widen_copy_run_frame_split >> strip_tac >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  match_mp_tac exprSimPropsTheory.pure_frame_buffer_tail >>
  qexistsl_tac [`u`, `inst`, `w2n w`, `capacity`] >>
  rpt conj_tac
  >- (irule pure_frame_mem_eq >> first_assum ACCEPT_TAC)
  >- simp[mcopy_def, write_memory_with_expansion_def]
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- fs[]
  >- fs[mcopy_def, write_memory_with_expansion_def]
  >- (rpt strip_tac >> rename1 `local_region cenv es.scopes s nm lb lsz` >>
      `local_region cenv es.scopes u nm lb lsz` by
        (irule exprSimPropsTheory.local_region_frame_fwd >>
         qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[] >>
         rpt strip_tac >> metis_tac[]) >>
      qpat_x_assum `!name b len. local_region _ _ u _ _ _ ==> _` drule >>
      simp[]) >>
  rpt gen_tac >> simp[regions_disjoint_def] >> strip_tac >>
  qpat_x_assum `u.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
  irule buffer_mcopy_exterior >> decide_tac
QED

Theorem widen_copy_run_allocation_frame:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a ==>
  ?w. eval_operand op t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,capacity) /\
    sa.cs_next_id < sb.cs_next_id /\ stmt_state_rel ctx fn cenv cx es t /\
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      w2n w + capacity <= b \/ b + sz <= w2n w)
Proof
  strip_tac >> drule_all widen_copy_run_frame_split >> strip_tac >>
  `not_local_ptr cenv es.scopes p` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_state_rel ctx fn cenv cx es (mcopy (w2n w) (w2n a) n u)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`capacity`,`inst`,`p`] >> simp[]) >>
  qexists_tac `w` >> fs[lookup_var_def] >>
  simp[mcopy_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  rpt strip_tac >>
  `local_region cenv es.scopes u name b sz` by
    (fs[local_region_def, mcopy_def, write_memory_with_expansion_def, lookup_var_def]) >>
  qpat_x_assum `!name b len. _` drule_all >> simp[regions_disjoint_def]
QED

Theorem widen_copy_run_parent_post:
  compile_bytestring_widen_copy capacity x n sa = (op,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  fn_has_code sa sb fn /\ 0 < n /\ n <= capacity /\ capacity < dimword(:256) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ (!z. x = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME a /\ ~is_word_type (expr_type e) /\
  post_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= capacity /\
  (!w. eval_operand op t = SOME w ==> val_in_memory tv v (w2n w) t.vs_memory) ==>
  expr_post ctx fn cenv cx e es sa sb s es v op t
Proof
  strip_tac >> drule_all widen_copy_run_allocation_frame >> strip_tac >>
  `wb_frame cenv es es sa s t` by (irule widen_copy_run_wb_frame >> metis_tac[]) >>
  `pure_frame cenv fn es sa s t` by
    (irule widen_copy_run_pure_frame >> metis_tac[]) >>
  irule convert_buffer_expr_post >> simp[] >>
  gvs[]
QED
