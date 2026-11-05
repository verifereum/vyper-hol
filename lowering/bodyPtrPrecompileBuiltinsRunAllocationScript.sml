Theory bodyPtrPrecompileBuiltinsRunAllocation
Ancestors bodyPtrPrecompileBuiltinsAllocationFrame allocationPtr
          bodyPtrPrecompileBuiltinsPrefixFrames exprLoweringProps
          venomMemDefs loweringPosts vyperValue vyperTyping valueEncoding
          ptrDiscipline compileEnv venomState venomInst venomExecSemantics
          finite_map pred_set fragExec context

Theorem new_site_bytes_range_exterior:
  t.vs_fmp = s.vs_fmp /\
  (!aid b sz. aid NOTIN FDOM s.vs_allocas /\
    FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint off len b sz) ==>
  !i. off <= i /\ i < off + len ==> i NOTIN new_site_bytes s t
Proof
  simp[new_site_bytes_def] >> rpt strip_tac >>
  Cases_on `aid IN FDOM s.vs_allocas` >> simp[] >>
  first_x_assum drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem alloca_new_site_bytes_contained:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  eval_operand (Var out) t = SOME w /\
  n < dimword(:256) /\ s.vs_alloca_next < dimword(:256) ==>
  new_site_bytes s t SUBSET {i | w2n w <= i /\ i < w2n w + n}
Proof
  pure_once_rewrite_tac[step_inst_base_def] >>
  simp[mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (strip_tac >> gvs[update_var_def, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE] >>
      simp[new_site_bytes_def, SUBSET_DEF, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[AllCaseEqs(), FLOOKUP_DEF] >> decide_tac) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  strip_tac >> gvs[update_var_def, eval_operand_def, lookup_var_def,
    FLOOKUP_UPDATE, new_site_bytes_def, FLOOKUP_DEF, SUBSET_DEF] >>
  rpt strip_tac >> gvs[]
QED

Theorem emitted_allocation_step:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t
Proof
  strip_tac >> drule emitted_allocation_singleton >> strip_tac >>
  Cases_on `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s` >> gvs[run_inst_seq_def]
QED

Theorem emitted_allocation_new_bytes_contained:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  eval_operand buf.buf_operand t = SOME w /\
  n < dimword(:256) /\ s.vs_alloca_next < dimword(:256) ==>
  new_site_bytes s t SUBSET {i | w2n w <= i /\ i < w2n w + n}
Proof
  strip_tac >> drule_all emitted_allocation_step >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  irule alloca_new_site_bytes_contained >> metis_tac[]
QED

(* Only allocation-growth bytes lie above the frontier; reused scratch
   addresses need not.  This boundary excludes growth, not scratch writes. *)
Theorem emitted_allocation_growth_exterior:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  off + len <= s.vs_alloca_next ==>
  !i. off <= i /\ i < off + len ==> i NOTIN new_site_bytes s t
Proof
  strip_tac >> drule_all emitted_allocation_step >> strip_tac >>
  rpt strip_tac >>
  `s.vs_alloca_next <= i` by
    (qpat_assum `step_inst_base _ s = OK t`
       (mp_then Any mp_tac staging_alloca_footprint_above_frontier) >>
     simp[mk_inst_def] >> disch_then irule >> simp[]) >> decide_tac
QED

Theorem emitted_allocation_old_region_exterior:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  alloca_next_valid s /\ FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
  !i. off <= i /\ i < off + len ==> i NOTIN new_site_bytes s t
Proof
  strip_tac >>
  `off + len <= s.vs_alloca_next` by
    (gvs[alloca_next_valid_def] >> first_x_assum drule >> decide_tac) >>
  metis_tac[emitted_allocation_growth_exterior]
QED

Theorem emitted_allocation_value_exterior:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx ty lo sf es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    i NOTIN new_site_bytes s t
Proof
  strip_tac >> drule_all emitted_allocation_step >> strip_tac >>
  rpt strip_tac >>
  `i < s.vs_alloca_next` by metis_tac[expr_val_at_below_frontier] >>
  `s.vs_alloca_next <= i` by
    (qpat_assum `step_inst_base _ s = OK t`
       (mp_then Any mp_tac staging_alloca_footprint_above_frontier) >>
     simp[mk_inst_def] >> disch_then irule >> simp[]) >> decide_tac
QED

Theorem emitted_allocation_point_exterior:
  compile_alloc_buffer n sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx fn cenv cx es s /\
  expr_val_at cenv cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) lo sf es v op s /\
  eval_operand op s = SOME w ==>
  !i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN new_site_bytes s t
Proof
  strip_tac >>
  `val_footprint (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v = 64` by
    (Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]) >>
  `evaluate_type (get_tenv cx) (ArrayT (BaseT (UintT 256)) (Fixed 2)) =
    SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) /\
   ~is_word_type (ArrayT (BaseT (UintT 256)) (Fixed 2))` by
    simp[evaluate_type_def, is_word_type_def, type_slot_size_def, wordsTheory.dimword_def] >>
  metis_tac[emitted_allocation_value_exterior]
QED
