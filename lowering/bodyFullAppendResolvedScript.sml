(* Resolved memory Append in the joint execution and ghost judgment. *)
Theory bodyFullAppendResolved
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFullCompose
  bodyFullMemoryFrames bodyAppendResolvedPre appendMemoryRel appendMemoryPtr
  bodyNameMemoryFacts representationCleanPtr appendMemoryPath
  normalizationPrefixPtr robustCopyTransportPtr exprSimAggregateEncoding
  exprSimHypsDefs exprSimDefs exprSimSource exprSimProps loweringPosts
  bodyPtrDefs supportedTypes valueEncoding valueEncodingProps valueEncodingDefs
  vyperValue vyperTyping vyperAST vyperState venomState finite_map list words arithmetic

Theorem append_local_word_ghost_inputs[local]:
  expr_sim_pre ce cx env (Name (ArrayT elem (Dynamic cap)) id) es /\
  supported_full_word_type elem /\ stmt_state_rel H ctx func ce cx es s /\
  ghost_inv_at D lo d ce cx es G tn s ==>
  ?entry p sz bp tv vs.
    lookup_scopes id es.scopes = SOME entry /\
    entry.type = ArrayTV tv (Dynamic cap) /\
    entry.value = ArrayV (DynArrayV vs) /\
    evaluate_type (get_tenv cx) elem = SOME tv /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME bp /\ type_memory_size tv = 32 /\
    ptr_covers G tn p s (32*(1+cap)) /\
    (!i. w2n bp <= i /\ i < w2n bp+32 ==> i NOTIN tn.t_mem) /\
    w2n bp+32*(1+cap) <= s.vs_alloca_next
Proof
  strip_tac >> drule_all body_name_source_region >> strip_tac >>
  `?tv. evaluate_type (get_tenv cx) elem = SOME tv /\
        entry.type = ArrayTV tv (Dynamic cap)` by
    gvs[evaluate_type_def, AllCaseEqs()] >>
  `?vs. entry.value = ArrayV (DynArrayV vs)` by
    (qpat_x_assum `value_has_type entry.type entry.value` mp_tac >>
     simp[] >> Cases_on `entry.value` >> simp[value_has_type_def] >>
     rename1 `ArrayV arr` >> Cases_on `arr` >> simp[value_has_type_def]) >>
  `type_memory_size tv = 32` by
    (qpat_x_assum `supported_full_word_type elem` mp_tac >>
     rw[supported_full_word_type_def] >>
     fs[evaluate_type_def, type_memory_size_def]) >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    mem_word_at (w2n w) mem = n2w (LENGTH vs)` by
    (rpt strip_tac >> first_x_assum drule >> simp[val_in_memory_def]) >>
  drule robust_mem_word_at_clean >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `sz`, `w`, `tv`, `vs`] >>
  simp[] >> conj_tac
  >- (gvs[ptr_covers_def, type_memory_size_def] >> metis_tac[LESS_EQ_TRANS]) >>
  gvs[type_memory_size_def] >> decide_tac
QED

Theorem append_local_word_robust_array[local]:
  (!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem) /\
  (!j. j < LENGTH vs ==> val_wf tv (EL j vs)) /\ type_memory_size tv = 32 /\
  mem_word_at off new_memory = n2w (LENGTH vs+1) /\
  DISJOINT {i | off <= i /\ i < off+32} new_taint /\
  (!mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory tv v (off+32*(1+LENGTH vs)) mem) /\
  (!i. ~(off <= i /\ i < off+32) /\
       ~(off+32*(1+LENGTH vs) <= i /\
         i < off+32*(1+LENGTH vs)+32) ==>
    mem_bytes_at i 1 new_memory = mem_bytes_at i 1 old_memory /\
    (i IN new_taint <=> i IN old_taint)) ==>
  !mem. mem_agree_outside new_taint new_memory mem ==>
    val_in_memory (ArrayTV tv (Dynamic cap))
      (ArrayV (DynArrayV (vs ++ [v]))) off mem
Proof
  strip_tac >> match_mp_tac robust_dynarray_clean_count_assemble >>
  simp[LENGTH_APPEND] >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = LENGTH vs`
  >- (qpat_x_assum `j = LENGTH vs` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [EL_APPEND_EQN] >>
      qpat_assum `!mem. mem_agree_outside new_taint new_memory mem ==> _` mp_tac >>
      simp_tac (srw_ss()) [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB, ADD_ASSOC, ADD_COMM]) >>
  `j < LENGTH vs` by decide_tac >>
  `val_wf tv (EL j vs)` by metis_tac[] >>
  `val_footprint tv (EL j vs) <= 32` by metis_tac[val_footprint_le] >>
  `!mem. mem_agree_outside old_taint old_memory mem ==>
    val_in_memory tv (EL j vs) (off+32+j*32) mem` by
    (rpt strip_tac >>
     `val_in_memory (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) off mem` by
       metis_tac[] >>
     `elems_in_memory vs (off+32) tv mem` by
       (qpat_assum `val_in_memory (ArrayTV tv (Dynamic cap))
          (ArrayV (DynArrayV vs)) off mem`
          (strip_assume_tac o PURE_ONCE_REWRITE_RULE [val_in_memory_def]) >>
        fs[]) >>
     qspecl_then [`vs`, `off+32`, `tv`, `mem`, `j`] mp_tac elems_in_memory_EL >>
     simp[]) >>
  simp[EL_APPEND_EQN] >>
  match_mp_tac (Q.SPECL [`old_taint`, `new_taint`, `old_memory`, `new_memory`,
    `{i | off <= i /\ i < off+32} UNION
     {i | off+32*(1+LENGTH (vs:value list)) <= i /\
          i < off+32*(1+LENGTH vs)+32}`, `tv`, `EL j vs`,
     `32*j+(off+32)`] robust_val_in_memory_exterior_frame) >>
  simp[] >>
  qpat_x_assum `!mem. mem_agree_outside old_taint old_memory mem ==> _`
    (ACCEPT_TAC o PURE_REWRITE_RULE
      [DECIDE ``off+32+j*32 = 32*j+(off+32)``])
QED

Theorem body_append_local_word_full:
  !cx id e.
    supported_full_word_type (expr_type e) /\
    (!s0 p s1. eval_target_place cx (NameTarget id) s0 = (INL p,s1) ==>
                  body_expr_full_ok cx e) ==>
    body_stmt_full_ok cx (Append (NameTarget id) e)
Proof
  rpt strip_tac >> rw[body_stmt_full_ok_def] >>
  rw[stmt_frag_full_def] >> all_tac
QED
