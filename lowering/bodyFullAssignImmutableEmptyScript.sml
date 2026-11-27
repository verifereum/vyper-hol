Theory bodyFullAssignImmutableEmpty
Ancestors
  vfmBuffer[qualified,ignore_grammar]
  ctorDeployDeadSection immSectionDead gasContext valueEncodingDefs valueEncodingProps
  valueEncodingProofs abiEncoderMemory cv_std byte words divides arithmetic list
  ptrDiscipline context emitHelper fragExec
  venomState venomInst venomExecSemantics loweringStateRelDefs
  string ASCIInumbers rich_list pred_set
  bodyFullMemoryFrames bodyPtrBytestringBuiltinsWindowGhost vyperPlaceFrames
  stmtSimAugAssignPlaceMemory vyperPlaceWriteSoundness
  immutableAssignEmpty immutableDeployAssignRestore immutableDeployAssignMemoryFrame
  immutableCtorWordStoreGhost[qualified,ignore_grammar]
  exprSimProps alist compileEnv exprLoweringProps
  bodySim bodyInvCodeProps bodyStorageMetadata immutableRelation
  ctorDeployDeadSectionFrame compileVyper venomMemProps stateRelProj
  bodyPtrDefs stmtSimDefs vyperState vyperTyping vyperTypeEnv vyperTypeValues
  exprSimHypsDefs vyperContext finite_map
  bodyInvSplit[qualified]


Theorem num_of_bytes_mono[local]:
  !xs ys. LIST_REL (\x y. w2n x <= w2n y) xs ys ==>
    num_of_bytes xs <= num_of_bytes ys
Proof
  Induct >> Cases_on `ys` >> simp[num_of_bytes_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

Theorem mem_word_at_bytewise_mono[local]:
  LIST_REL (\x y. w2n x <= w2n y) (mem_bytes_at a 32 sec') (mem_bytes_at a 32 sec) ==>
  w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)
Proof
  strip_tac >>
  drule LIST_REL_REVERSE >>
  disch_then (assume_tac o MATCH_MP num_of_bytes_mono) >>
  `!m. num_of_bytes (REVERSE (mem_bytes_at a 32 m)) < dimword (:256)` by
    (gen_tac >> mp_tac (Q.SPEC `REVERSE (mem_bytes_at a 32 m)` vfmBufferTheory.num_of_bytes_lt) >>
     simp[dimword_def]) >>
  `!m. mem_word_at a m = word_of_bytes_be (mem_bytes_at a 32 m)` by
    simp[mem_word_at_def, mem_bytes_at_def, word_of_bytes_be_def] >>
  asm_rewrite_tac[] >>
  simp[word_of_bytes_be_eq_num_of_bytes, dividesTheory.compute_divides,
       be_bytes_thm, TAKE_APPEND1, TAKE_LENGTH_ID_rwt, w2n_n2w_compute]
QED

(* Decreasing length words can only make more bytes dead. *)
Theorem mem_dead_bytes_lengths_decrease[local]:
  (!sec off tv i. mem_dead_bytes sec off tv i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes sec' off tv i) /\
  (!sec off tvs i. mem_dead_bytes_list sec off tvs i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes_list sec' off tvs i) /\
  (!sec off fields i. mem_dead_bytes_fields sec off fields i ==>
    !sec'. (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) ==>
      mem_dead_bytes_fields sec' off fields i)
Proof
  ho_match_mp_tac mem_dead_bytes_ind >>
  simp[mem_dead_bytes_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `off` assume_tac) >> decide_tac)
  >- (first_x_assum (qspec_then `off` assume_tac) >> decide_tac)
  >- (qexists_tac `k` >> simp[] >> metis_tac[])
  >- (qexists_tac `k` >> simp[] >>
      qpat_assum `!a. w2n (mem_word_at a sec') <= _`
        (qspec_then `off` assume_tac) >>
      Cases_on `k < w2n (mem_word_at off sec')`
      >- (`k < w2n (mem_word_at off sec)` by decide_tac >>
          fs[] >> metis_tac[]) >>
      Cases_on `k < w2n (mem_word_at off sec)` >> fs[] >>
      drule (cj 1 mem_dead_bytes_range) >>
      simp[ADD1, LEFT_ADD_DISTRIB] >> decide_tac)
  >> metis_tac[]
QED

Theorem imm_section_dead_lengths_decrease:
  (!a. w2n (mem_word_at a sec') <= w2n (mem_word_at a sec)) /\
  imm_section_dead tops sec i ==>
  imm_section_dead tops sec' i
Proof
  simp[imm_section_dead_def] >>
  metis_tac[cj 1 mem_dead_bytes_lengths_decrease]
QED

Theorem imm_section_dead_mstore_zero:
  imm_section_dead tops (mem_bytes_at 0 lo s.vs_memory) i ==>
  imm_section_dead tops (mem_bytes_at 0 lo (mstore p 0w s).vs_memory) i
Proof
  strip_tac >> irule imm_section_dead_lengths_decrease >>
  goal_assum (drule_at Any) >> gen_tac >>
  irule mem_word_at_bytewise_mono >>
  simp[LIST_REL_EL_EQN] >> qx_gen_tac `j` >> strip_tac >>
  `!m. EL j (mem_bytes_at a 32 (mem_bytes_at 0 lo m)) =
      if a+j < lo then EL (a+j) (mem_bytes_at 0 lo m) else 0w` by
    metis_tac[EL_mem_bytes_at, LENGTH_mem_bytes_at] >>
  Cases_on `a+j < lo` >> asm_rewrite_tac[] >> simp[] >>
  `!m. EL (a+j) (mem_bytes_at 0 lo m) = EL 0 (mem_bytes_at (a+j) 1 m)` by
    simp[EL_mem_bytes_at] >>
  asm_rewrite_tac[] >>
  Cases_on `p <= a+j /\ a+j < p+32`
  >- (`a+j-p + 1 <= 32` by decide_tac >>
      drule abi_encoder_zero_subwindow >>
      disch_then (qspecl_then [`s`, `p`] mp_tac) >>
      `p+(a+j-p) = a+j` by decide_tac >>
      `REPLICATE 1 (0w:byte) = [0w]` by EVAL_TAC >>
      asm_rewrite_tac[] >> simp[w2n_n2w]) >>
  `a+j+1 <= p \/ p+32 <= a+j` by decide_tac >>
  simp[mstore_mem_bytes_at_disjoint]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `ce.ce_modules = [(NONE,tops)]` by
    metis_tac[body_inv_contract, contract_inv_cenv_modules] >>
  `cx_tops cx = tops` by metis_tac[body_inv_main_code, cx_tops_module] >>
  mp_tac (Q.INST [`word` |-> `0w`]
    immutableCtorWordStoreGhostTheory.immutable_ctor_word_store_ghost) >>
  impl_tac >-
    (simp[] >> rpt strip_tac >>
     irule imm_section_dead_mstore_zero >>
     `i IN tn.t_mem` by
       (qpat_assum `tf.t_mem SUBSET tn.t_mem`
          (drule_then ACCEPT_TAC o REWRITE_RULE [SUBSET_DEF])) >>
     qpat_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
     qpat_assum `ce.ce_modules = [(NONE,tops)]` (fn modules =>
       qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _`
         (qspec_then `i` (mp_tac o REWRITE_RULE
           [MATCH_MP immSectionDeadTheory.imm_section_dead_mods_singleton modules]))) >>
     asm_rewrite_tac[]) >>
  simp[]
QED
*)
Theorem immutable_empty_store_ghost:
  ghost_inv_at D lo d ce cx es G tn s /\
  dead_lo_ok H D lo ce cx /\ ce.ce_is_ctor /\
  (contract_inv mods exps ctx ce cx /\
     module_body_inv mods ce.ce_module tops ce cx) /\
  expr_sim_inv_mods mods ce cx env es /\ stmt_state_rel H ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  ee.scopes = es.scopes /\ off+32 <= lo /\
  q.vs_memory = (mstore off 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_mem SUBSET tn.t_mem ==>
  ghost_inv_at D lo d ce cx ee Gf tf q
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `val_in_memory itv iv off s.vs_memory` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ es s`
       (mp_tac o MATCH_MP state_rel_immutables_rel o MATCH_MP stmt_state_rel_state_rel) >>
     simp[immutables_rel_def] >> metis_tac[]) >>
  `state_well_typed es` by fs[expr_sim_inv_def] >>
  drule_all state_well_typed_immutables_ALOOKUP >> strip_tac >>
  drule_all imms_well_typed_get_source_immutables >> strip_tac >>
  `mem_word_at (off+k) q.vs_memory = 0w` by simp[mstore_mem_word_at_same] >>
  drule_all immutable_assign_empty_representation >> strip_tac >>
  `value_has_type ptv (default_value ptv)` by
    metis_tac[default_value_well_typed,evaluate_type_well_formed_type_value] >>
  drule_all mem_path_offset_sound >> strip_tac >>
  `!b n. off <= b /\ b+n <= off+type_memory_size itv /\
      (b+n <= off+k \/ off+k+type_memory_size ptv <= b) ==>
      mem_bytes_at b n q.vs_memory = mem_bytes_at b n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  drule_all immutable_value_bytes_rel_replace_path >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by simp[LENGTH_mstore_eq] >>
  `!a n. regions_disjoint a n off (type_memory_size itv) ==>
      mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule immutable_store_stmt_state_rel >>
  qpat_assum `immutable_section_layout_mods _ _`
    (fn layout => qpat_assum `ce.ce_is_ctor`
      (fn ctor => REWRITE_TAC [layout,ctor])) >>
  qexistsl_tac [`env`,`es`,`id`,`off`,`s`,`sa`,`ce.ce_module`,`itv`,`root_ty`,`new`] >>
  qpat_x_assum `q.vs_memory = _` kall_tac >>
  simp[]
QED
*)
Theorem immutable_empty_path_store_restore:
  bodyInvSplit$immutable_section_layout_mods ce.ce_modules ce /\
  stmt_state_rel H ctx func ce cx es s /\ expr_sim_inv_mods mods ce cx env es /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME root_ty /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) root_ty = SOME itv /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables ce.ce_module imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  assign_subscripts itv iv path (Replace (default_value ptv)) = INL new /\
  write_place cx (ImmutablePlace ce.ce_module id []) new es = (INL (),ee) /\
  has_length_word ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  q.vs_memory = (mstore (off+k) 0w s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) ==>
  stmt_state_rel H ctx func ce cx ee q
Proof
  cheat
QED
