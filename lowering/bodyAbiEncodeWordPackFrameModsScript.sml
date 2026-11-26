(* Lift a fixed ABI word-pack endpoint to the linked ghost and frame. *)
Theory bodyAbiEncodeWordPackFrameMods
Ancestors
  bodyMethodIdScratchFrameMods bodyPtrBytestringBuiltinsWindowGhost
  bodyShaRegisteredFrameMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvSplit stateRelProj loweringStateRelDefs ptrDiscipline
  compileEnv venomState finite_map alist pred_set

Theorem abi_encode_word_pack_frame_mods:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  immutable_frame_mods func ce cx ee s /\
  stmt_state_rel H ctx func ce cx ee s /\
  local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
           not_fresh_at st x) /\
  (!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==>
       not_fresh_at st x) /\
  pure_frame ce func ee st s z /\
  lo <= p /\
  (!a n. a + n <= p \/ p + cap <= a ==>
       mem_bytes_at a n z.vs_memory = mem_bytes_at a n s.vs_memory) /\
  (!name b n. local_region ce ee.scopes s name b n ==>
       p + cap <= b \/ b + n <= p) /\
  (!name b n. local_region ce ee.scopes s name b n ==>
       mem_bytes_at b n z.vs_memory = mem_bytes_at b n s.vs_memory /\
       (!i. b <= i /\ i < b + n /\ i IN tz.t_mem ==> i IN tn.t_mem)) /\
  (!x. not_fresh_at st x ==>
       lookup_var x z = lookup_var x s /\
       FLOOKUP Gz x = FLOOKUP G x /\
       op_taint tz (Var x) = op_taint tn (Var x)) /\
  (!i. i < s.vs_alloca_next /\ i IN tz.t_mem ==> i IN tn.t_mem) /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a k. FLOOKUP z.vs_allocas aid = SOME (a,k) ==>
       FLOOKUP s.vs_allocas aid = SOME (a,k) \/
       s.vs_alloca_next <= a) /\
  z.vs_call_ctx = s.vs_call_ctx /\
  z.vs_accounts = s.vs_accounts /\
  z.vs_transient = s.vs_transient /\
  z.vs_immutables = s.vs_immutables /\
  tz.t_stor = tn.t_stor /\
  tz.t_trans = tn.t_trans /\
  tz.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d ce cx ee Gz tz z /\
  immutable_frame_mods func ce cx ee z
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx ee G tn s` by
    (irule bodyMethodIdScratchFrameModsTheory.method_id_ghost_at_zero >>
     qexists_tac `lo` >> first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func ce ee.scopes s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `stor_taint_ok_at D tz z` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP (cj 4 (iffLR ghost_inv_at_mods_def))) >>
     simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
  `allocas_from 0 z` by simp[ptrDisciplineTheory.allocas_from_def] >>
  `0 <= z.vs_alloca_next` by decide_tac >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
      lookup_var x z = SOME w` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at st x ==> lookup_var x z = lookup_var x s /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     asm_rewrite_tac[]) >>
  `!x. not_fresh_at st x ==>
      FLOOKUP Gz x = FLOOKUP G x /\ op_taint tz (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `lo <= s.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
     fs[ghost_inv_at_mods_def]) >>
  `!i. i < lo /\ i IN tz.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i < s.vs_alloca_next /\ i IN tz.t_mem` by
       (conj_tac
        >- (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
            qexists_tac `lo` >> conj_tac
            >- first_assum ACCEPT_TAC
            >- first_assum ACCEPT_TAC)
        >- first_assum ACCEPT_TAC) >>
     qpat_assum `!i. i < s.vs_alloca_next /\ i IN tz.t_mem ==> i IN tn.t_mem`
       (qspec_then `i` (drule_then assume_tac)) >>
     first_x_assum (drule_then assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d ce cx ee Gz tz z` by
    (irule bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`G`,`ee`,`func`,`s`,`st`,`tn`] >>
     simp[NoAsms] >> rpt conj_tac
     >- (qpat_assum `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
              lookup_var x z = SOME w` ACCEPT_TAC)
     >- (qpat_assum `!name b n. local_region ce ee.scopes s name b n ==> _`
              ACCEPT_TAC)
     >- (qpat_assum `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> _`
              ACCEPT_TAC)
     >- (qpat_assum `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> _`
              ACCEPT_TAC)
     >- (qpat_assum `!x. not_fresh_at st x ==> _` ACCEPT_TAC)
     >- simp[]
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC
     >- first_assum ACCEPT_TAC) >>
  irule bodyShaRegisteredFrameModsTheory.sha_registered_frame_mods >>
  conj_tac
  >- qpat_assum `ghost_inv_at D 0 d ce cx ee Gz tz z` ACCEPT_TAC
  >- (qexistsl_tac [`G`,`s`,`st`,`tn`] >>
      simp[NoAsms] >> rpt conj_tac
      >- (qpat_assum `!x. not_fresh_at st x ==> _` ACCEPT_TAC)
      >- (qpat_assum `!aid a k. FLOOKUP z.vs_allocas aid = SOME (a,k) ==> _`
              ACCEPT_TAC)
      >- (qpat_assum `!i. i < lo /\ i IN tz.t_mem ==> _` ACCEPT_TAC)
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC)
QED
