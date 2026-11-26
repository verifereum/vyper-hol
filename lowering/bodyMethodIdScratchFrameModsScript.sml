(* Transport the linked ghost and immutable frame across a registered scratch write. *)
Theory bodyMethodIdScratchFrameMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit exprLoweringProps
  loweringSlice loweringStateRelDefs ptrDiscipline compileEnv venomInst
  venomState bodyPtrDefs valueEncodingDefs finite_map alist pred_set

Theorem method_id_ghost_at_zero:
  ghost_inv_at_mods D lo d ce cx es G tn s ==>
  ghost_inv_at D 0 d ce cx es G tn s
Proof
  simp[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem method_id_scratch_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  ghost_inv_at D 0 d ce cx es G' tn' z /\
  local_ptrs_reserved ce k /\
  (!x. not_fresh_at k x ==> FLOOKUP G' x = FLOOKUP G x) /\
  (!x. not_fresh_at k x ==> op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' z
Proof
  strip_tac >>
  `allocas_from lo z /\ lo <= z.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, allocas_from_def] >> rpt strip_tac >>
     qpat_assum `!aid a sz. FLOOKUP z.vs_allocas aid = _ ==> _`
       (drule_then strip_assume_tac) >- metis_tac[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  gvs[SUBSET_DEF, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem method_id_scratch_sep[local]:
  immutable_alloca_sep_mods func ce cx es s /\
  local_ptrs_reserved ce k /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s) /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) ==>
  immutable_alloca_sep_mods func ce cx es z
Proof
  simp[immutable_alloca_sep_mods_def] >> strip_tac >> rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >> simp[] >>
  rpt gen_tac >> strip_tac >> disj1_tac >>
  rename1 `local_region _ _ z id a sz` >> qexists_tac `id` >>
  fs[local_region_def, local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]
QED

Theorem method_id_scratch_immutables[local]:
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es s /\
  immutable_alloca_sep_mods func ce cx es z /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  (!a sz. a + sz <= b \/ b + n <= a ==>
      mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory) ==>
  immutables_rel_mods ce cx.txn.target ce.ce_is_ctor es z
Proof
  simp[immutables_rel_mods_def, immutable_alloca_sep_mods_def] >>
  strip_tac >> rpt gen_tac >> disch_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  qpat_assum `!src tops. _ ==> immutable_alloca_sep _ _ _ _ _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [immutable_alloca_sep_def])) >>
  qpat_x_assum `ce.ce_is_ctor ==> _` (drule_then assume_tac) >>
  pop_assum (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!i a sz. MEM i _ /\ _ ==> regions_disjoint _ _ a sz`
    (drule_all_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem method_id_scratch_frame_op_taint_mods:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  immutable_frame_mods func ce cx es s /\
  ghost_inv_at D 0 d ce cx es G' tn' z /\
  local_ptrs_reserved ce k /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
                           FLOOKUP G' x = FLOOKUP G x /\
                           op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) /\ lo <= b /\
  (!a sz. a + sz <= b \/ b + n <= a ==>
      mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory) ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' z /\
  immutable_frame_mods func ce cx es z
Proof
  simp[immutable_frame_mods_def] >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [IMP_CONJ_THM, FORALL_AND_THM]) >>
  conj_tac
  >- (`mem_bytes_at 0 lo z.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
        (qpat_assum `!a sz. a + sz <= b \/ _ ==> _`
           (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
      drule_all method_id_scratch_ghost >> simp[]) >>
  reverse conj_asm2_tac
  >- (drule_all method_id_scratch_sep >> simp[]) >>
  drule_all method_id_scratch_immutables >> simp[]
QED

(* The exact finite-map observation implies operand-taint agreement. *)
Theorem method_id_scratch_frame_mods:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  immutable_frame_mods func ce cx es s /\
  ghost_inv_at D 0 d ce cx es G' tn' z /\
  local_ptrs_reserved ce k /\
  (!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
                           FLOOKUP G' x = FLOOKUP G x /\
                           FLOOKUP tn'.t_var x = FLOOKUP tn.t_var x) /\
  tn'.t_mem SUBSET tn.t_mem /\
  z.vs_data_section = s.vs_data_section /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  (!aid a sz. FLOOKUP z.vs_allocas aid = SOME (a,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (a,sz) \/ s.vs_alloca_next <= a) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP z.vs_allocas inst.inst_id = SOME (b,n) /\ lo <= b /\
  (!a sz. a + sz <= b \/ b + n <= a ==>
      mem_bytes_at a sz z.vs_memory = mem_bytes_at a sz s.vs_memory) ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' z /\
  immutable_frame_mods func ce cx es z
Proof
  strip_tac >>
  `!x. not_fresh_at k x ==> lookup_var x z = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >>
     simp[op_taint_def]) >>
  drule_all method_id_scratch_frame_op_taint_mods >> simp[]
QED
