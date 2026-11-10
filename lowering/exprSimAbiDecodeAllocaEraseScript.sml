Theory exprSimAbiDecodeAllocaErase
Ancestors
  exprSimAbiDecodeBuiltin exprLoweringProps localPtrsProps actualDecoderSites
  finite_map pred_set list venomState venomMemDefs compileEnv
  exprSimAbiDecodeCoverageBoundary

Definition abi_decode_alloca_ids_def:
  abi_decode_alloca_ids func =
    {id | ?i. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\ id = i.inst_id}
End

Definition abi_decode_clean_allocas_def:
  abi_decode_clean_allocas func s =
    s with vs_allocas := DRESTRICT s.vs_allocas (abi_decode_alloca_ids func)
End

Theorem abi_decode_clean_lookup:
  FLOOKUP (abi_decode_clean_allocas func s).vs_allocas id =
    if id IN abi_decode_alloca_ids func then FLOOKUP s.vs_allocas id else NONE
Proof
  simp[abi_decode_clean_allocas_def, FLOOKUP_DRESTRICT]
QED

Theorem abi_decode_clean_fields[simp]:
  (abi_decode_clean_allocas func s).vs_memory = s.vs_memory /\
  (abi_decode_clean_allocas func s).vs_vars = s.vs_vars /\
  (abi_decode_clean_allocas func s).vs_alloca_next = s.vs_alloca_next /\
  (abi_decode_clean_allocas func s).vs_current_bb = s.vs_current_bb /\
  (abi_decode_clean_allocas func s).vs_inst_idx = s.vs_inst_idx /\
  (abi_decode_clean_allocas func s).vs_fmp = s.vs_fmp
Proof
  simp[abi_decode_clean_allocas_def]
QED

Theorem abi_decode_clean_pending:
  pending_alloca_size func (abi_decode_clean_allocas func s) =
    pending_alloca_size func s
Proof
  simp[pending_alloca_size_def, abi_decode_clean_allocas_def, FDOM_DRESTRICT] >>
  AP_TERM_TAC >> AP_TERM_TAC >>
  `!xs. (!i. MEM i xs /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func) ==>
    FILTER (\i. i.inst_opcode = ALLOCA /\
      ~(i.inst_id IN FDOM s.vs_allocas /\ i.inst_id IN abi_decode_alloca_ids func)) xs =
    FILTER (\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN FDOM s.vs_allocas) xs` by
    (Induct >- simp[] >>
     simp_tac bool_ss [MEM] >> gen_tac >> strip_tac >>
     `!i. MEM i xs /\ i.inst_opcode = ALLOCA ==>
       i.inst_id IN abi_decode_alloca_ids func` by metis_tac[] >>
     first_x_assum drule_all >> strip_tac >>
     Cases_on `h.inst_opcode = ALLOCA` >> gvs[] >>
     `h.inst_id IN abi_decode_alloca_ids func` by metis_tac[] >> simp[]) >>
  rule_assum_tac (SIMP_RULE bool_ss []) >>
  first_x_assum irule >> simp[abi_decode_alloca_ids_def] >> metis_tac[]
QED

Theorem abi_decode_clean_inv:
  alloca_inv s ==> alloca_inv (abi_decode_clean_allocas func s)
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
     abi_decode_clean_lookup] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_decode_clean_resources:
  decode_site_resources ctx func s ==>
  decode_site_resources ctx func (abi_decode_clean_allocas func s)
Proof
  rw[decode_site_resources_def]
  >- gvs[alloca_room_def, abi_decode_clean_pending]
  >- metis_tac[abi_decode_clean_inv]
  >- (gvs[fmp_room_def, abi_decode_clean_pending] >> metis_tac[]) >>
  fs[abi_decode_clean_lookup, AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_decode_clean_builtin_resources:
  abi_builtin_decode_site_resources ctx func st last mn mx outsz cnt p d s /\
  abi_builtin_decode_output_site st mn mx IN abi_decode_alloca_ids func ==>
  abi_builtin_decode_site_resources ctx func st last mn mx outsz cnt p d
    (abi_decode_clean_allocas func s)
Proof
  simp_tac bool_ss [abi_builtin_decode_site_resources_def] >> strip_tac >>
  asm_simp_tac bool_ss [abi_decode_clean_fields, abi_decode_clean_lookup] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> metis_tac[abi_decode_clean_resources]
QED

Theorem abi_decode_clean_protected_rows:
  (!i b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (b,sz) ==>
    compileEnv$regions_disjoint b sz q n) /\
  FLOOKUP (abi_decode_clean_allocas func s).vs_allocas id = SOME (b,sz) ==>
  compileEnv$regions_disjoint b sz q n
Proof
  rw[abi_decode_clean_lookup] >>
  fs[AllCaseEqs(), abi_decode_alloca_ids_def] >> metis_tac[]
QED

Theorem abi_decode_output_site_registered:
  lower_abi_decode data info mn mx outsz a = (out,b) /\
  (!i. MEM i (frag_code a b) ==> MEM i (fn_insts func)) ==>
  abi_builtin_decode_output_site a mn mx IN abi_decode_alloca_ids func
Proof
  strip_tac >> drule abi_decode_lower_output_allocation >> strip_tac >>
  simp[abi_decode_alloca_ids_def] >> metis_tac[]
QED

Theorem abi_decode_clean_immutable_region:
  immutable_alloca_sep func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= s.vs_alloca_next /\
  (!id b sz. FLOOKUP (abi_decode_clean_allocas func s).vs_allocas id = SOME (b,sz) ==>
    compileEnv$regions_disjoint b sz off (type_memory_size tv))
Proof
  strip_tac >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [immutable_alloca_sep_def] >>
  disch_then drule_all >> strip_tac >>
  conj_tac >- simp[] >> rpt strip_tac >>
  irule abi_decode_clean_protected_rows >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]
QED
