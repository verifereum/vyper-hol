Theory extRetScratchResourcePtr
Ancestors
  allocaSiteResource allocationPtr extRetSourceAllocationPtr exprLoweringProps
  localPtrsProps loweringPosts exprSimOperands compileEnv venomState venomInst
  venomExecSemantics venomMemDefs words finite_map pred_set arithmetic

Definition scratch_resource_def:
  scratch_resource ctx fn sites q len s <=>
    alloca_room ctx fn s /\ alloca_inv s /\
    (len <> 0 ==> q+len <= s.vs_alloca_next) /\
    (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
      sz = 32 /\ (len <> 0 ==> venomMemDefs$regions_disjoint (q,len) (b,sz)))
End

Theorem scratch_resource_fields:
  scratch_resource ctx fn sites q len s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  scratch_resource ctx fn sites q len t
Proof
  simp[scratch_resource_def] >> strip_tac >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem scratch_word_size[local]:
  w2n (32w:bytes32) = 32
Proof
  simp_tac (srw_ss()) [w2n_n2w, dimword_def,
    fcpLib.INDEX_CONV ``dimindex (:256)``]
QED

Theorem scratch_resource_alloca:
  scratch_resource ctx fn sites q len s /\ inst.inst_id IN sites /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit 32w] /\ inst.inst_outputs = [out] ==>
  ?t b. exec_alloca inst s (32w:bytes32) = OK t /\
    scratch_resource ctx fn sites q len t /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32) /\
    lookup_var out t = SOME (n2w b) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP t.vs_allocas id = SOME (p,sz)) /\
    (len <> 0 ==> venomMemDefs$regions_disjoint (q,len) (b,32))
Proof
  simp_tac std_ss [scratch_resource_def] >> strip_tac >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = 32` by
    metis_tac[] >>
  drule_all alloca_site32_execute >> strip_tac >>
  `len <> 0 ==> venomMemDefs$regions_disjoint (q,len) (b,32)` by
    (strip_tac >>
     drule alloca_site_execute_protected >> disch_then drule >>
     disch_then (qspecl_then [`q`, `len`, `b`] mp_tac) >>
     pure_rewrite_tac [scratch_word_size] >>
     impl_tac >- (rpt conj_tac >- metis_tac[] >> metis_tac[]) >>
     simp[]) >>
  qexistsl_tac [`t`, `b`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (strip_tac >> res_tac >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `id = inst.inst_id`
  >- (qpat_x_assum `id = inst.inst_id` SUBST_ALL_TAC >>
      qpat_x_assum `FLOOKUP t.vs_allocas inst.inst_id = SOME (b,32)` mp_tac >>
      qpat_x_assum `FLOOKUP t.vs_allocas inst.inst_id = SOME (b',sz)` mp_tac >>
      qpat_x_assum `len <> 0 ==> regions_disjoint _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp_tac std_ss []) >>
  `FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     qpat_x_assum `inst.inst_outputs = [out]` mp_tac >>
     qpat_x_assum `id <> inst.inst_id` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >>
     gvs[exec_alloca_def, update_var_def, FLOOKUP_UPDATE,
         AllCaseEqs()]) >>
  metis_tac[]
QED
