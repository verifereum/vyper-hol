(* Parameter-origin support for an individual inherited allocation site.
   RO is deliberately independent of the analysis that establishes it. *)
Theory readonlyProvenanceSupport
Ancestors
  o1LowerDloadGhost execEquivParamBase venomExecProps o1PassContract
  ptrDiscipline pointerConfinedDefs memLocDefs
  venomInst venomState finite_map pred_set list words

Definition readonly_origin_contract_def:
  readonly_origin_contract RO V fn <=>
    (!inst idx v. MEM inst (fn_insts fn) /\ inst.inst_opcode = PARAM /\
       inst.inst_operands = [Lit idx] /\ inst_output inst = SOME v /\
       RO fn.fn_name (w2n idx) ==> v IN V fn) /\
    (!inst u v. MEM inst (fn_insts fn) /\
       is_pointer_preserving_op inst.inst_opcode /\
       MEM (Var u) inst.inst_operands /\ u IN V fn /\
       MEM v inst.inst_outputs ==> v IN V fn) /\
    (!inst ops v. MEM inst (fn_insts fn) /\
       mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v ==>
       v NOTIN V fn) /\
    (!inst nm args k v. MEM inst (fn_insts fn) /\
       inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,args) /\
       k < LENGTH args /\ EL k args = Var v /\ v IN V fn ==> RO nm k)
End

Definition readonly_site_support_def:
  readonly_site_support V fn G q <=>
    !v. FLOOKUP G v = SOME q ==> v IN V fn
End

Definition readonly_param_support_def:
  readonly_param_support RO fn PG q <=>
    !k. k < LENGTH PG /\ EL k PG = SOME q ==> RO fn.fn_name k
End

Theorem readonly_site_support_empty[simp]:
  readonly_site_support V fn FEMPTY q
Proof
  simp[readonly_site_support_def]
QED

Theorem readonly_site_support_restrict:
  readonly_site_support V fn G q ==>
  readonly_site_support V fn (DRESTRICT G keys) q
Proof
  simp[readonly_site_support_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem readonly_site_support_step:
  readonly_origin_contract RO V fn /\ readonly_site_support V fn G q /\
  readonly_param_support RO fn PG q /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode <> DALLOCA /\
  (inst.inst_opcode = ALLOCA ==> FLOOKUP s'.vs_allocas inst.inst_id <> SOME q) ==>
  readonly_site_support V fn (step_prov PG G inst s') q
Proof
  rpt strip_tac >> simp[readonly_site_support_def] >> rpt strip_tac >>
  Cases_on `inst.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FLOOKUP_DRESTRICT, readonly_site_support_def] >>
  Cases_on `t` >> gvs[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `out_prov PG G inst s'` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs(), readonly_site_support_def] >>
  Cases_on `inst.inst_opcode = ALLOCA` >> gvs[out_prov_def] >>
  Cases_on `inst.inst_opcode = PARAM`
  >- (gvs[AllCaseEqs(), readonly_param_support_def,
          readonly_origin_contract_def, inst_output_def] >> metis_tac[]) >>
  gvs[AllCaseEqs()] >> drule first_prov_origin >> strip_tac >>
  gvs[readonly_origin_contract_def] >>
  qpat_x_assum `!i u v. _` irule >>
  qexistsl_tac [`inst`, `v`] >> simp[is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem readonly_site_support_phis:
  !insts. readonly_origin_contract RO V fn /\
    EVERY (\i. MEM i (fn_insts fn)) insts /\ readonly_site_support V fn G q ==>
    readonly_site_support V fn (phis_prov prev G insts) q
Proof
  Induct >> simp[phis_prov_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phis_prov_def] >>
  `readonly_site_support V fn (phis_prov prev G insts) q` by metis_tac[] >>
  simp[readonly_site_support_def] >> rpt strip_tac >>
  Cases_on `h.inst_outputs` >>
  gvs[set_prov_def, FLOOKUP_DRESTRICT, readonly_site_support_def] >>
  Cases_on `t` >> gvs[set_prov_def, FLOOKUP_DRESTRICT] >>
  Cases_on `phi_prov prev G h` >>
  gvs[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, AllCaseEqs(), readonly_site_support_def] >>
  gvs[phi_prov_def, AllCaseEqs()] >>
  drule resolve_phi_MEM >> strip_tac >>
  Cases_on `op` >> gvs[op_prov_def] >>
  gvs[readonly_origin_contract_def] >>
  qpat_x_assum `!i u v. _` irule >>
  qexistsl_tac [`h`, `s`] >> simp[is_pointer_preserving_op_def] >> metis_tac[]
QED

Theorem readonly_site_support_entry:
  readonly_origin_contract RO V fn /\ readonly_site_support V fn G q ==>
  readonly_site_support V fn (entry_prov fn s G) q
Proof
  strip_tac >> simp[entry_prov_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  irule readonly_site_support_phis >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  drule lookup_block_MEM >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[]
QED

Theorem readonly_site_support_no_write:
  readonly_origin_contract RO V fn /\ readonly_site_support V fn G q /\
  MEM inst (fn_insts fn) /\ mem_write_ops inst = SOME ops ==>
  op_prov G ops.iao_ofst <> SOME q
Proof
  rpt strip_tac >> Cases_on `ops.iao_ofst` >>
  gvs[op_prov_def, readonly_site_support_def, readonly_origin_contract_def] >>
  metis_tac[]
QED

Theorem readonly_site_support_call:
  readonly_origin_contract RO V fn /\ readonly_site_support V fn G q /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,args) /\ k < LENGTH args /\
  op_prov G (EL k args) = SOME q ==> RO nm k
Proof
  rpt strip_tac >> Cases_on `EL k args` >>
  gvs[op_prov_def, readonly_site_support_def, readonly_origin_contract_def] >>
  metis_tac[]
QED
