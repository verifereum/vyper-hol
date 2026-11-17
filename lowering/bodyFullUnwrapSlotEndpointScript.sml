Theory bodyFullUnwrapSlotEndpoint
Ancestors
  exprSimPtrTopLevelStorageCopy exprPtrUnwrapRuntimeFrame
  slotCopyExecution exprSimStorageCopy ptrDiscipline words arithmetic
  compileEnv venomState venomExecSemantics

Theorem unwrap_slot_loop_endpoint:
  toplevel_copy_inv cv ds dst src loc w b n a G0 tn0 n Gf tnf z /\
  (loc = LocStorage \/ loc = LocTransient) /\
  (!x. slot_copy_external mid (Var x) ==> ~MEM x ds) /\
  (!x. not_fresh_at mid x ==> ~MEM x ds) ==>
  slot_copy_runtime_frame mid (n2w b : bytes32) n a z /\
  (!j. j < n ==> mem_word_at (b+32*j) z.vs_memory =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a (w+n2w j)) /\
  (!j k. j < n /\ k < 32 /\ b+32*j+k IN tnf.t_mem ==>
    k IN key_taint (if loc=LocStorage then tn0.t_stor else tn0.t_trans) (w+n2w j)) /\
  (!q. ~(b <= q /\ q < b+32*n) /\ q IN tnf.t_mem ==> q IN tn0.t_mem) /\
  (!x. not_fresh_at mid x ==>
    lookup_var x z = lookup_var x a /\ FLOOKUP Gf x = FLOOKUP G0 x /\
    op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
  tnf.t_stor = tn0.t_stor /\ tnf.t_trans = tn0.t_trans /\ tnf.t_imm = tn0.t_imm
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac mp_tac) >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule toplevel_copy_inv_content >>
  disch_then (strip_assume_tac o REWRITE_RULE [storage_copy_inv_def, copy_prefix_def]) >>
  drule copy_static_fields >> strip_tac >>
  rpt conj_tac
  >- suspend "runtime"
  >- suspend "words"
  >- suspend "taint"
  >- suspend "outside"
  >- (rpt strip_tac >>
      `~MEM x ds` by metis_tac[] >>
      metis_tac[toplevel_copy_inv_ghost_frame, storage_copy_frame_def])
  >> fs[toplevel_copy_inv_def]
QED
Resume unwrap_slot_loop_endpoint[runtime]:
  `b < dimword (:256)` by
    (drule toplevel_copy_inv_bounds >> simp[dimword_def]) >>
  simp[slot_copy_runtime_frame_def] >> rpt conj_tac
  >- (rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def] >>
      gvs[storage_copy_frame_def, eval_operand_def] >> metis_tac[])
  >- (rpt strip_tac >> first_x_assum irule >> decide_tac)
  >> metis_tac[]
QED
Resume unwrap_slot_loop_endpoint[words]:
  rpt strip_tac >>
  `mem_word_at (b+32*j) z.vs_memory = copy_runtime_word loc a (w+n2w j)` by simp[] >>
  Cases_on `loc=LocStorage` >>
  gvs[copy_runtime_word_def, slot_copy_word_def]
QED
Resume unwrap_slot_loop_endpoint[taint]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, pred_setTheory.SUBSET_DEF] >>
  disch_then (qspec_then `b+32*j+k` mp_tac) >>
  `b <= b+32*j+k /\ b+32*j+k < b+32*n` by decide_tac >>
  simp[] >> strip_tac >>
  rename1 `(w+n2w i,r) IN toplevel_copy_source_taint loc tn0` >>
  `i = j /\ r = k` by intLib.COOPER_TAC >>
  qpat_x_assum `(w+n2w i,r) IN _` mp_tac >>
  simp[key_taint_def, toplevel_copy_source_taint_def]
QED
Resume unwrap_slot_loop_endpoint[outside]:
  rpt strip_tac >> drule toplevel_copy_inv_memory_taint >>
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
       toplevel_copy_translated_taint_def, pred_setTheory.SUBSET_DEF] >>
  disch_then (qspec_then `q` mp_tac) >> simp[] >>
  strip_tac >> gvs[]
QED
Finalise unwrap_slot_loop_endpoint
