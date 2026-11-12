Theory lowerDloadExternalMemory
Ancestors
  lowerDloadExternalInputs lowerDloadExternalEffects lowerDloadCleanCopy
  lowerDloadStoreProducer lowerDloadAccessClassification lowerDloadNormalData
  lowerDloadOwnership lowerDloadRelocation lowerDloadPairedBoundary
  lowerDloadReachableDiscipline lowerDloadCoverageInvariant
  ptrDiscipline codegenRel words
  venomState venomExecSemantics list pred_set finite_map arithmetic

Theorem ld_external_written_taint:
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  written_taint tn i s = {}
Proof
  simp[MEM] >> strip_tac >> simp[written_taint_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[]
QED

(* The range premise is the declared capacity, not the actual write. *)
Theorem ld_external_return_mem_taint:
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  source_memory_write_ranges i s = [(p,n)] /\
  r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp ==>
  (step_taint i s r tn).t_mem =
    tn.t_mem DIFF {a | p <= a /\ a < p + LENGTH (TAKE n r.vs_returndata)}
Proof
  strip_tac >>
  `written_taint tn i s = {}` by
    (irule ld_external_written_taint >> gvs[MEM]) >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[step_taint_def, mem_taint_def, step_writes_def, LENGTH_TAKE_EQ, MIN_DEF,
       new_site_bytes_def, FLOOKUP_DEF, range_bytes_def, EXTENSION, SF CONJ_ss] >>
  Cases_on `n < LENGTH r.vs_returndata` >>
  Cases_on `n <= LENGTH r.vs_returndata` >> gvs[] >>
  `n = LENGTH r.vs_returndata` by decide_tac >> simp[]
QED

(* The declared output range bounds every actually written prefix.  Unlike
   a read footprint this gives both directions of related-byte membership. *)
Theorem ld_owned_write_prefix_geometry:
  access_ok lo (ld_erase AG) fn i s /\ ~in_revert_forward fn s /\
  mem_write_ops i = SOME ops /\
  MEM (w2n p,n) (source_memory_write_ranges i s) /\
  eval_operand ops.iao_ofst s = SOME p /\
  eval_operand ops.iao_ofst t = SOME q /\
  op_taint tn ops.iao_ofst = {} /\
  (!v. ops.iao_ofst = Var v ==> v IN U) /\
  ld_owned_vars U E AG BH tn un s t /\
  (!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)) /\
  (!owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz ==>
    lo <= bs /\ lo <= bt /\ bt+sz < dimword(:256)) /\
  (!owner other bs bt sz cs ct cz.
    owner IN live /\ other IN live /\ owner <> other /\
    ld_site_entry E owner bs bt sz /\ ld_site_entry E other cs ct cz ==>
    (bs+sz <= cs \/ cs+cz <= bs) /\
    (bt+sz <= ct \/ ct+cz <= bt)) /\ m <= n ==>
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
    ((w2n p<=a /\ a<w2n p+m) <=> (w2n q<=b /\ b<w2n q+m))) /\
  (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
    w2n p<=a /\ a<w2n p+m ==> a-w2n p=b-w2n q)
Proof
  strip_tac >> Cases_on `m = 0` >- simp[] >>
  `n <> 0` by decide_tac >>
  `((w2n p = w2n q /\ w2n p+m <= lo) \/
    (?owner bs bt sz. owner IN live /\ ld_site_entry E owner bs bt sz /\
      bs <= w2n p /\ w2n p+m <= bs+sz /\ w2n q = bt+(w2n p-bs)))` by
    (drule ld_access_write_classification >>
     disch_then (qspecl_then [`w2n p`,`n`] mp_tac) >> simp[] >> strip_tac
     >- (disj1_tac >>
         `ld_op_prov AG ops.iao_ofst = NONE` by gvs[GSYM ld_erase_op_prov] >>
         drule ld_owned_operand_clean >>
         disch_then (qspec_then `ops.iao_ofst` mp_tac) >> simp[] >>
         strip_tac >> gvs[] >> decide_tac) >>
     gvs[] >>
     `?bt. ld_site_entry E owner bs bt sz /\
       FLOOKUP BH v = SOME(owner,(bt,sz)) /\
       w2n q = bt+(w2n p-bs) /\ w2n q+n <= bt+sz` by
       (irule ld_owned_address_transport >> simp[] >>
        conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
        qexistsl_tac [`AG`,`U`,`s`,`t`,`tn`,`un`] >> simp[]) >>
     disj2_tac >> qexistsl_tac [`owner`,`bs`,`bt`,`sz`] >> simp[] >>
     metis_tac[]) >>
  irule ld_fixed_live_write_footprint >> metis_tac[]
QED

Theorem ld_create_mem_taint:
  MEM i.inst_opcode [CREATE;CREATE2] /\
  r.vs_allocas = s.vs_allocas /\ r.vs_fmp = s.vs_fmp ==>
  (step_taint i s r tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  `written_taint tn i s = {}` by
    (irule ld_external_written_taint >> gvs[MEM]) >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >> strip_tac >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
    source_memory_write_ranges_def, new_site_bytes_def,
    FLOOKUP_DEF, range_bytes_def, EXTENSION, SF CONJ_ss]
QED

Theorem ld_external_memory_preserved:
  ld_annotated_reachable vs0 CS astk k L AP AG tn fn i s /\
  ptr_discipline lo CS vs0 /\ ~in_revert_forward fn s /\
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
  ld_normal_data CS fn V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  mem_write_ops i = SOME ops /\ MEM ops.iao_ofst i.inst_operands /\
  (!v. ops.iao_ofst = Var v ==> v IN U) /\
  eval_operand ops.iao_ofst s = SOME p /\
  eval_operand ops.iao_ofst t = SOME q /\
  source_memory_write_ranges i s = [(w2n p,n)] /\
  source_memory_write_ranges i t = [(w2n q,n)] /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
  t'.vs_allocas = t.vs_allocas /\ t'.vs_fmp = t.vs_fmp /\
  s'.vs_returndata = bs /\ t'.vs_returndata = bs /\
  s'.vs_memory = (write_memory_with_expansion (w2n p) (TAKE n bs) s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion (w2n q) (TAKE n bs) t).vs_memory ==>
  ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
    (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  drule ld_normal_data_frame >> disch_then (strip_assume_tac o SRULE[ld_frame_data_def]) >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule_all ld_annotated_access_ok >> strip_tac >>
  `op_taint tn ops.iao_ofst = {}` by
    (drule ld_annotated_external_clean >>
     disch_then (qspec_then `lo` mp_tac) >>
     simp[MEM] >> impl_tac >- gvs[MEM] >> strip_tac >> metis_tac[]) >>
  `!v owner bs sz. FLOOKUP AG v = SOME(owner,(bs,sz)) ==>
    owner IN live /\ bs+sz < dimword(:256)` by
    (rpt strip_tac >>
     qpat_x_assum `!v. ld_owned_selection E _ _`
       (qspec_then `v` mp_tac) >>
     simp[ld_owned_selection_def] >> strip_tac >> metis_tac[]) >>
  `(!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) ==>
      ((w2n p<=a /\ a<w2n p+LENGTH (TAKE n bs)) <=>
       (w2n q<=b /\ b<w2n q+LENGTH (TAKE n bs)))) /\
   (!a b. ((a=b /\ a<lo) \/ ld_site_bytes E live a b) /\
      w2n p<=a /\ a<w2n p+LENGTH (TAKE n bs) ==> a-w2n p=b-w2n q)` by
    (irule ld_owned_write_prefix_geometry >>
     conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `access_ok _ _ _ _ _`)) >>
     simp[LENGTH_TAKE_EQ] >> metis_tac[]) >>
  `(step_taint i s s' tn).t_mem =
     tn.t_mem DIFF {a | w2n p<=a /\ a<w2n p+LENGTH (TAKE n bs)}` by
    (metis_tac[ld_external_return_mem_taint]) >>
  `(step_taint i t t' un).t_mem =
     un.t_mem DIFF {b | w2n q<=b /\ b<w2n q+LENGTH (TAKE n bs)}` by
    (metis_tac[ld_external_return_mem_taint]) >>
  drule ld_normal_data_memory >> disch_tac >>
  `ld_byte_rel (\a b. (a=b /\ a<lo) \/ ld_site_bytes E live a b)
     (tn.t_mem DIFF {a | w2n p<=a /\ a<w2n p+LENGTH (TAKE n bs)})
     (un.t_mem DIFF {b | w2n q<=b /\ b<w2n q+LENGTH (TAKE n bs)})
     (\a. read_memory a 1 (write_memory_with_expansion (w2n p) (TAKE n bs) s))
     (\b. read_memory b 1 (write_memory_with_expansion (w2n q) (TAKE n bs) t))` by
    (irule ld_shared_payload_write >> BETA_TAC >> asm_rewrite_tac[]) >>
  pop_assum mp_tac >>
  asm_rewrite_tac[ld_byte_rel_def, read_memory_def]
QED

Theorem ld_create_memory_preserved:
  MEM i.inst_opcode [CREATE;CREATE2] /\
  ld_byte_rel R tn.t_mem un.t_mem
    (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp /\
  t'.vs_allocas = t.vs_allocas /\ t'.vs_fmp = t.vs_fmp /\
  s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory ==>
  ld_byte_rel R (step_taint i s s' tn).t_mem (step_taint i t t' un).t_mem
    (\a. read_memory a 1 s') (\b. read_memory b 1 t')
Proof
  strip_tac >>
  `(step_taint i s s' tn).t_mem = tn.t_mem` by
    metis_tac[ld_create_mem_taint] >>
  `(step_taint i t t' un).t_mem = un.t_mem` by
    metis_tac[ld_create_mem_taint] >>
  qpat_x_assum `ld_byte_rel _ _ _ _ _` mp_tac >>
  asm_rewrite_tac[ld_byte_rel_def, read_memory_def]
QED
