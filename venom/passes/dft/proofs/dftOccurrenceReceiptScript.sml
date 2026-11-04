(* Receipts certify actual variable-only transitions, not residual matching. *)
Theory dftOccurrenceReceipt
Ancestors
  dftOccurrenceResidual dftOccurrenceReplay dftOccurrenceMachine
  dftOpenErase dftOpenMachine venomExecSemantics venomState venomInst list arithmetic

Definition dft_receipt_def:
  dft_receipt w ctx c0 H h inst addr us <=>
    h < H /\
    dft_occ_event inst addr (FUNPOW (dft_occ_oracle_next w ctx) h c0) /\
    ?fn bb s stack n fn' bb' t stack' n'.
      (FUNPOW (dft_occ_oracle_next w ctx) h c0).dft_occ_core =
        DftOpen (DftAt fn 0 bb s) stack n /\
      (dft_occ_oracle_next w ctx
        (FUNPOW (dft_occ_oracle_next w ctx) h c0)).dft_occ_core =
        DftOpen (DftAt fn' 0 bb' t) stack' n' /\
      dft_cut_data t = dft_pending_apply us (dft_cut_data s) /\
      EVERY (\p. MEM (FST p) inst.inst_outputs) us
End

Definition dft_receipt_list_def:
  dft_receipt_list w ctx c0 H rs <=>
    EVERY (\(h,inst,addr,us). dft_receipt w ctx c0 H h inst addr us) rs /\
    SORTED $< (MAP (\(h,inst,addr,us). h) rs)
End

Definition dft_receipt_payload_def:
  dft_receipt_payload rs = FLAT (MAP (\(h,inst,addr,us). us) rs)
End

Theorem dft_receipt_event:
  dft_receipt w ctx c0 H h inst addr us ==>
  dft_occ_event inst addr (FUNPOW (dft_occ_oracle_next w ctx) h c0)
Proof
  simp[dft_receipt_def]
QED

Theorem dft_receipt_transition:
  dft_receipt w ctx c0 H h inst addr us ==>
  ?fn bb s stack n fn' bb' t stack' n'.
    (FUNPOW (dft_occ_oracle_next w ctx) h c0).dft_occ_core =
      DftOpen (DftAt fn 0 bb s) stack n /\
    (dft_occ_oracle_next w ctx
      (FUNPOW (dft_occ_oracle_next w ctx) h c0)).dft_occ_core =
      DftOpen (DftAt fn' 0 bb' t) stack' n' /\
    dft_cut_data t = dft_pending_apply us (dft_cut_data s) /\
    EVERY (\p. MEM (FST p) inst.inst_outputs) us
Proof
  simp[dft_receipt_def]
QED

Theorem dft_receipt_extend:
  dft_receipt w ctx c0 H h inst addr us /\ H <= H' ==>
  dft_receipt w ctx c0 H' h inst addr us
Proof
  simp[dft_receipt_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem dft_receipt_list_extend:
  dft_receipt_list w ctx c0 H rs /\ H <= H' ==>
  dft_receipt_list w ctx c0 H' rs
Proof
  simp[dft_receipt_list_def, EVERY_MEM] >>
  rpt strip_tac >> PairCases_on `e` >> gvs[] >>
  irule dft_receipt_extend >> goal_assum (drule_at Any) >>
  first_x_assum (qspec_then `(e0,e1,e2,e3)` mp_tac) >> simp[]
QED

Theorem dft_receipt_gas:
  h < H /\
  c = FUNPOW (dft_occ_oracle_next w ctx) h c0 /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  dft_occ_event inst addr c /\
  inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  dft_receipt w ctx c0 H h inst addr [(out,w addr)]
Proof
  strip_tac >>
  `dft_occ_address c = addr` by
    (irule dft_occ_gas_address >>
     simp[dft_occ_gas_event_def] >> metis_tac[]) >>
  ` (dft_occ_oracle_next w ctx c).dft_occ_core =
      dft_erase (DftOpen (DftAt fn 0 bb
        ((update_var out (w addr) s) with vs_inst_idx := SUC s.vs_inst_idx))
        stack (SUC n))` by
    (qpat_x_assum `c = FUNPOW _ _ _` kall_tac >>
     simp[dft_occ_oracle_next_def, dft_next_inf_gas]) >>
  gvs[dft_receipt_def, dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  simp[dft_cut_data_def, dft_pending_apply_def, update_var_def]
QED
