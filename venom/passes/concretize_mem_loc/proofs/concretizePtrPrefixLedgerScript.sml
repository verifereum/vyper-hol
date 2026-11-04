Theory concretizePtrPrefixLedger
Ancestors
  concretizePtrPrefixRelation concretizePtrBytes concretizePtrChronologicalHistory
  contextCodegenRel ptrDiscipline pred_set

(* Endpoint demand is operational, not a parameter predicting future reads. *)
Definition ptr_ledger_read_demand_def:
  ptr_ledger_read_demand obs =
    range_bytes (source_memory_read_ranges obs.po_inst obs.po_state)
      DIFF obs.po_taint.t_mem
End

(* A ledger entry records the actual adjacent successful write events.
   It is not a promise of endpoint agreement or noninterference. The byte
   map will be derived from the activation registry at the use site. *)
Definition ptr_ledger_write_pair_def:
  ptr_ledger_write_pair C Ct rho a z b w <=>
    ptr_chrono_step C a z /\ ptr_chrono_step Ct b w /\
    ~is_terminator a.po_inst.inst_opcode /\
    a.po_inst.inst_opcode <> INVOKE /\
    ~is_terminator b.po_inst.inst_opcode /\
    b.po_inst.inst_opcode <> INVOKE /\
    (!i. i IN range_bytes (step_writes a.po_inst a.po_state z.po_state) ==>
       rho i IN range_bytes (step_writes b.po_inst b.po_state w.po_state)) /\
    ptr_bytes_agree
      (range_bytes (step_writes a.po_inst a.po_state z.po_state)
         DIFF z.po_taint.t_mem)
      rho z.po_state.vs_memory w.po_state.vs_memory
End
