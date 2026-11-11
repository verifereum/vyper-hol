Theory concretizePtrPrefixLedger
Ancestors
  concretizePtrPrefixRelation concretizePtrBytes concretizePtrChronologicalHistory
  concretizeMemLocDefs contextCodegenRel ptrDiscipline pred_set list

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

(* Tokens are source-entry event indices, not stack depths or addresses.
   Registry entries are retained after return. The target function carries
   the production fn_mems_used table used to interpret an owned site. *)
Datatype:
  ptr_ledger_activation = <|
    pla_source : ir_function;
    pla_target : ir_function;
    pla_parent : num option;
    pla_call : num option;
    pla_target_entry : num |>
End

Definition ptr_ledger_owned_site_def:
  ptr_ledger_owned_site (registry : (num,ptr_ledger_activation) fmap)
    (births : (num # num,num # num) fmap) token aid base size pos <=>
    FLOOKUP births (token,aid) = SOME (base,size) /\
    ?activation. FLOOKUP registry token = SOME activation /\
      MEM (Allocation aid,pos,size) activation.pla_target.fn_mems_used
End

(* Erasure refers to a birth in the original owner's activation, including
   for imported pointers. No numerical-site inverse lookup is used. *)
Definition ptr_ledger_erases_def:
  ptr_ledger_erases (births : (num # num,num # num) fmap)
    (tagged : (string,num # num) fmap) numerical <=>
    (!v. FLOOKUP numerical v =
      case FLOOKUP tagged v of
        NONE => NONE
      | SOME owner => FLOOKUP births owner) /\
    (!v owner. FLOOKUP tagged v = SOME owner ==> owner IN FDOM births)
End

Definition ptr_ledger_owned_byte_def:
  ptr_ledger_owned_byte registry births token aid k source target <=>
    ?base size pos.
      ptr_ledger_owned_site registry births token aid base size pos /\
      k < size /\ source = base + k /\ target = pos + k
End

(* Cursor indices are obtained by retaining the actual transformed source
   instructions; a deleted NOP contributes no target cursor. PHI entry is
   deliberately not modelled as an ordinary event here. *)
Definition ptr_ledger_block_alignment_def:
  ptr_ledger_block_alignment positions src tgt indices <=>
    indices = FILTER
      (\j. (concretize_inst_with_positions positions (EL j src)).inst_opcode <> NOP)
      (COUNT_LIST (LENGTH src)) /\
    tgt = MAP (\j. concretize_inst_with_positions positions (EL j src)) indices
End
