Theory concretizePtrPairedJumpSchema
Ancestors
  concretizePtrPairedRoot concretizePtrPairedPrefixProbe concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrMixedPhi concretizeStepStructure concretizeStepShape
  concretizeStepCallChecks concretizeStepRetpc concretizeStageShape
  venomExecSemantics venomWf unitShapeDefs ptrDiscipline finite_map list

(* Audit only: parse and typecheck a proposed obligation. This asserts no
   theorem, introduces no constant and registers no oracle. *)
val _ = type_of ``
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = JMP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  step_inst fuel Ct at.po_inst at.po_state = OK t_jump /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
``;
