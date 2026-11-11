(* Contiguous parameter prefixes leave the residual block computation intact.
   This is conditional execution infrastructure, not a produced-prefix claim. *)
Theory functionInlinerParameterSequential
Ancestors
  o1LowerDloadSegmentContinuation functionInlinerParameterSavedReads
  functionInlinerOperationalCuts venomExecSemantics venomState venomInst list

(* The sequence is indexed by actual machine states.  In particular the
   increment uses the old PC, not the PC returned by step_inst.  No condition
   is imposed on the residual computation at the one-past-end boundary. *)
Theorem inline_parameter_sequential_exec:
  !es f start.
    (f 0).vs_inst_idx = start /\
    (!j. j < LENGTH es ==>
      get_instruction bb (f j).vs_inst_idx = SOME (EL j es) /\
      ~is_terminator (EL j es).inst_opcode /\
      ?u. step_inst fuel C (EL j es) (f j) = OK u /\
          f (SUC j) = u with vs_inst_idx := SUC (f j).vs_inst_idx) ==>
    exec_block fuel C bb (f 0) = exec_block fuel C bb (f (LENGTH es)) /\
    (!j. j <= LENGTH es ==> (f j).vs_inst_idx = start + j)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ld_exec_block_finite_continuation >> simp[]) >>
  Induct >> simp[] >> strip_tac >>
  `j < LENGTH es` by decide_tac >>
  first_x_assum (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> simp[]
QED

(* Empty intervals are legitimate boundaries, including at the end of a block. *)
Theorem inline_parameter_sequential_empty:
  LENGTH es = 0 ==>
  exec_block fuel C bb (f 0) = exec_block fuel C bb (f (LENGTH es)) /\
  (f (LENGTH es)).vs_inst_idx = (f 0).vs_inst_idx
Proof simp[]
QED

(* PC advancement changes neither addressed storage nor archived caller
   reads. Logical and physical PCs may advance from different locations. *)
Theorem inline_parameter_sequential_control:
  inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
  inline_parameter_saved_reads ((p,a,route,snap)::rest) ==>
  inline_owner_storage cert
    ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := si)::rest)
    (frame with ipf_state := frame.ipf_state with vs_inst_idx := ti) /\
  inline_parameter_saved_reads
    ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := si)::rest)
Proof
  strip_tac >> conj_tac
  >- (irule inline_owner_storage_index >> simp[]) >>
  irule inline_parameter_saved_reads_head_replace >> goal_assum (drule_at Any)
QED
