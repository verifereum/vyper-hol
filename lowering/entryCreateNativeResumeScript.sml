(* Residual native trace at an already entered instruction cursor. *)
Theory entryCreateNativeResume
Ancestors
  dftGasFromListTraceDefs blockSimHelpers venomExecSemantics venomState venomInst list

Definition create_trace_from_def:
  create_trace_from p d k C f s =
    case lookup_block s.vs_current_bb f.fn_blocks of
      NONE => []
    | SOME bb =>
        trace_block p d k C f bb s ++
          (case exec_block k C bb s of
             OK u => if u.vs_halted then [] else trace_blocks p d k C f u
           | _ => [])
End

Theorem create_trace_from_enter:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK sp /\
  sp.vs_current_bb = s.vs_current_bb ==>
  trace_blocks p d (SUC k) C f s =
    create_trace_from p (SUC d) k C f
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> drule_all trace_blocks_enter >> simp[create_trace_from_def]
QED

Theorem create_trace_from_next:
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  u.vs_current_bb = s.vs_current_bb ==>
  create_trace_from p d k C f s =
    ((p,d,i.inst_id),f,i,s) ::
      (trace_step p d k C f i s ++
       create_trace_from p d k C f (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  simp[create_trace_from_def] >>
  drule_all trace_block_visit >> disch_then (fn th => simp[Once th]) >>
  drule_all exec_block_step >> simp[APPEND_ASSOC]
QED
