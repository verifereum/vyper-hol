Theory exprSimAbiDecodeShapeProbe
Ancestors
  exprSimAbiDecodeShape exprSimAbiDecodeTrace compileEnv emitHelper venomInst emitHelperProps list arithmetic

Definition decode_trace_safe_def:
  decode_trace_safe lo hi allowed excluded es <=>
    lo <= hi /\
    EVERY (\i. lo <= i.inst_id /\ i.inst_id < hi)
      (decode_instructions es) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (decode_instructions es)) /\
    ALL_DISTINCT (decode_switches es) /\
    EVERY (\l. MEM l allowed) (decode_switches es) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      i.inst_opcode <> PHI /\ i.inst_opcode <> STOP /\ i.inst_opcode <> RETURN)
      (decode_instructions es) /\
    (decode_switches es = [] ==>
      EVERY (\i. ~MEM (Label excluded) i.inst_operands) (decode_instructions es))
End

(* Same witness carries the actual run and trace safety. Allowed labels may
   have been reserved before this action, rather than allocated inside it. *)
Definition decode_shape_run_def:
  decode_shape_run allowed excluded m s <=>
    ?x t es. m s = (x,t) /\
      t = decode_history t (decode_replay es s) /\
      decode_trace_safe s.cs_next_id t.cs_next_id allowed excluded es
End

Theorem decode_shape_probe_emits:
  decode_shape_run [] excluded
    (comp_ignore_bind (emit_void MSTORE []) (emit_void MSTORE [])) s
Proof
  simp[decode_shape_run_def, comp_ignore_bind_def, comp_bind_def,
       emit_void_def, fresh_id_def, emit_def] >>
  qexists_tac `[DecodeEmit (mk_inst s.cs_next_id MSTORE [] []);
    DecodeEmit (mk_inst (s.cs_next_id + 1) MSTORE [] [])]` >>
  simp[decode_trace_safe_def, decode_instructions_def, decode_switches_def,
       decode_replay_def, decode_step_def, decode_history_def, mk_inst_def] >>
  simp[compile_state_component_equality]
QED

Theorem decode_shape_probe_reserved:
  let l1 = fresh_label_output suffix s.cs_next_label;
      l2 = fresh_label_output suffix (s.cs_next_label + 1) in
  decode_shape_run [l1;l2] excluded
    (comp_bind (fresh_label suffix) (\a.
      comp_bind (fresh_label suffix) (\b.
        comp_ignore_bind (new_block a)
          (comp_ignore_bind (new_block b) (comp_return ()))))) s
Proof
  simp[decode_shape_run_def, comp_ignore_bind_def, comp_bind_def,
       fresh_label_def, new_block_def, comp_return_def] >>
  qexists_tac `[DecodeSwitch (fresh_label_output suffix s.cs_next_label);
    DecodeSwitch (fresh_label_output suffix (s.cs_next_label + 1))]` >>
  simp[decode_trace_safe_def, decode_instructions_def, decode_switches_def,
       decode_replay_def, decode_step_def, decode_history_def] >>
  metis_tac[fresh_label_output_inj, DECIDE ``n <> n + 1``]
QED

Theorem decode_trace_safe_append:
  decode_trace_safe lo mid allowed excluded es /\
  decode_trace_safe mid hi allowed excluded fs /\
  (!l. MEM l (decode_switches es) ==> ~MEM l (decode_switches fs)) ==>
  decode_trace_safe lo hi allowed excluded (es ++ fs)
Proof
  rw[decode_trace_safe_def, decode_instructions_append,
     decode_switches_append, EVERY_APPEND, MAP_APPEND, ALL_DISTINCT_APPEND] >>
  fs[EVERY_MEM, MEM_MAP]
  >- (rpt strip_tac >>
      qpat_x_assum `!i. MEM i (decode_instructions es) ==> lo <= _ /\ _` drule >>
      decide_tac)
  >- (rpt strip_tac >>
      qpat_x_assum `!i. MEM i (decode_instructions fs) ==> mid <= _ /\ _` drule >>
      decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!i. MEM i (decode_instructions es) ==> lo <= _ /\ _` drule >>
  qpat_x_assum `!i. MEM i (decode_instructions fs) ==> mid <= _ /\ _` drule >>
  decide_tac
QED
