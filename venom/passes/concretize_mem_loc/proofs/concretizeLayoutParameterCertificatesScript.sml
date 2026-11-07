Theory concretizeLayoutParameterCertificates
Ancestors concretizeLayoutParameterControl frameIndexedCertificates

(* A single PARAM edge, including exec_block's index increment. Source
   admissibility of the successor is deliberately supplied, not inferred.
   Obs is transported explicitly, even in this constant-Obs instance. *)
Theorem resolved_parameter_entry_edge:
  inst.inst_opcode = PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [out] /\
  parameter_roots (\i x y. clean_resolved_root L (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  PG = MAP (OPTION_MAP SND) rp /\ resolution ct rp om rv /\
  indexed_entry A
    (\g a b. local_rel (\u. F) (guarded_ptr Opaque L (FST g))
       (guarded_bytes Opaque (FST g) (SND g)) R Obs a b /\
       parameter_control a = parameter_control b) (rv,tn) s t /\
  relocation_taint_le R tn un /\
  (!a b x y. Obs a b ==> Obs (update_var out x a) (update_var out y b)) /\
  control_transport Obs Obs
    (\a. a with vs_inst_idx := SUC s.vs_inst_idx)
    (\b. b with vs_inst_idx := SUC t.vs_inst_idx) /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  get_instruction bb' t.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK post /\
  (!rv'. resolution ct rp (origin_step PG om inst post) rv' ==>
    A (rv',step_taint inst s post tn)
      (post with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  ?post' rv'.
    block_segment fuel ctx bb s
      (post with vs_inst_idx := SUC s.vs_inst_idx) /\
    block_segment fuel' ctx' bb' t
      (post' with vs_inst_idx := SUC t.vs_inst_idx) /\
    resolution ct rp (origin_step PG om inst post) rv' /\
    indexed_entry A
      (\g a b. local_rel (\u. F) (guarded_ptr Opaque L (FST g))
        (guarded_bytes Opaque (FST g) (SND g)) R Obs a b /\
        parameter_control a = parameter_control b)
      (rv',step_taint inst s post tn)
      (post with vs_inst_idx := SUC s.vs_inst_idx)
      (post' with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[indexed_entry_def] >> strip_tac >>
  drule_all resolved_parameter_continuation >>
  disch_then (qspecl_then [`fuel'`, `ctx'`] strip_assume_tac) >>
  qexistsl_tac [`post'`, `rv'`] >> gvs[]
QED

val _ = export_theory();
