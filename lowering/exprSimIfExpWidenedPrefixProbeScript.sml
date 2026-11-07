Theory exprSimIfExpWidenedPrefixProbe
Ancestors
  exprSimIfExpWidenedCounted abiEncoderPrefixSafety abiEncoderObserver
  exprLowering context exprSimUnwrap compileEnv

(* The return-only unwrap really is a zero-instruction first cut. *)
Theorem unwrap_stack_first_cut[local]:
  unwrap_value ce (StackValue ty op) sm = (out,sn) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  out = op /\ sn = sm /\
  local_prefix ctx func (sn.cs_current_bb,LENGTH sn.cs_current_insts) s s
Proof
  simp[unwrap_value_def, comp_return_def] >> strip_tac >>
  irule (cj 1 local_prefix_rules) >> simp[]
QED

(* Storage-copy diagnostic: unwrap_storage_copy_path supplies gas_path,
   expr_post, and the exit cursor, but no avoidance of that cursor along
   the proper prefix. No claim that an arbitrary gas path is a first-cut
   path is exported here. *)
