Theory o1LabelFlowMiddleFmp
Ancestors
  o1ContractFmpLowering fmpStepBridge o1LabelFlowRetention
  codegenSymRel unitShapeDefs fmpStepContract o1PassContract venomInst

(* The row supplies FMP-freedom; callees may already be sealed.  The
   no-parameter boundary handles both sealed and unsealed functions. *)
Theorem fmp_row_blocks_unchanged:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_fn_row 3 f /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions ==>
  out.fpo_function.fn_blocks = f.fn_blocks
Proof
  strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
  drule fmp_lower_function_no_param >>
  impl_tac >- fs[o1_fn_row_def] >>
  strip_tac >> gvs[]
QED

Theorem code_end_var_same_blocks:
  f.fn_blocks = g.fn_blocks ==>
  (code_end_var f x <=> code_end_var g x)
Proof
  strip_tac >>
  `fn_insts f = fn_insts g` by simp[fn_insts_def] >>
  metis_tac[code_end_var_instruction_subset]
QED

Theorem label_flow_ok_same_blocks:
  f.fn_blocks = g.fn_blocks ==>
  (label_flow_ok (ctx with ctx_functions := [f]) <=>
   label_flow_ok (ctx with ctx_functions := [g]))
Proof
  strip_tac >>
  `fn_insts f = fn_insts g` by simp[fn_insts_def] >>
  metis_tac[label_flow_ok_closed_retention]
QED

Theorem fmp_row_label_flow_ok:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_fn_row 3 f /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function])
Proof
  strip_tac >> drule_all fmp_row_blocks_unchanged >>
  metis_tac[label_flow_ok_same_blocks]
QED

Theorem fmp_row_code_end_lifetime:
  fn_pass_step rpolicy (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_fn_row 3 f /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  (!x. code_end_var f x ==>
    ?d op. MEM d (fn_insts f) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts f) /\ MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb f.fn_blocks /\ MEM j bb.bb_instructions /\
         MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)) ==>
  !x. code_end_var out.fpo_function x ==>
    ?d op. MEM d (fn_insts out.fpo_function) /\ d.inst_opcode = ADD /\
      d.inst_operands = [op; Label "code_end"] /\ d.inst_outputs = [x] /\
      (!k. MEM k (fn_insts out.fpo_function) /\
           MEM x k.inst_outputs ==> k = d) /\
      (!bb j. MEM bb out.fpo_function.fn_blocks /\
         MEM j bb.bb_instructions /\ MEM (Var x) j.inst_operands ==>
         j.inst_opcode = CODECOPY /\
         (?dst sz. j.inst_operands = [dst; Var x; sz] /\
                   dst <> Var x /\ sz <> Var x) /\
         ?pre post. bb.bb_instructions = pre ++ d::j::post)
Proof
  strip_tac >>
  `out.fpo_function.fn_blocks = f.fn_blocks` by
    metis_tac[fmp_row_blocks_unchanged] >>
  `!x. code_end_var out.fpo_function x <=> code_end_var f x` by
    metis_tac[code_end_var_same_blocks] >>
  gvs[fn_insts_def]
QED
