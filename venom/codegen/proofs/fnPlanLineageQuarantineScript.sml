Theory fnPlanLineageQuarantine
Ancestors
  fnPlanLineageInventory fnPlanLineageSetup stackPlanGen venomInst
Libs wordsLib

(* The unrestricted dispatcher probe admits malformed instructions. OFFSET
   reads HD outputs even when outputs=[], so the requested-name exclusions
   alone do not ensure stack non-recreation. This is not a ready-program
   counterexample and says nothing about the frozen lineage theorem. *)
Theorem native_quarantine_offset_empty_outputs_obstruction:
  ~MEM (Var (HD ([] : string list))) (init_plan_state 0).ps_stack /\
  ~MEM (Var (HD ([] : string list)))
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_operands /\
  ~MEM (HD ([] : string list))
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_outputs /\
  (!targets. (mk_inst 0 OFFSET [Lit 0w; Label "L"] []).inst_opcode = JMP /\
    join_target_ops lv fn lbl (mk_inst 0 OFFSET [Lit 0w; Label "L"] []) =
      SOME targets ==> ~MEM (Var (HD ([] : string list))) targets) /\
  generate_inst_plan lv dfg cfg fn
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] []) nl halt term lbl
    (init_plan_state 0) =
    SOME ([SOPushOfst "L" 0],
      (init_plan_state 0) with ps_stack := [Var (HD ([] : string list))]) /\
  MEM (Var (HD ([] : string list))) [Var (HD ([] : string list))]
Proof
  EVAL_TAC >> simp[]
QED

Theorem ready_member_instruction_shape:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions ==> inst_wf inst /\ codegen_ready_inst inst
Proof
  simp[codegen_ready_fn_def, venomWfTheory.fn_inst_wf_def,
    listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ready_non_phi_operand_bound:
  codegen_ready_inst inst /\ inst.inst_opcode <> PHI ==>
  LENGTH (compute_operands inst) <= 16
Proof
  simp[codegen_ready_inst_def]
QED

Theorem offset_declared_output_stack_support:
  inst_wf inst /\ inst.inst_opcode = OFFSET /\
  generate_offset_plan inst ps = (ops,qs) /\ MEM (Var v) qs.ps_stack ==>
  MEM (Var v) ps.ps_stack \/ MEM v inst.inst_outputs
Proof
  strip_tac >> drule_all venomWfTheory.inst_wf_offset_shape >> strip_tac >>
  gvs[generate_offset_plan_def, stackModelTheory.stack_push_def]
QED
