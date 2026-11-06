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
