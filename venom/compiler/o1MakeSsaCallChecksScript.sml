Theory o1MakeSsaCallChecks
Ancestors
  o1MakeSsaCallOwnership o1MakeSsaCallPaths o1MakeSsaFlags unitShapeDefs
  makeSsaCurrentDefs list pred_set

Theorem current_flag_fails_operands:
  current_flag_alias rs vs ws /\ LENGTH bbs = LENGTH bbs' /\
  (!n l. revert_path bbs n l ==> revert_path bbs' n l) /\
  flag_fails bbs vs inst ==>
  flag_fails bbs' ws
    (inst with inst_operands := rename_current_operands rs inst.inst_operands)
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[flag_fails_def] >>
  Cases_on `inst.inst_operands` >> gvs[rename_current_operands_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t` >> gvs[rename_current_operands_def, current_flag_alias_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t'` >> gvs[rename_current_operands_def] >>
  Cases_on `h` >> gvs[rename_current_operands_def] >>
  Cases_on `t` >> gvs[rename_current_operands_def]
QED
