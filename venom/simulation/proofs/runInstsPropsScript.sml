(*
 * run_insts and exec_block over a prefix of non-terminator, non-INVOKE
 * instructions: index independence, appending, and skipping the prefix.
 *)

Theory runInstsProps
Ancestors
  analysisSimDefs instIdxIndep venomExecSemantics venomState venomInst list

Theorem run_insts_singleton:
  !fuel ctx (x:instruction) s.
    run_insts fuel ctx [x] s = step_inst fuel ctx x s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

Theorem run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED


(* step_inst for non-term non-INVOKE is idx-independent (bridges to instIdxIndep) *)
Theorem step_inst_idx_indep:
  !fuel ctx inst s n.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (step_inst fuel ctx inst s)
Proof
  rw[step_inst_non_invoke, step_inst_inst_idx_indep]
QED


(* run_insts on non-term non-INVOKE instructions is idx-independent *)
Theorem run_insts_idx_indep:
  !fuel ctx insts s n.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    run_insts fuel ctx insts (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (run_insts fuel ctx insts s)
Proof
  Induct_on `insts` >> simp[run_insts_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  simp[run_insts_def, step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[exec_result_map_def, run_insts_def] >>
  `v.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `n`] mp_tac) >>
  simp[] >>
  strip_tac >> simp[exec_result_map_def]
QED


(* When run_insts succeeds on a non-term non-INVOKE prefix, exec_block
   skips past those instructions and continues from the resulting state. *)
Theorem exec_block_skip_prefix:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s'
  ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`]
    mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES])
  >> simp[]
QED


(* The Error-case counterpart of exec_block_skip_prefix. *)
Theorem exec_block_prefix_error:
  !prefix fuel ctx bb s j e.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j) (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  asm_rewrite_tac[] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[instIdxIndepTheory.exec_result_map_def, Once run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `e`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[]
QED

