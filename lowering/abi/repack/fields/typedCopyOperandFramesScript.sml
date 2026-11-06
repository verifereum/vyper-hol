(* TOP-LEVEL: operand frames compose over actual compiler-counter cuts.
   Offset results avoid later allocations whether they reuse an input
   operand or return a newly allocated address temporary. *)
Theory typedCopyOperandFrames
Ancestors
  typedCopyOffset typedArrayLoopNames typedDynLoopNames copyVarFlow compileVarFlow abiBytestringCode abiStaticLoopCode
  compileEnv venomState venomInst list arithmetic

Theorem compile_with_byte_offset_next_var:
  !base_op offset cs op after.
    compile_with_byte_offset base_op offset cs = (op,after) ==> cs.cs_next_var <= after.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`base_op`, `offset`] compiler_vars_mono_with_byte_offset) >>
  simp_tac bool_ss [compiler_vars_mono_def] >>
  disch_then (qspec_then `cs` mp_tac) >> simp[]
QED

Theorem compiler_operand_avoid_interval:
  !arg_op var_start sub_start sub_end var_end.
    var_start <= sub_start /\ sub_start <= sub_end /\ sub_end <= var_end /\
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_start (var_end - var_start)) ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names sub_start (sub_end - sub_start))
Proof
  rpt gen_tac >> strip_tac >>
  `var_start + (sub_start - var_start) = sub_start` by decide_tac >>
  mp_tac (Q.SPECL [`arg_op`, `var_start`, `var_end - var_start`, `sub_start - var_start`, `sub_end - sub_start`]
    compiler_var_names_avoid_segment) >>
  impl_tac >- (conj_tac >- first_assum MATCH_ACCEPT_TAC >> decide_tac) >> asm_simp_tac bool_ss []
QED

Theorem compiler_operands_avoid_interval:
  !dst src var_start sub_start sub_end var_end.
    var_start <= sub_start /\ sub_start <= sub_end /\ sub_end <= var_end /\
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names var_start (var_end - var_start)) ==>
    EVERY (\name. dst <> Var name /\ src <> Var name) (compiler_var_names sub_start (sub_end - sub_start))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `EVERY _ (compiler_var_names var_start _)` (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`dst`, `var_start`, `sub_start`, `sub_end`, `var_end`] compiler_operand_avoid_interval) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`src`, `var_start`, `sub_start`, `sub_end`, `var_end`] compiler_operand_avoid_interval) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> simp[EVERY_CONJ]
QED

Theorem compiler_operands_frame_intervals:
  !var_start var_mid var_end initial middle final.
    var_start <= var_mid /\ var_mid <= var_end /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_start (var_mid - var_start)) ==>
      eval_operand arg_op middle = eval_operand arg_op initial) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_mid (var_end - var_mid)) ==>
      eval_operand arg_op final = eval_operand arg_op middle) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_start (var_end - var_start)) ==>
      eval_operand arg_op final = eval_operand arg_op initial
Proof
  rpt gen_tac >> strip_tac >>
  `var_start + (var_mid - var_start) = var_mid /\
    var_mid - var_start + (var_end - var_mid) = var_end - var_start` by decide_tac >>
  mp_tac (Q.SPECL [`var_start`, `var_mid - var_start`, `var_end - var_mid`, `initial`, `middle`, `final`]
    compiler_operands_frame_ranges) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> first_assum MATCH_ACCEPT_TAC]) >> asm_simp_tac bool_ss []
QED

Theorem compile_with_byte_offset_result_avoids:
  !base_op offset cs op after var_mid var_end.
    compile_with_byte_offset base_op offset cs = (op,after) /\
    after.cs_next_var <= var_mid /\ var_mid <= var_end /\
    EVERY (\name. base_op <> Var name) (compiler_var_names cs.cs_next_var (var_end - cs.cs_next_var)) ==>
    EVERY (\name. op <> Var name) (compiler_var_names var_mid (var_end - var_mid))
Proof
  rpt gen_tac >> strip_tac >> drule compile_with_byte_offset_code >> DISCH_TAC >>
  Cases_on `offset = 0`
  >- (fs[] >> qpat_x_assum `after = cs` SUBST_ALL_TAC >> qpat_x_assum `op = base_op` SUBST_ALL_TAC >>
      mp_tac (Q.SPECL [`base_op`, `cs.cs_next_var`, `var_mid`, `var_end`, `var_end`] compiler_operand_avoid_interval) >>
      impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]) >> simp[]) >>
  gvs[] >> `cs.cs_next_var + (var_mid - cs.cs_next_var) = var_mid` by decide_tac >>
  mp_tac (Q.SPECL [`cs.cs_next_var`, `var_mid - cs.cs_next_var`, `var_end - var_mid`, `0`]
    compiler_var_names_before) >> impl_tac >- decide_tac >> asm_simp_tac (srw_ss()) []
QED
