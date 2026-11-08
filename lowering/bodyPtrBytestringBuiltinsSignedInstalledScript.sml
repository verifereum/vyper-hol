Theory bodyPtrBytestringBuiltinsSignedInstalled
Ancestors
  bodyPtrBytestringBuiltinsSignedFrame fragExec exprLoweringProps

(* Actual whole-Slice lowering, not the isolated conversion fixture. *)
Definition signed_installed_compiled_def:
  signed_installed_compiled = lower_value compile_expr signed_frame_env
    (BaseT (BytesT (Dynamic 1))) signed_frame_expr (initial_compile_state "entry")
End

Theorem signed_installed_prefix:
  TAKE 6 (SND signed_installed_compiled).cs_current_insts =
    [mk_inst 0 MLOAD [Var "b_ptr"] ["%0"];
     mk_inst 1 ADD [Var "b_ptr"; Lit 32w] ["%1"];
     mk_inst 2 MLOAD [Var "%1"] ["%2"];
     mk_inst 3 ISZERO [Var "%0"] ["%3"];
     mk_inst 4 ISZERO [Var "%3"] ["%4"];
     mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"]]
Proof
  EVAL_TAC
QED

Theorem signed_empty_context_no_mul:
  !fn. lookup_function fn.fn_name order_frame_unit.cu_context.ctx_functions = SOME fn ==>
    EVERY (\i. i.inst_opcode <> MUL) (fn_insts fn)
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[listTheory.INDEX_FIND_def, AllCaseEqs()] >>
  simp[vyperCompilerTheory.EVERY_fn_insts_blocks]
QED

Theorem signed_installed_mul_member:
  MEM (mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"])
    (SND signed_installed_compiled).cs_current_insts
Proof
  mp_tac signed_installed_prefix >> strip_tac >>
  `MEM (mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"])
    (TAKE 6 (SND signed_installed_compiled).cs_current_insts)` by simp[] >>
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem signed_installed_code_has_mul:
  fn_has_code (initial_compile_state "entry") (SND signed_installed_compiled) fn ==>
  MEM (mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"]) (fn_insts fn)
Proof
  simp[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> rpt strip_tac >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[signed_installed_mul_member]
QED

Theorem signed_installed_empty_frame_obstruction:
  !fn. ~(fn_has_code (initial_compile_state "entry")
             (SND signed_installed_compiled) fn /\
          stmt_state_rel order_frame_unit.cu_context fn signed_frame_env
            order_runtime_cx signed_frame_source signed_frame_start)
Proof
  rpt strip_tac >> drule signed_installed_code_has_mul >>
  fs[stmt_state_rel_def, alloca_room_def] >>
  drule signed_empty_context_no_mul >>
  simp[listTheory.EVERY_MEM] >>
  disch_then (qspec_then `mk_inst 5 MUL [Var "%2"; Var "%4"] ["%5"]` mp_tac) >>
  simp[venomInstTheory.mk_inst_def]
QED
