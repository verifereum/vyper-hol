(* Target-only entry facts: the return token and memory-return buffer. *)
Theory bodyIntCallEntryTarget
Ancestors
  bodyIntCallEntryEnv intCallCallee stmtSim context compileEnv
  venomState words

Theorem compile_internal_prologue_return_fields:
  compile_internal_prologue cenv params has_rb ret st = ((cenv',pc),st') ==>
  cenv'.ce_return_pc = SOME (PtrVar pc 0) /\
  (cenv.ce_return_buf = NONE ==> cenv'.ce_return_buf = NONE) /\
  (~has_rb ==> cenv'.ce_return_buf = cenv.ce_return_buf)
Proof
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule materialize_internal_params_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  Cases_on `has_rb` >> gvs[comp_return_def, comp_bind_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `return_buf_var` >> simp[]
QED

(* The token/buffer facts are precisely the corresponding conclusions of
   compile_internal_prologue_entry. The caller must supply buffer headroom. *)
Theorem internal_prologue_ret_pc_ok:
  compile_internal_prologue cenv params has_rb ret st0 =
    ((cenv2,return_pc),st1) /\
  (?x. return_pc = Var x /\ not_fresh_at st1 x /\
       lookup_var x s1 = SOME token) /\
  (has_rb ==>
   ?rb. not_fresh_at st1 rb /\ lookup_var rb s1 = SOME (HD args) /\
        !off sz. cenv.ce_return_buf = SOME (MemLoc off sz) ==>
                 cenv2.ce_return_buf = SOME (PtrVar (Var rb) sz)) /\
  (cenv.ce_return_buf = NONE \/
   ?off sz. has_rb /\ cenv.ce_return_buf = SOME (MemLoc off sz) /\
            w2n (HD args) + sz + 64 < dimword (:256)) ==>
  ret_pc_ok (cenv2 with ce_alloca_locals := T) st1 s1
Proof
  strip_tac >> drule compile_internal_prologue_return_fields >> strip_tac >>
  simp[ret_pc_ok_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
