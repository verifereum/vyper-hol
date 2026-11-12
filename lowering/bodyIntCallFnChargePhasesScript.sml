(* Extension interfaces for the conditional phases around materialization. *)
Theory bodyIntCallFnChargePhases
Ancestors
  externalEntryShape moduleLowering compileEnv emitHelper context
  loweringShapeDefs venomInst list words

Theorem internal_return_param_extends:
  !hr st rb sb.
    (if hr then do p <- emit_op PARAM [Lit 0w]; return (SOME p) od
     else return NONE) st = (rb,sb) ==> cs_extends st sb
Proof
  rpt gen_tac >> Cases_on `hr` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[cj 1 emit_op_labels, pairTheory.SND, cs_extends_refl]
QED

Theorem internal_immutable_region_extends:
  !ctor imm st op sb.
    (if ctor /\ imm > 0 then
       do ar <- compile_fixed_region_with_id imm;
          return (SOME (SND ar).buf_operand) od
     else return NONE) st = (op,sb) ==> cs_extends st sb
Proof
  rpt gen_tac >> Cases_on `ctor /\ imm > 0` >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  metis_tac[cj 1 compile_fixed_region_with_id_labels, pairTheory.SND,
            cs_extends_refl]
QED

Theorem internal_return_region_extends:
  !ce rt st sb.
    (case rt of NONE => return () | SOME ty =>
       if ce.ce_returns_count > 0 then
         do compile_alloc_buffer (type_memory_bytes ce ty); return () od
       else return ()) st = ((),sb) ==> cs_extends st sb
Proof
  rpt gen_tac >> Cases_on `rt` >> simp[comp_return_def] >>
  strip_tac >> gvs[]
  >- simp[cs_extends_refl] >>
  rename1 `type_memory_bytes ce ty` >>
  Cases_on `ce.ce_returns_count > 0` >> gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def]
  >- (pairarg_tac >> gvs[] >>
      metis_tac[cj 1 compile_alloc_buffer_labels, pairTheory.SND]) >>
  simp[cs_extends_refl]
QED

Theorem internal_function_exit_extends:
  !done nr key trans view rt rpc st sb.
    (if done then return () else
       do (if nr then compile_nonreentrant_unlock key trans view else return ());
          (case rt of NONE => emit_inst RET [rpc] []
                    | SOME ty => emit_inst INVALID [] []) od) st = ((),sb) ==>
    cs_extends st sb
Proof
  rpt gen_tac >> Cases_on `done` >> simp[comp_return_def]
  >- (strip_tac >> gvs[] >> simp[cs_extends_refl]) >>
  simp[comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `(if nr then _ else _) st = (_,mid)` >>
  `cs_extends st mid` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[cj 6 stmt_context_helpers_labels, pairTheory.SND, cs_extends_refl]) >>
  `cs_extends mid sb` by
    (Cases_on `rt` >> gvs[] >>
     metis_tac[cj 1 emit_inst_labels, pairTheory.SND]) >>
  metis_tac[cs_extends_trans]
QED
