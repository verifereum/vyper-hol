(* Compiler-only adapters for the shared reason encoder. *)
Theory reasonCompilerFramePtr
Ancestors reasonTupleFramePtr emitHelperProps exprLoweringProps emitHelper compileEnv loweringStateRelDefs fragExec venomState arithmetic

Theorem reason_emit_op_explicit:
  emit_op opc ops sa = (Var out,sb) ==>
  out = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst opc ops [out] (sa with cs_next_var := sa.cs_next_var + 1) = ((),sb)
Proof
  simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >> strip_tac >> gvs[]
QED

Theorem reason_emit_inst_counter:
  emit_inst opc ops outs sa = ((),sb) ==>
  emit_inst opc ops outs (sa with cs_next_var := k) =
    ((),sb with cs_next_var := k)
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem reason_emit_void_counter:
  emit_void opc ops sa = ((),sb) ==>
  emit_void opc ops (sa with cs_next_var := k) =
    ((),sb with cs_next_var := k)
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
       comp_return_def] >> strip_tac >> gvs[]
QED

Theorem reason_emit_op_counter:
  emit_op opc ops sa = (Var out,sb) ==>
  emit_inst opc ops [out] (sa with cs_next_var := k) =
    ((),sb with cs_next_var := k)
Proof
  strip_tac >> drule reason_emit_op_explicit >> strip_tac >>
  drule reason_emit_inst_counter >>
  disch_then (qspec_then `k` mp_tac) >> simp[]
QED

Theorem reason_fn_has_code_counter:
  fn_has_code (sa with cs_next_var := k) (sb with cs_next_var := j) func <=>
  fn_has_code sa sb func
Proof
  simp[fn_has_code_def, emitted_blocks_def]
QED

Theorem reason_fresh_vars_lookup_frame:
  fresh_vars_wrt sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  (!p. MEM p outputs ==> not_fresh_at sb p) /\
  (!p. ~MEM p outputs ==> lookup_var p t = lookup_var p s) ==>
  fresh_vars_wrt sb t
Proof
  simp[fresh_vars_wrt_def, not_fresh_at_def, GREATER_EQ, lookup_var_def,
       finite_mapTheory.FLOOKUP_DEF] >> rpt strip_tac >>
  `~MEM (STRING #"%" (toString n)) outputs` by metis_tac[] >>
  first_x_assum drule >> simp[] >> metis_tac[LESS_EQ_TRANS]
QED

(* Compiler freshness is name separation, not absence from runtime maps. *)
Theorem reason_tuple_copy_names:
  emit_op MLOAD [Var src] sa = (Var v1,c1) /\
  emit_op ADD [Var v1;Lit 31w] c1 = (Var v2,c2) /\
  emit_op AND [Var v2;Lit (i2w (-32))] c2 = (Var v3,c3) /\
  emit_op ADD [Lit 32w;Var v3] c3 = (Var v4,c4) /\
  emit_void MCOPY [Var dst;Var src;Var v4] c4 = ((),sb) ==>
  (!p. not_fresh_at sa p ==> p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!p. MEM p [v1;v2;v3;v4] ==> not_fresh_at sb p) /\
  (!p. MEM p [v1;v2;v3;v4] ==>
    ?n. p = STRING #"%" (toString n) /\ sa.cs_next_var <= n)
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[not_fresh_at_def, GREATER_EQ, ASCIInumbersTheory.toString_inj] >>
  rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem reason_tuple_copy_nonlocal:
  emit_op MLOAD [Var src] sa = (Var v1,c1) /\
  emit_op ADD [Var v1;Lit 31w] c1 = (Var v2,c2) /\
  emit_op AND [Var v2;Lit (i2w (-32))] c2 = (Var v3,c3) /\
  emit_op ADD [Lit 32w;Var v3] c3 = (Var v4,c4) /\
  emit_void MCOPY [Var dst;Var src;Var v4] c4 = ((),sb) /\
  local_ptrs_reserved cenv sa ==>
  !p. MEM p [v1;v2;v3;v4] ==> not_local_ptr cenv scopes p
Proof
  strip_tac >> drule_all reason_tuple_copy_names >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
  irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]
QED

Theorem reason_tuple_copy_fresh_names:
  emit_op MLOAD [Var src] sa = (Var v1,c1) /\
  emit_op ADD [Var v1;Lit 31w] c1 = (Var v2,c2) /\
  emit_op AND [Var v2;Lit (i2w (-32))] c2 = (Var v3,c3) /\
  emit_op ADD [Lit 32w;Var v3] c3 = (Var v4,c4) /\
  emit_void MCOPY [Var dst;Var src;Var v4] c4 = ((),sb) /\
  fresh_vars_wrt sa s /\ not_fresh_at sa src /\ not_fresh_at sa dst ==>
  (!p. p = src \/ p = dst ==> p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4) /\
  (!p. MEM p [v1;v2;v3;v4] ==> lookup_var p s = NONE) /\
  sa.cs_next_var <= sb.cs_next_var /\
  (!p. MEM p [v1;v2;v3;v4] ==> not_fresh_at sb p)
Proof
  strip_tac >> drule_all reason_tuple_copy_names >> strip_tac >>
  rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      gvs[fresh_vars_wrt_def, lookup_var_def, finite_mapTheory.FLOOKUP_DEF]) >>
  simp[]
QED
