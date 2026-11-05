Theory bodyMemTbExtract32StoreOrigin
Ancestors
  bodyMemTbExtract32RecursiveOrigin bodyMemTbExtract32Emission
  context exprLoweringProps exprOperandVar compileEnv venomInst list pair

Theorem extract32_copy_memory_delta_excluded:
  not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
  compile_copy_memory dst src n sa = (u,sb) ==>
  ?ds.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds
Proof
  Cases_on `n`
  >- simp[compile_copy_memory_def, comp_return_def] >>
  simp[compile_copy_memory_def] >> rpt strip_tac >>
  drule_at (Pos last) extract32_emit_void_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_copy_memory_dynamic_delta_excluded:
  not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\ len <> Var v /\
  compile_copy_memory_dynamic dst src len sa = (u,sb) ==>
  ?ds.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds
Proof
  simp[compile_copy_memory_dynamic_def] >> rpt strip_tac >>
  drule_at (Pos last) extract32_emit_void_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_with_byte_offset_result_excluded:
  not_fresh_at sa v /\ bufop <> Var v /\
  compile_with_byte_offset bufop off sa = (r,sb) ==> r <> Var v
Proof
  Cases_on `off = 0` >> simp[compile_with_byte_offset_def, comp_return_def] >>
  rpt strip_tac >> gvs[] >>
  drule_at (Pos last) extract32_emit_op_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_with_byte_offset_delta_excluded:
  not_fresh_at sa v /\ bufop <> Var v /\
  compile_with_byte_offset bufop off sa = (r,sb) ==>
  ?ds.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds
Proof
  Cases_on `off = 0`
  >- simp[compile_with_byte_offset_def, comp_return_def] >>
  simp[compile_with_byte_offset_def] >> rpt strip_tac >>
  drule_at (Pos last) extract32_emit_op_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> metis_tac[]
QED

(* Local support for finite sequences of primitive emissions. *)
fun store_emit_mono_tac eq = fn goal =>
  let val inst = PART_MATCH (rand o rand) ci_mono_emit_op (lhs (concl eq))
  in assume_tac (REWRITE_RULE [eq, pairTheory.SND] inst) goal end;

fun store_emit_delta_tac eq =
  mp_then (Pos last) (qspec_then `v` mp_tac)
    extract32_emit_op_excluded_register eq >>
  (impl_tac >- (simp[] >> NO_TAC)) >> strip_tac >>
  WEAKEN_TAC (aconv (concl eq));

Theorem extract32_bytestring_copy_len_result_excluded:
  not_fresh_at sa v /\ src <> Var v /\
  compile_bytestring_copy_len src sa = (r,sb) ==> r <> Var v
Proof
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  every_assum (fn eq => TRY (store_emit_mono_tac eq)) >>
  ntac 3 (imp_res_tac compiler_ci_mono_not_fresh) >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (store_emit_delta_tac eq)))) >>
  simp[]
QED

Theorem extract32_bytestring_copy_len_delta_excluded:
  not_fresh_at sa v /\ src <> Var v /\
  compile_bytestring_copy_len src sa = (r,sb) ==>
  ?ds.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds
Proof
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  every_assum (fn eq => TRY (store_emit_mono_tac eq)) >>
  ntac 3 (imp_res_tac compiler_ci_mono_not_fresh) >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (store_emit_delta_tac eq)))) >>
  simp[listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND]
QED

Theorem extract32_store_bytestring_delta_excluded:
  not_fresh_at sa v /\ src <> Var v /\ dst <> Var v /\
  compile_store_bytestring src dst sa = (u,sb) ==>
  ?ds.
    FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
    (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
    EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds
Proof
  rpt strip_tac >>
  Cases_on `compile_bytestring_copy_len src sa` >>
  rename1 `compile_bytestring_copy_len src sa = (len,s1)` >>
  gvs[compile_store_bytestring_def, comp_bind_def] >>
  `ci_mono sa s1` by
    (`!s. ci_mono s (SND (compile_bytestring_copy_len src s))` by
       (simp[compile_bytestring_copy_len_def] >>
        rpt (CHANGED_TAC (rpt gen_tac >>
          TRY (irule ci_mono_bind >> conj_tac) >> simp[ci_mono_emit_op]))) >>
     metis_tac[pairTheory.SND]) >>
  `not_fresh_at s1 v` by (irule compiler_ci_mono_not_fresh >> metis_tac[]) >>
  drule_at (Pos last) extract32_bytestring_copy_len_result_excluded >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pos last) extract32_bytestring_copy_len_delta_excluded >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  drule_at (Pos last) extract32_emit_void_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
  simp[listTheory.APPEND_ASSOC, listTheory.EVERY_APPEND]
QED
