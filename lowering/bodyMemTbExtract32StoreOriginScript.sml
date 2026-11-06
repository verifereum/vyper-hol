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

Theorem extract32_typed_memory_delta_family:
  (!ce dst dt src st.
    !sa v u sb. not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
    compile_store_memory_typed ce dst dt src st sa = (u,sb) ==>
    ?ds.
      FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
      (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
      EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds) /\
  (!ce dst src dts sts doff soff.
    !sa v u sb. not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
    compile_typed_copy_fields ce dst src dts sts doff soff sa = (u,sb) ==>
    ?ds.
      FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
      (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
      EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds) /\
  (!ce dst dt src st count.
    !sa v u sb. not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
    compile_copy_sarray_typed ce dst dt src st count sa = (u,sb) ==>
    ?ds.
      FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
      (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
      EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds) /\
  (!ce dst dt cap src st.
    !sa v u sb. not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
    compile_copy_dynarray_typed ce dst dt cap src st sa = (u,sb) ==>
    ?ds.
      FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
      (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
      EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds) /\
  (!ce dst src dfs sfs doff soff.
    !sa v u sb. not_fresh_at sa v /\ dst <> Var v /\ src <> Var v /\
    compile_struct_typed_copy ce dst src dfs sfs doff soff sa = (u,sb) ==>
    ?ds.
      FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
      (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ ds /\
      EVERY (\i. ~MEM v i.inst_outputs /\ ~MEM (Var v) i.inst_operands) ds)
Proof
  ho_match_mp_tac contextTheory.compile_store_memory_typed_ind >>
  rpt conj_tac
  >- suspend "dispatch"
  >- suspend "fields_nil"
  >- suspend "fields_mismatch"
  >- suspend "fields_cons"
  >- suspend "sarray"
  >- suspend "dynarray"
  >- suspend "struct_nil"
  >> suspend "struct_cons"
QED

Resume extract32_typed_memory_delta_family[fields_nil]:
  simp[Once compile_store_memory_typed_def, comp_return_def]
QED

Resume extract32_typed_memory_delta_family[fields_mismatch]:
  simp[Once compile_store_memory_typed_def, comp_return_def]
QED

Resume extract32_typed_memory_delta_family[struct_nil]:
  simp[Once compile_store_memory_typed_def, comp_return_def]
QED

Resume extract32_typed_memory_delta_family[dispatch]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `is_word_type dt`
  >- (gvs[Once compile_store_memory_typed_def, comp_bind_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      every_assum (fn eq => TRY (store_emit_mono_tac eq)) >>
      imp_res_tac compiler_ci_mono_not_fresh >>
      rpt (CHANGED_TAC (every_assum (fn eq => TRY (store_emit_delta_tac eq)))) >>
      drule_at (Pos last) extract32_emit_void_excluded_register >>
      disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
      simp[APPEND_ASSOC, EVERY_APPEND]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- (gvs[Once compile_store_memory_typed_def] >>
      drule_all extract32_store_bytestring_delta_excluded >> simp[]) >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (Cases_on `dt` >> Cases_on `st` >>
      TRY (rename1 `compile_store_memory_typed ce dst (ArrayT dty db) src (ArrayT sty sbnd) sa` >>
           Cases_on `db` >> Cases_on `sbnd`) >>
      gvs[] >>
      qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
      simp[Once compile_store_memory_typed_def] >> strip_tac >>
      TRY (drule_all extract32_copy_memory_delta_excluded >>
           simp[APPEND_ASSOC] >> NO_TAC) >>
      metis_tac[]) >>
  gvs[Once compile_store_memory_typed_def] >>
  drule_at (Pos last) extract32_emit_void_excluded_register >>
  disch_then (qspec_then `v` mp_tac) >> simp[]
QED

Theorem extract32_with_byte_offset_mono[local]:
  !bufop off sa. ci_mono sa (SND (compile_with_byte_offset bufop off sa))
Proof
  rpt gen_tac >> simp[compile_with_byte_offset_def] >>
  IF_CASES_TAC >> simp[comp_return_def, ci_mono_refl, ci_mono_emit_op]
QED

fun typed_store_mono_tac eq =
  MAP_FIRST (fn mono => fn goal =>
    let val inst = PART_MATCH (rand o rand) mono (lhs (concl eq))
    in assume_tac (REWRITE_RULE [eq, pairTheory.SND] inst) goal end)
    [extract32_with_byte_offset_mono, cj 1 ci_mono_typed_memory_family,
     cj 2 ci_mono_typed_memory_family, cj 3 ci_mono_typed_memory_family,
     cj 4 ci_mono_typed_memory_family, cj 5 ci_mono_typed_memory_family];

fun typed_store_offset_tac eq = fn goal =>
  (mp_then (Pos last) (qspec_then `v` mp_tac)
     extract32_with_byte_offset_result_excluded eq >>
   (impl_tac >- (simp[] >> NO_TAC)) >> strip_tac >>
   mp_then (Pos last) (qspec_then `v` mp_tac)
     extract32_with_byte_offset_delta_excluded eq >>
   (impl_tac >- (simp[] >> NO_TAC)) >> strip_tac >>
   WEAKEN_TAC (aconv (concl eq))) goal;

Resume extract32_typed_memory_delta_family[fields_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  every_assum (fn eq => TRY (typed_store_mono_tac eq)) >>
  ntac 4 (imp_res_tac compiler_ci_mono_not_fresh) >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (typed_store_offset_tac eq)))) >>
  gvs[] >>
  qpat_x_assum `!dst' src' sa' v' sb. _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sa' v' sb. _` (drule_all_then strip_assume_tac) >>
  simp[APPEND_ASSOC, EVERY_APPEND]
QED

Resume extract32_typed_memory_delta_family[struct_cons]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `ALOOKUP sfs name` >>
  TRY (rename1 `SOME p` >> PairCases_on `p`) >> gvs[] >>
  qpat_x_assum `compile_struct_typed_copy _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  every_assum (fn eq => TRY (typed_store_mono_tac eq)) >>
  ntac 4 (imp_res_tac compiler_ci_mono_not_fresh) >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (typed_store_offset_tac eq)))) >>
  gvs[] >>
  qpat_x_assum `!dst' src' sa' v' sb. _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!sa' v' sb. _` (drule_all_then strip_assume_tac) >>
  simp[APPEND_ASSOC, EVERY_APPEND]
QED

Resume extract32_typed_memory_delta_family[sarray]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def] >>
  IF_CASES_TAC
  >- (strip_tac >> drule_all extract32_copy_memory_delta_excluded >> simp[]) >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  every_assum (fn eq => TRY (extract32_call_mono_tac eq)) >>
  every_assum (fn eq => TRY (typed_store_mono_tac eq)) >>
  ntac 20 (imp_res_tac compiler_ci_mono_not_fresh) >>
  qpat_assum `fresh_var _ = _`
    (mp_then (Pos hd) (qspec_then `v` mp_tac) extract32_fresh_var_excluded_register) >>
  simp[] >> strip_tac >>
  rpt (CHANGED_TAC (every_assum (fn eq => TRY (extract32_call_delta_tac eq)))) >>
  gvs[] >>
  qpat_x_assum `!dst' src' sa' v' sb. _` (drule_all_then strip_assume_tac) >>
  imp_res_tac extract32_fresh_label_chronological >>
  imp_res_tac extract32_fresh_var_chronological >>
  imp_res_tac extract32_new_block_chronological >>
  simp[APPEND_ASSOC, EVERY_APPEND]
QED
