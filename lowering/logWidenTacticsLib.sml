(* Goal-directed scalar representation tactics for the Log consumers.
   No theorem values are manufactured or cached here. *)
structure logWidenTacticsLib =
struct
open HolKernel boolLib bossLib
open supportedTypesTheory vyperValueTheory compileEnvTheory
     valueCopyBytesTheory valueTypingMemoryPropsTheory
     exprSimDefsTheory exprSimPropsTheory loweringPostsTheory
     stmtSimLogArgsTheory
open vyperEventArgCompatTheory
open listTheory eventLoweringStructureTheory stmtSimLogTraceTheory
     stmtSimLogSuffixCodeTheory loweringSliceTheory emitHelperPropsTheory
     exprLoweringPropsTheory loweringStateRelDefsTheory
     vyperEventCompatibilityTheory stmtSimLogArgsGrowthTheory fragExecTheory

fun scalar_evaluate ty =
  qpat_x_assum ([QUOTE "type_memory_bytes _ ("] @ ty @ [QUOTE ") < dimword (:256)"]) mp_tac >>
  qpat_x_assum ([QUOTE "supported_scalar_type ("] @ ty @ [QUOTE ")"]) mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  Cases_on ty >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_word_type_def, supported_string_type_def,
      evaluate_type_def, type_memory_bytes_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
       gvs[supported_word_type_def, supported_string_type_def,
           evaluate_type_def, type_memory_bytes_def, type_slot_size_def,
           vfmConstantsTheory.word_size_def]) >>
  gvs[supported_int_width_def] >>
  rename1 `cap < dimword (:256)` >>
  qspec_then `32` mp_tac arithmeticTheory.DIVISION >>
  (impl_tac >- decide_tac) >>
  disch_then (qspec_then `cap+31` strip_assume_tac) >> decide_tac

fun scalar_transport cases =
  rename1 `event_arg_compatible dst src` >>
  `src = dst \/ (is_bytestring_type src /\ is_bytestring_type dst)` by
    (drule cases >> strip_tac >>
     gvs[supported_scalar_type_def, supported_word_type_def,
         supported_string_type_def, is_bytestring_type_def]) >>
  Cases_on `src = dst` >- gvs[] >>
  gvs[] >>
  rename1 `evaluate_type (get_tenv cx) src = SOME stv` >>
  rename1 `evaluate_type (get_tenv cx) dst = SOME dtv` >>
  rename1 `value_has_type stv v` >>
  `val_footprint stv v = val_footprint dtv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[value_has_type_memory_wf] >>
  `~is_word_type src /\ ~is_word_type dst` by
    metis_tac[is_bytestring_word_type] >>
  `?sbt. stv = BaseTV sbt` by metis_tac[bytestring_type_value] >>
  `?dbt. dtv = BaseTV dbt` by metis_tac[bytestring_type_value] >>
  gvs[log_arg_rel_def] >>
  conj_tac >-
    (fs[expr_val_rel_def] >>
     metis_tac[bytestring_val_in_memory_transfer]) >>
  conj_tac >-
    (fs[expr_val_at_def] >> rpt strip_tac >> gvs[] >>
     metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]) >>
  fs[log_arg_clear_def] >> rpt strip_tac >>
  metis_tac[local_val_at_base, arithmeticTheory.LESS_EQ_REFL]

fun declared_evaluation g = (
  TRY strip_tac >> Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (ys,sm)` >>
  `LENGTH ys = LENGTH args` by
    (mp_tac (Q.SPECL [`cenv`,`args`,`sa`] compile_log_eval_all_length) >> simp[]) >>
  `MAP SND ys = MAP (lowered_value_type cenv) args` by
    (mp_tac (Q.SPECL [`cenv`,`args`,`sa`] compile_log_eval_all_types) >> simp[])) g

fun declared_pairs g = (
  qabbrev_tac `xs = ZIP (MAP FST ys,tys)` >>
  `MAP SND xs = tys /\ LENGTH xs = LENGTH args` by simp[Abbr `xs`, MAP_ZIP]) g

fun declared_arguments g = (
  declared_evaluation >>
  `LENGTH tys = LENGTH args` by metis_tac[LIST_REL_LENGTH] >>
  declared_pairs) g

fun declared_view g = (
  `log_eval_view cenv args sa xs sm` by
    (simp[log_eval_view_def, LIST_REL_EL_EQN, Abbr `xs`, EL_ZIP, EL_MAP] >>
     rpt strip_tac >>
     qpat_x_assum `MAP SND ys = _` (mp_tac o Q.AP_TERM `EL n`) >>
     gvs[EL_MAP, LIST_REL_EL_EQN] >> metis_tac[])) g

fun declared_topics g = (
  Cases_on `compile_log_topic_ops (FST (split_log_ops xs flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (ops,st)` >>
  `EVERY (supported_scalar_type o SND) xs` by
    (gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  `LENGTH flags = LENGTH xs` by decide_tac >>
  `cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags)` by simp[]) g

fun declared_frames g = (
  drule_all log_success_suffix_code >> strip_tac >>
  `cs_extends sa sm` by (drule_all compile_log_eval_all_grows >> simp[]) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[])) g

fun declared_structure_finish g = (
  map_every qexists_tac [`ys`,`xs`,`sm`,`ops`,`st`] >>
  simp[markerTheory.Abbrev_def] >> fs[markerTheory.Abbrev_def] >>
  metis_tac[fn_has_code_mid, cs_extends_refl]) g

fun declared_structure g = (
  declared_arguments >> declared_view >> declared_topics >>
  declared_frames >> declared_structure_finish) g

fun compatible_cases g = (
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def]) g

fun with_cases tac g = (
  `(!fty aty. event_arg_compatible fty aty ==>
     aty = fty \/
     (?n m. fty = BaseT (StringT n) /\ aty = BaseT (StringT m)) \/
     (?n m. fty = BaseT (BytesT (Dynamic n)) /\
            aty = BaseT (BytesT (Dynamic m))) \/
     (?t b. fty = ArrayT t b) \/ (?ts. fty = TupleT ts)) /\
   (!fs ats. event_arg_compatible_list fs ats ==> T)` by compatible_cases >>
  qpat_x_assum `!fty aty. event_arg_compatible fty aty ==> _` tac) g

fun physical_tags cases g = (
  gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rpt strip_tac >>
  qpat_x_assum `!n. n < LENGTH tys ==> event_arg_compatible _ _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qpat_assum `!n. n < LENGTH tys ==> supported_scalar_type (EL n tys)`
    (qspec_then `n` mp_tac) >> simp_tac bool_ss [] >>
  (impl_tac >- simp[]) >>
  disch_then (mp_tac o REWRITE_RULE [supported_scalar_type_def]) >>
  strip_tac >> drule cases >> strip_tac >>
  gvs[is_bytestring_type_def, supported_word_type_def, supported_string_type_def]) g

fun source_witness scalar g = (
  gvs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
       Abbr `ds`, Abbr `axs`, EL_ZIP, Excl "enc_def"] >>
  rpt strip_tac >> qexists_tac `expr_type (EL n args)` >>
  qpat_x_assum `!n. n < LENGTH vs ==> ?tv. _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `tv` >> simp[] >>
  `supported_scalar_type (EL n tys)` by simp[] >>
  `event_arg_compatible (EL n tys) (expr_type (EL n args))` by simp[] >>
  drule_all scalar >> strip_tac >> simp[]) g

fun topics_eq scalar g = (
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >> Cases_on `flags` >> Cases_on `vals` >>
  simp[vyperEventTheory.encode_indexed_event_topics_def] >>
  rename1 `encode_indexed_event_topics (flg::_) _ _` >>
  Cases_on `flg` >> simp[vyperEventTheory.encode_indexed_event_topics_def] >>
  drule_all scalar >> simp[]) g

fun non_indexed g = (
  Induct >> rpt gen_tac >> strip_tac
  >- (Cases_on `tys` >> gvs[log_non_indexed_types_def]) >>
  Cases_on `tys` >> gvs[log_non_indexed_types_def, LIST_REL_CONS1] >>
  rename1 `log_non_indexed_types (flg::_) _` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `flg` >> simp[log_non_indexed_types_def]) g

fun abi_eq scalar g = (
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS1] >> drule_all scalar >>
  disch_then (qspec_then `tenv` strip_assume_tac) >>
  Cases_on `vals` >> simp[]) g

fun encoding_facts scalar g = (
  `!tys atys flags vals.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    encode_indexed_event_topics flags atys vals =
    encode_indexed_event_topics flags tys vals` by (POP_ASSUM_LIST (K all_tac) >> topics_eq scalar) >>
  `!flags tys atys.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
    LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags atys)` by (POP_ASSUM_LIST (K all_tac) >> non_indexed) >>
  `!tys atys vals tenv.
    EVERY supported_scalar_type tys /\ LIST_REL event_arg_compatible tys atys ==>
    vyper_to_abi_types tenv atys = vyper_to_abi_types tenv tys /\
    vyper_to_abi_list tenv atys vals = vyper_to_abi_list tenv tys vals` by (POP_ASSUM_LIST (K all_tac) >> abi_eq scalar) >>
  `EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
   LIST_REL event_arg_compatible (log_non_indexed_types flags tys)
      (log_non_indexed_types flags (MAP expr_type args))` by metis_tac[] >>
  metis_tac[]) g

fun selected_data cases g = (
  qpat_assum `LIST_REL (\arg v. supported_scalar_type (SND arg) /\ _) ds vs`
    (mp_then Any mp_tac stmtSimLogTopicsTheory.split_log_ops_data_rel) >>
  disch_then (qspec_then `flags` mp_tac) >> simp[] >> strip_tac >>
  `MAP SND (SND (split_log_ops ds flags)) = log_non_indexed_types flags tys` by
    metis_tac[stmtSimLogTopicsTheory.split_log_ops_data_types] >>
  qpat_x_assum `SUM _ < dimword (:256)` mp_tac >>
  qpat_x_assum `MAP SND (SND _) = _` (rewrite_tac o single o GSYM) >>
  simp[MAP_MAP_o, combinTheory.o_DEF] >> strip_tac >>
  gvs[LIST_REL_EL_EQN, Excl "enc_def"] >> gen_tac >> disch_tac >>
  qpat_x_assum `!n. n < LENGTH (log_non_indexed_values flags vs) ==> _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  qabbrev_tac `dty = SND (EL n (SND (split_log_ops ds flags)))` >>
  `type_memory_bytes cenv dty < dimword (:256)` by
    (qspecl_then [`type_memory_bytes cenv o SND`,
                   `SND (split_log_ops ds flags)`,`n`] mp_tac
       abiEncoderInputTheory.abi_encoder_prefix_sum_bound >>
     simp[Abbr `dty`, combinTheory.o_DEF] >> decide_tac) >>
  `?dtv. evaluate_type (get_tenv cx) dty = SOME dtv` by scalar_evaluate `dty` >>
  drule_all (CONJUNCT1 event_arg_compatible_value_has_type) >> strip_tac >>
  qpat_x_assum `log_arg_rel _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `event_arg_compatible _ _` mp_tac >>
  qpat_x_assum `evaluate_type _ dty = SOME _` mp_tac >>
  qpat_x_assum `evaluate_type _ aty = SOME _` mp_tac >>
  qpat_x_assum `value_has_type tv _` mp_tac >>
  qpat_x_assum `value_has_type dtv _` mp_tac >>
  qpat_x_assum `supported_scalar_type aty` mp_tac >>
  qpat_x_assum `supported_scalar_type dty` mp_tac >>
  qpat_x_assum `Abbrev (dty = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  reverse conj_tac >- simp[] >>
  Cases_on `EL n (SND (split_log_ops ds flags))` >>
  gvs[markerTheory.Abbrev_def] >> scalar_transport cases) g

end
