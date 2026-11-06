(* TOP-LEVEL: checked compatible field types and saved Log arguments supply
   the indexed-topic execution relation, including bytestring address bounds.
   API: compatible_log_args_topic_values. Helpers: log_args_topic_values,
   log_arg_topic_value, compatible_indexable_types, event_arg_compatible_indexable.
   Non-indexed values retain arbitrary recursive types. *)
Theory eventLogTopicInputs
Ancestors
  vyperEventArgCompat
  typedLogArgs eventTopicValueProps valueLoadProps valueEncoding
  vyperTypeContract vyperTypeSystem compileEnv venomState list pair words arithmetic

Theorem event_arg_compatible_indexable:
  !fty aty. event_indexable_type fty /\ event_arg_compatible fty aty ==> event_indexable_type aty
Proof
  Cases_on `fty` >> Cases_on `aty` >> gvs[event_indexable_type_def, event_arg_compatible_def]
QED

Theorem compatible_indexable_types:
  !flags ftys atys.
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags ftys /\
    LIST_REL event_arg_compatible ftys atys ==>
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags atys
Proof
  Induct_on `flags`
  >- (Cases_on `ftys` >> Cases_on `atys` >> simp[]) >>
  rpt gen_tac >> Cases_on `ftys` >> Cases_on `atys` >> simp[] >> strip_tac >> conj_tac
  >- (strip_tac >> fs[] >> drule_all event_arg_compatible_indexable >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_arg_topic_value:
  !tenv src ty tv v ss dst byte_count.
    event_indexable_type ty /\ evaluate_type tenv ty = SOME tv /\ lowered_value_rel ty tv v src ss /\
    log_arg_safe src ty tv ss dst byte_count ==>
    topic_value_rel tenv (src,ty) v ss
Proof
  rpt gen_tac >> strip_tac >>
  `!addr. is_bytestring_type ty /\ eval_operand src ss = SOME addr ==>
    w2n addr + val_memory_size v <= dimword(:256)` by
    (qx_gen_tac `addr` >> strip_tac >>
     `~is_word_type ty` by (drule_all bytestring_type_not_word >> simp[]) >>
     `value_has_type tv v` by fs[lowered_value_rel_def] >>
     `val_memory_size v <= type_memory_size tv` by (drule_all bytestring_value_size_bound >> simp[]) >>
     qpat_x_assum `log_arg_safe _ _ _ _ _ _` (mp_tac o REWRITE_RULE [log_arg_safe_def]) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> disch_then (qspec_then `addr` mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >> decide_tac) >>
  drule_all lowered_value_rel_topic_value_rel >> simp[]
QED

Theorem log_args_topic_values:
  !args atvs values flags tenv ss dst byte_count.
    LENGTH flags = LENGTH args /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags (MAP SND args) /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) args atvs /\
    log_args_rel args atvs values ss /\ log_args_safe args atvs ss dst byte_count ==>
    LIST_REL (\(flag,arg) v. flag ==> topic_value_rel tenv arg v ss) (ZIP (flags,args)) values
Proof
  Induct_on `args`
  >- (rpt gen_tac >> Cases_on `flags` >> Cases_on `atvs` >> Cases_on `values` >>
      simp[log_args_rel_def, log_args_safe_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `atvs`, `values`, `flags`, `tenv`, `ss`, `dst`, `byte_count`] >>
  Cases_on `arg` >> Cases_on `flags` >> Cases_on `atvs` >> Cases_on `values` >>
  simp_tac (srw_ss()) [log_args_rel_def, log_args_safe_def] >> strip_tac >>
  rename1 `lowered_value_rel ty tv value src ss` >>
  rename1 `log_args_rel args rest_tvs rest_values ss` >>
  rename1 `LIST_REL (\flag ty. flag ==> event_indexable_type ty) rest_flags (MAP SND args)` >>
  conj_tac
  >- (DISCH_TAC >> mp_tac (Q.SPECL [`tenv`, `src`, `ty`, `tv`, `value`, `ss`, `dst`, `byte_count`]
        log_arg_topic_value) >> simp[]) >>
  qpat_x_assum `!atvs values flags tenv ss dst byte_count. _`
    (qspecl_then [`rest_tvs`, `rest_values`, `rest_flags`, `tenv`, `ss`, `dst`, `byte_count`] mp_tac) >> simp[]
QED

Theorem compatible_log_args_topic_values:
  !args atvs values flags field_types tenv ss dst byte_count.
    LENGTH flags = LENGTH args /\
    LIST_REL event_arg_compatible field_types (MAP SND args) /\
    LIST_REL (\flag ty. flag ==> event_indexable_type ty) flags field_types /\
    LIST_REL (\arg tv. evaluate_type tenv (SND arg) = SOME tv) args atvs /\
    log_args_rel args atvs values ss /\ log_args_safe args atvs ss dst byte_count ==>
    LIST_REL (\(flag,arg) v. flag ==> topic_value_rel tenv arg v ss) (ZIP (flags,args)) values
Proof
  rpt gen_tac >> strip_tac >> drule_all compatible_indexable_types >> DISCH_TAC >>
  drule_all log_args_topic_values >> simp[]
QED
