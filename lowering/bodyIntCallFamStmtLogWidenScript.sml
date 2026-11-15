(* The intcall Log step with argument types compatible with, rather than
   equal to, the event's declared field types.  The evaluated arguments are
   viewed at the declared types: log_eval_view only asks the operands and
   bytestring-ness to agree, and a scalar argument's value relation moves
   from its own type to a compatible declared type, since a bytestring's
   layout and footprint ignore its bound.  The declared types must evaluate:
   a non-indexed one does by log_alloc_ok's bound, an indexed one is a
   premise of the caller. *)
Theory bodyIntCallFamStmtLogWiden
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogArgs
  stmtSimLogCompose stmtSimLogTrace stmtSimLogArgs stmtSimLogArgsGrowth
  stmtSimLogSuffixCode eventLoweringStructure fragExec
  exprSimSubscriptMap gasOutcome loweringPosts emitHelperProps exprLoweringProps
  compileEnv exprLowering valueEncoding valueEncodingDefs valueTypingMemoryProps
  supportedTypes vyperEventArgCompat vyperEventCompatibility vyperTyping vyperValue
  vyperInterpreter vyperState list

(* ===== Compatible scalar types ===== *)

Theorem event_arg_compatible_scalar_cases:
  (!fty aty. event_arg_compatible fty aty ==>
     aty = fty \/
     (?n m. fty = BaseT (StringT n) /\ aty = BaseT (StringT m) /\ m <= n) \/
     (?n m. fty = BaseT (BytesT (Dynamic n)) /\
            aty = BaseT (BytesT (Dynamic m)) /\ m <= n) \/
     (?t b. fty = ArrayT t b) \/ (?ts. fty = TupleT ts)) /\
  (!fs ats. event_arg_compatible_list fs ats ==> T)
Proof
  ho_match_mp_tac event_arg_compatible_ind >> rw[event_arg_compatible_def]
QED

Theorem compatible_scalar_type:
  supported_scalar_type fty /\ event_arg_compatible fty aty ==>
  supported_scalar_type aty /\
  (is_bytestring_type aty <=> is_bytestring_type fty)
Proof
  strip_tac >> drule (CONJUNCT1 event_arg_compatible_scalar_cases) >>
  strip_tac >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def, is_bytestring_type_def]
QED

Theorem compatible_scalar_types:
  !tys atys.
    LIST_REL event_arg_compatible tys atys /\
    EVERY supported_scalar_type tys ==>
    EVERY supported_scalar_type atys
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[compatible_scalar_type]
QED

(* ===== Moving an argument's value relation to its declared type ===== *)

Theorem evaluate_bytestring_type[local]:
  (evaluate_type tenv (BaseT (StringT n)) = SOME tv ==>
   tv = BaseTV (StringT n)) /\
  (evaluate_type tenv (BaseT (BytesT (Dynamic n))) = SOME tv ==>
   tv = BaseTV (BytesT (Dynamic n)))
Proof
  rw[evaluate_type_def]
QED

Theorem bytestring_retype_facts[local]:
  value_has_type (BaseTV bt1) v /\
  ((?m n. bt1 = StringT m /\ bt2 = StringT n /\ m <= n) \/
   (?m n. bt1 = BytesT (Dynamic m) /\ bt2 = BytesT (Dynamic n) /\ m <= n)) ==>
  value_has_type (BaseTV bt2) v /\
  (!a mem. val_in_memory (BaseTV bt2) v a mem =
           val_in_memory (BaseTV bt1) v a mem) /\
  val_footprint (BaseTV bt2) v = val_footprint (BaseTV bt1) v /\
  val_wf (BaseTV bt1) v /\ val_wf (BaseTV bt2) v /\
  val_footprint (BaseTV bt1) v <= type_memory_size (BaseTV bt1) /\
  val_footprint (BaseTV bt2) v <= type_memory_size (BaseTV bt2)
Proof
  strip_tac >> gvs[] >>
  qspec_then `m` assume_tac word_size_capacity >>
  qspec_then `n` assume_tac word_size_capacity >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  simp[val_in_memory_def, val_footprint_def, val_wf_def, type_memory_size_def]
QED

Theorem local_val_at_retype[local]:
  local_val_at cenv cx n j (BaseTV bt1) v /\
  val_footprint (BaseTV bt1) v <= type_memory_size (BaseTV bt1) /\
  val_footprint (BaseTV bt2) v = val_footprint (BaseTV bt1) v ==>
  local_val_at cenv cx n j (BaseTV bt2) v
Proof
  rw[local_val_at_def] >> metis_tac[]
QED

Theorem log_arg_rel_retype_base[local]:
  ~is_word_type (BaseT bt1) /\ ~is_word_type (BaseT bt2) /\
  evaluate_type (get_tenv cx) (BaseT bt1) = SOME (BaseTV bt1) /\
  (!tv. evaluate_type (get_tenv cx) (BaseT bt2) = SOME tv ==> tv = BaseTV bt2) /\
  (!a mem. val_in_memory (BaseTV bt2) v a mem =
           val_in_memory (BaseTV bt1) v a mem) /\
  val_footprint (BaseTV bt2) v = val_footprint (BaseTV bt1) v /\
  val_wf (BaseTV bt1) v /\ val_wf (BaseTV bt2) v /\
  val_footprint (BaseTV bt1) v <= type_memory_size (BaseTV bt1) /\
  val_footprint (BaseTV bt2) v <= type_memory_size (BaseTV bt2) /\
  log_arg_rel cenv cx sa sb es s (op,BaseT bt1) v ==>
  log_arg_rel cenv cx sa sb es s (op,BaseT bt2) v
Proof
  rw[log_arg_rel_def]
  >- (gvs[expr_val_rel_def] >> rw[] >> res_tac >> gvs[])
  >- suspend "val_at" >>
  suspend "clear"
QED

Resume log_arg_rel_retype_base[val_at]:
  simp[expr_val_at_def] >> rpt gen_tac >> strip_tac >>
  `tv = BaseTV bt2` by metis_tac[] >> gvs[] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE (srw_ss()) [expr_val_at_def]) >>
  disch_then (qspec_then `BaseTV bt1` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `w` >> fs[] >>
  metis_tac[local_val_at_retype]
QED

Resume log_arg_rel_retype_base[clear]:
  simp[log_arg_clear_def] >> rpt gen_tac >> strip_tac >>
  `tv = BaseTV bt2` by metis_tac[] >> gvs[] >>
  qpat_x_assum `log_arg_clear _ _ _ _`
    (mp_tac o SIMP_RULE (srw_ss()) [log_arg_clear_def]) >>
  metis_tac[local_val_at_retype]
QED

Finalise log_arg_rel_retype_base

Theorem log_arg_rel_compatible[local]:
  supported_scalar_type fty /\ event_arg_compatible fty aty /\
  evaluate_type (get_tenv cx) aty = SOME atv /\ value_has_type atv v /\
  (is_bytestring_type fty ==> ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv) /\
  log_arg_rel cenv cx sa sb es s (op,aty) v ==>
  log_arg_rel cenv cx sa sb es s (op,fty) v /\
  ?ftv. evaluate_type (get_tenv cx) fty = SOME ftv /\ value_has_type ftv v
Proof
  strip_tac >> drule (CONJUNCT1 event_arg_compatible_scalar_cases) >>
  strip_tac
  >- (gvs[] >> metis_tac[])
  >- (gvs[is_bytestring_type_def] >>
      imp_res_tac evaluate_bytestring_type >> gvs[] >>
      drule_then (qspec_then `StringT n` mp_tac) bytestring_retype_facts >>
      impl_tac >- simp[] >> strip_tac >> simp[] >>
      irule log_arg_rel_retype_base >> simp[is_word_type_def] >>
      qexists_tac `StringT m` >> simp[is_word_type_def])
  >- (gvs[is_bytestring_type_def] >>
      imp_res_tac evaluate_bytestring_type >> gvs[] >>
      drule_then (qspec_then `BytesT (Dynamic n)` mp_tac) bytestring_retype_facts >>
      impl_tac >- simp[] >> strip_tac >> simp[] >>
      irule log_arg_rel_retype_base >> simp[is_word_type_def] >>
      qexists_tac `BytesT (Dynamic m)` >> simp[is_word_type_def]) >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def]
QED

Theorem log_args_retype:
  !xs tys vs.
    LIST_REL (log_arg_rel cenv cx sa sb es s) xs vs /\
    LIST_REL event_arg_compatible tys (MAP SND xs) /\
    EVERY supported_scalar_type tys /\
    EVERY (\ty. is_bytestring_type ty ==>
                ?tv. evaluate_type (get_tenv cx) ty = SOME tv) tys /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) (MAP SND xs) vs ==>
    LIST_REL (log_arg_rel cenv cx sa sb es s) (ZIP (MAP FST xs, tys)) vs /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) tys vs
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `tys` >> Cases_on `vs` >>
  simp[] >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[] >>
  rename1 `log_arg_rel _ _ _ _ _ _ x v` >> PairCases_on `x` >> gvs[] >>
  drule_all log_arg_rel_compatible >> simp[]
QED

(* ===== Declared bytestring types evaluate ===== *)

Theorem bytestring_memory_bytes_evaluate[local]:
  is_bytestring_type ty /\ type_memory_bytes cenv ty < dimword (:256) ==>
  ?tv. evaluate_type tenv ty = SOME tv
Proof
  strip_tac >>
  `?n. ty = BaseT (StringT n) \/ ty = BaseT (BytesT (Dynamic n))` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def]) >>
  qspec_then `n` assume_tac word_size_capacity >>
  gvs[type_memory_bytes_def, evaluate_type_def, type_slot_size_def,
      vfmConstantsTheory.word_size_def]
QED

Theorem event_field_bytestrings_evaluate:
  !fields.
    SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) <
      dimword (:256) /\
    EVERY (\f. SND f ==> ?tv. evaluate_type tenv (SND (FST f)) = SOME tv) fields ==>
    EVERY (\ty. is_bytestring_type ty ==> ?tv. evaluate_type tenv ty = SOME tv)
      (MAP (SND o FST) fields)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp_tac (srw_ss()) [] >> strip_tac >>
  conj_tac
  >- (strip_tac >> Cases_on `h2` >> fs[log_non_indexed_types_def] >>
      irule bytestring_memory_bytes_evaluate >> simp[] >>
      qexists_tac `cenv` >> decide_tac) >>
  first_x_assum irule >> Cases_on `h2` >> fs[log_non_indexed_types_def] >>
  decide_tac
QED

(* ===== The Log statement's compile structure at the declared types ===== *)

(* log_compile_structure with the declared types tys compatible with the
   argument types; the eval view is at tys. *)
Theorem log_compile_structure_compat:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  LIST_REL event_arg_compatible tys (MAP expr_type args) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type tys /\
  ~exprs_can_mutate cenv args /\
  EVERY (\e. is_bytestring_type (lowered_value_type cenv e) <=>
             is_bytestring_type (expr_type e)) args /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?ys xs sm ops st. compile_log_eval_all cenv args sa = (ys,sm) /\
    xs = ZIP (MAP FST ys, tys) /\ log_eval_view cenv args sa xs sm /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = tys /\ LENGTH ys = LENGTH args /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (ys,sm)` >>
  `LENGTH ys = LENGTH args` by
    (mp_tac (Q.SPECL [`cenv`, `args`, `sa`] compile_log_eval_all_length) >> simp[]) >>
  `MAP SND ys = MAP (lowered_value_type cenv) args` by
    (mp_tac (Q.SPECL [`cenv`, `args`, `sa`]
       eventLoweringStructureTheory.compile_log_eval_all_types) >> simp[]) >>
  `LENGTH tys = LENGTH args` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  qabbrev_tac `xs = ZIP (MAP FST ys, tys)` >>
  `MAP SND xs = tys /\ LENGTH xs = LENGTH args` by simp[Abbr `xs`, MAP_ZIP] >>
  `log_eval_view cenv args sa xs sm` by suspend "view" >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops xs flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (ops,st)` >>
  `EVERY (supported_scalar_type o SND) xs` by
    gvs[EVERY_MAP, combinTheory.o_DEF] >>
  `LENGTH flags = LENGTH xs` by decide_tac >>
  `cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP SND xs,flags)` by simp[] >>
  drule_all log_success_suffix_code >> strip_tac >>
  `cs_extends sa sm` by (drule_all compile_log_eval_all_grows >> simp[]) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[]) >>
  map_every qexists_tac [`ys`, `xs`, `sm`, `ops`, `st`] >>
  simp[markerTheory.Abbrev_def] >> fs[markerTheory.Abbrev_def] >>
  metis_tac[fn_has_code_mid, cs_extends_refl]
QED

Resume log_compile_structure_compat[view]:
  simp[log_eval_view_def, LIST_REL_EL_EQN, Abbr `xs`, EL_ZIP, EL_MAP] >>
  rpt strip_tac >>
  `SND (EL n ys) = lowered_value_type cenv (EL n args)` by
    (qpat_x_assum `MAP SND ys = _` (mp_tac o Q.AP_TERM `EL n`) >>
     simp[EL_MAP]) >>
  `event_arg_compatible (EL n tys) (expr_type (EL n args)) /\
   supported_scalar_type (EL n tys) /\
   (is_bytestring_type (lowered_value_type cenv (EL n args)) <=>
    is_bytestring_type (expr_type (EL n args)))` by
    gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
  metis_tac[compatible_scalar_type]
QED

Finalise log_compile_structure_compat

(* ===== The evaluated arguments at the declared types ===== *)

Theorem intcall_log_args_retype:
  LIST_REL event_arg_compatible tys (MAP expr_type args) /\
  EVERY supported_scalar_type tys /\
  EVERY (\ty. is_bytestring_type ty ==>
              ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv) tys /\
  LENGTH ys = LENGTH args /\ xs = ZIP (MAP FST ys, tys) /\
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s)
    (\res ee u. ?vs. res = INL vs /\
      log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee
        (ZIP (MAP FST ys, MAP expr_type args)) vs u /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP expr_type args) vs /\
      EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\ (!lab. FST p <> Label lab))
        (ZIP (MAP FST ys, MAP expr_type args)))
    (\res ee r. expr_exit res r) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s)
    (\res ee u. ?vs. res = INL vs /\
      log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee xs vs u /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP SND xs) vs /\
      EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\ (!lab. FST p <> Label lab)) xs)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH args` by (imp_res_tac LIST_REL_LENGTH >> fs[]) >>
  irule gas_outcome_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> gvs[log_args_post_def] >>
  drule log_args_retype >> disch_then (qspec_then `tys` mp_tac) >>
  impl_tac >- simp[MAP_ZIP] >> strip_tac >>
  gvs[MAP_ZIP] >>
  gvs[EVERY_EL, EL_ZIP, EL_MAP] >> metis_tac[]
QED
