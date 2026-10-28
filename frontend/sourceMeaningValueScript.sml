Theory sourceMeaningValue
Ancestors
  sourceMeaningConst sourceConstValueAggregateLib sourceConstValueStructuredProps
  sourceConstValueStructured sourceConstValue vyperInterpreter vyperState
  vyperContext vyperAST vyperValue vyperValueOperation list option pair

(* Type-directed source-value denotation. No expressions, reification or
   evaluator occur here. Nominal struct values are deliberately excluded:
   the expression frontend's constant replacement uses an empty nominal map. *)
Theorem source_meaning_value_member_size:
  !ss s. MEM s ss ==>
    source_const_value_size s < list_size source_const_value_size ss + 1
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[] >> res_tac >> simp[]
QED

Definition source_meaning_value_def:
  source_meaning_value tenv ty (SCV_List ss) =
    (case ty of ArrayT et bd =>
      case evaluate_type tenv et of NONE => NONE | SOME tv =>
        OPTION_MAP (\vs. ArrayV (make_array_value tv bd vs))
          (OPT_MMAP (source_meaning_value tenv et) ss)
     | _ => NONE) /\
  source_meaning_value tenv ty (SCV_Tuple ss) =
    (case ty of TupleT ts =>
      if LENGTH ts = LENGTH ss then
        OPTION_MAP (\vs. ArrayV (TupleV vs))
          (OPT_MMAP (\(t,s). source_meaning_value tenv t s) (ZIP (ts,ss)))
      else NONE
     | _ => NONE) /\
  source_meaning_value tenv ty sv =
    OPTION_MAP evaluate_literal (source_const_value_literal sv)
Termination
  WF_REL_TAC `measure (\(tenv,ty,sv). source_const_value_size sv)` >>
  simp[] >> rpt strip_tac >>
  irule source_meaning_value_member_size >> gvs[MEM_ZIP, MEM_EL] >> metis_tac[]
End

Theorem source_meaning_value_many:
  !ss ts ps f.
    source_const_reify_many f ts ss = SOME ps /\
    (!t s p. f t s = SOME p ==>
      source_meaning_value tenv t s = SOME (SND p)) ==>
    OPT_MMAP (\(t,s). source_meaning_value tenv t s) (ZIP (ts,ss)) =
      SOME (MAP SND ps) /\ LENGTH ts = LENGTH ss
Proof
  Induct >> Cases_on `ts` >>
  simp[source_const_reify_many_def, OPT_MMAP_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_const_reify_many_def] >> res_tac >> gvs[]
QED

Theorem source_meaning_value_replicate:
  !ss. OPT_MMAP (\(t,s). source_meaning_value tenv t s)
    (ZIP (REPLICATE (LENGTH ss) et,ss)) =
    OPT_MMAP (source_meaning_value tenv et) ss
Proof
  Induct >> simp[OPT_MMAP_def]
QED

Theorem source_meaning_value_step:
  (!t s p. f t s = SOME p ==>
    source_meaning_value tenv t s = SOME (SND p)) /\
  source_const_reify_step f FEMPTY tenv ty sv = SOME p ==>
  source_meaning_value tenv ty sv = SOME (SND p)
Proof
  strip_tac >> Cases_on `sv` >>
  gvs[source_const_reify_step_def, source_const_value_literal_def, AllCaseEqs()] >>
  TRY (simp[source_meaning_value_def, source_const_value_literal_def] >> NO_TAC) >>
  drule_all source_meaning_value_many >> strip_tac >>
  gvs[source_meaning_value_def, source_meaning_value_replicate] >>
  qexists_tac `MAP SND ps` >> simp[] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem source_meaning_value_fuel:
  !n tenv ty sv p.
    source_const_reify_fuel n FEMPTY tenv ty sv = SOME p ==>
    source_meaning_value tenv ty sv = SOME (SND p)
Proof
  Induct >> simp[Once source_const_reify_fuel_def] >>
  rpt strip_tac >> irule source_meaning_value_step >>
  qexists_tac `source_const_reify_fuel n FEMPTY tenv` >> simp[]
QED

(* Successful reification establishes denotation; it does NOT define it. *)
Theorem source_meaning_value_reify:
  sourceConstValueStructured$source_const_reify FEMPTY tenv ty sv = SOME e ==>
  ?v. source_meaning_value tenv ty sv = SOME v /\
    (!cx st. get_tenv cx = tenv ==> eval_expr cx e st = (INL (Value v),st))
Proof
  simp[sourceConstValueStructuredTheory.source_const_reify_def, AllCaseEqs()] >>
  rpt strip_tac >> drule source_meaning_value_fuel >> strip_tac >>
  drule source_const_reify_fuel_certificate >>
  simp[source_const_reify_certificate_def] >> metis_tac[]
QED
