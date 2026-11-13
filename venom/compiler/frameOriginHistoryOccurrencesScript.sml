Theory frameOriginHistoryOccurrences
Ancestors
  frameOriginHistory list rich_list

Theorem origin_observations_split:
  !h xs di ds ys.
    origin_observations h = xs ++ [(di,ds)] ++ ys ==>
    ?pre fn PG G om rest.
      h = pre ++ OriginObserve (OriginSnapshot fn PG G om di ds)::rest /\
      origin_observations pre = xs /\ origin_observations rest = ys
Proof
  Induct_on `h` >- simp[origin_observations_def] >>
  qx_gen_tac `ev` >> rename1 `origin_observations (ev::tail)` >>
  Cases_on `ev` >> simp[origin_observations_def] >> rpt gen_tac
  >- (Cases_on `o'` >> simp[origin_observations_def] >> Cases_on `xs` >>
      simp[] >> strip_tac
      >- (qexists `[]` >> simp[origin_observations_def] >> metis_tac[])
      >> first_x_assum drule >> strip_tac >>
      qexists `OriginObserve (OriginSnapshot i l f f0 i0 v)::pre` >>
      simp[origin_observations_def] >> metis_tac[])
  >> strip_tac >> first_x_assum drule >> strip_tac >>
  qmatch_goalsub_abbrev_tac `ev::tail` >>
  qexists `ev::pre` >> simp[origin_observations_def, Abbr `ev`] >> metis_tac[]
QED

Theorem front_member_split[local]:
  !l x. MEM x (FRONT l) ==>
    ?pre rest. l = pre ++ x::rest /\ rest <> []
Proof
  Induct >- simp[] >> qx_gen_tac `head` >> Cases_on `l` >> simp[] >> rpt strip_tac
  >- (qexists `[]` >> simp[])
  >> first_x_assum drule >> strip_tac >> qexists `head::pre` >> simp[] >>
  metis_tac[]
QED

Theorem origin_observations_completion:
  origin_log ctx h /\ MEM (di,ds) (FRONT (origin_observations h)) ==>
    ?pre fn PG G om e b suffix.
      h = pre ++ OriginObserve (OriginSnapshot fn PG G om di ds)::
        e::OriginObserve b::suffix /\
      origin_edge ctx (OriginSnapshot fn PG G om di ds) e b
Proof
  rpt strip_tac >> drule front_member_split >> strip_tac >> gvs[] >>
  drule origin_observations_split >> strip_tac >>
  `rest' <> []` by (strip_tac >> gvs[origin_observations_def]) >>
  drule_all origin_log_completion >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem joint_origin_history_current_completion:
  joint_origin_history vs0 ctx stk PG0 G0 tn fn0 inst s oms om0 hs h /\
  MEM (di,ds) (FRONT (origin_observations h)) ==>
    ?pre fn PG G om e b suffix.
      h = pre ++ OriginObserve (OriginSnapshot fn PG G om di ds)::
        e::OriginObserve b::suffix /\
      origin_edge ctx (OriginSnapshot fn PG G om di ds) e b
Proof
  rpt strip_tac >> irule origin_observations_completion >>
  simp[] >> metis_tac[joint_origin_history_current_log]
QED

Theorem joint_origin_history_saved_completion:
  joint_origin_history vs0 ctx stk PG0 G0 tn fn0 inst s oms om0 hs h /\
  n < LENGTH stk /\ MEM (di,ds) (FRONT (origin_observations (EL n hs))) ==>
    ?pre fn PG G om e b suffix.
      EL n hs = pre ++ OriginObserve (OriginSnapshot fn PG G om di ds)::
        e::OriginObserve b::suffix /\
      origin_edge ctx (OriginSnapshot fn PG G om di ds) e b
Proof
  rpt strip_tac >> irule origin_observations_completion >>
  simp[] >> metis_tac[joint_origin_history_saved_log]
QED
