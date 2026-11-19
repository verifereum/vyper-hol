Theory dftPacketRootedCompose
Ancestors
  venomExecSemantics venomInst venomState list rich_list

Theorem fold_event_prefix[local]:
  !step.
    (!es r level.
      step (es,r) level =
        (es ++ FST (step ([],r) level), SND (step ([],r) level))) ==>
    !levels es r.
      FOLDL step (es,r) levels =
        (es ++ FST (FOLDL step ([],r) levels),
         SND (FOLDL step ([],r) levels))
Proof
  qx_gen_tac `f` >> strip_tac >> Induct
  >- simp[] >>
  rpt gen_tac >> pure_rewrite_tac[FOLDL] >>
  first_x_assum (qspecl_then [`es`,`r`,`h`] SUBST1_TAC) >>
  Cases_on `f ([],r) h` >>
  rename1 `f ([],r) h = (events,result)` >>
  first_assum (qspecl_then [`es ++ events`,`result`] mp_tac) >>
  first_x_assum (qspecl_then [`events`,`result`] mp_tac) >>
  simp[APPEND_ASSOC]
QED

Theorem fold_stopped[local]:
  !step r.
    (!es level. step (es,r) level = (es,r)) ==>
    !levels es. FOLDL step (es,r) levels = (es,r)
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[]
QED

Theorem dft_packet_rooted_call_append:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    pre sf plan entry es u c cs more.
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  R (pre ++ [(sf,plan,NONE)]) entry = (es,OK u) /\
  S c u = OK cs ==>
  R (pre ++ [(sf,plan,SOME c)] ++ more) entry =
    (es ++ FST (R more cs), SND (R more cs))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL fstep` >>
  `FOLDL fstep (es,OK cs) more =
    (es ++ FST (FOLDL fstep ([],OK cs) more),
     SND (FOLDL fstep ([],OK cs) more))` by
    (irule fold_event_prefix >>
     rpt gen_tac >> PairCases_on `level` >> Cases_on `r` >>
     simp[Abbr `fstep`]) >>
  `FOLDL fstep ([],OK entry) (pre ++ [(sf,plan,SOME c)]) =
    (es,OK cs)` suffices_by simp[FOLDL_APPEND] >>
  gvs[FOLDL_APPEND,FOLDL] >>
  Cases_on `FOLDL fstep ([],OK entry) pre` >>
  rename1 `FOLDL fstep ([],OK entry) pre = (prior,result)` >>
  Cases_on `result` >> gvs[Abbr `fstep`] >>
  Cases_on `P sf.fn_name plan v` >>
  rename1 `P sf.fn_name plan v = (events,last_result)` >>
  Cases_on `last_result` >> gvs[]
QED

Theorem dft_packet_rooted_call_stopped:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    pre sf plan entry es r c more.
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  R (pre ++ [(sf,plan,NONE)]) entry = (es,r) /\
  (~?u. r = OK u) ==>
  R (pre ++ [(sf,plan,SOME c)] ++ more) entry = (es,r)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL fstep` >>
  `FOLDL fstep (es,r) more = (es,r)` by
    (irule fold_stopped >>
     rpt gen_tac >> PairCases_on `level` >> Cases_on `r` >>
     gvs[Abbr `fstep`]) >>
  `FOLDL fstep ([],OK entry) (pre ++ [(sf,plan,SOME c)]) =
    (es,r)` suffices_by simp[FOLDL_APPEND] >>
  gvs[FOLDL_APPEND,FOLDL] >>
  Cases_on `FOLDL fstep ([],OK entry) pre` >>
  rename1 `FOLDL fstep ([],OK entry) pre = (prior,result)` >>
  Cases_on `result` >> gvs[Abbr `fstep`] >>
  Cases_on `P sf.fn_name plan v` >>
  rename1 `P sf.fn_name plan v = (events,last_result)` >>
  Cases_on `last_result` >> gvs[]
QED
