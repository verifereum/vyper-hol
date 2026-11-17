Theory dftPacketChangedCallerSuccess
Ancestors
  venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_changed_caller_success:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    pre sf plan c entry events cs.
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  R (pre ++ [(sf,plan,SOME c)]) entry = (events,OK cs) ==>
  ?u. R (pre ++ [(sf,plan,NONE)]) entry = (events,OK u) /\
      S c u = OK cs
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `FOLDL fstep` >>
  gvs[FOLDL_APPEND,FOLDL] >>
  Cases_on `FOLDL fstep ([],OK entry) pre` >>
  rename1 `FOLDL fstep ([],OK entry) pre = (prior,result)` >>
  Cases_on `result` >> gvs[Abbr `fstep`] >>
  Cases_on `P sf.fn_name plan v` >>
  rename1 `P sf.fn_name plan v = (es,last_result)` >>
  Cases_on `last_result` >> gvs[]
QED
