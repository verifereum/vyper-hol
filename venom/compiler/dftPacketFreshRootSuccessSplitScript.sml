Theory dftPacketFreshRootSuccessSplit
Ancestors
  dftPacketRootedCompose venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_fresh_root_success_split:
  !R (P : string -> (basic_block # num # instruction list) list ->
       venom_state -> (string # num) list # exec_result)
    (S : instruction -> venom_state -> exec_result)
    pre sf plan ent c child_entry csf bb e z events v.
  R = (\levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
          (prior ++ FST (P sf.fn_name plan ent),
           case SND (P sf.fn_name plan ent) of
             OK caller => (case call of NONE => OK caller | SOME c => S c caller)
           | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  (!ev u. R (pre ++ [(sf,plan,NONE)]) ent = (ev,OK u) ==>
    S c u = OK (child_entry with vs_gas_readings := u.vs_gas_readings)) /\
  R (pre ++ [(sf,plan,SOME c);(csf,[(bb,e,z)],NONE)]) ent =
    (events,OK v) ==>
  ?ev u ec.
    R (pre ++ [(sf,plan,NONE)]) ent = (ev,OK u) /\
    P csf.fn_name [(bb,e,z)]
      (child_entry with vs_gas_readings := u.vs_gas_readings) = (ec,OK v) /\
    events = ev ++ ec
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `FOLDL fstep` >>
  gvs[FOLDL_APPEND,FOLDL] >>
  Cases_on `FOLDL fstep ([],OK ent) pre` >>
  rename1 `FOLDL fstep ([],OK ent) pre = (prior,result)` >>
  Cases_on `result` >> gvs[Abbr `fstep`] >>
  rename1 `P sf.fn_name plan caller_entry` >>
  Cases_on `P sf.fn_name plan caller_entry` >>
  rename1 `P sf.fn_name plan caller_entry = (caller_events,caller_result)` >>
  Cases_on `caller_result` >> gvs[] >>
  rename1 `P csf.fn_name [(bb,e,z)]
    (child_entry with vs_gas_readings := caller_post.vs_gas_readings)` >>
  Cases_on `P csf.fn_name [(bb,e,z)]
    (child_entry with vs_gas_readings := caller_post.vs_gas_readings)` >>
  gvs[AllCaseEqs()]
QED
