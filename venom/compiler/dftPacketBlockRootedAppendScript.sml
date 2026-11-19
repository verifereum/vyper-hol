Theory dftPacketBlockRootedAppend
Ancestors
  dftPacketSameLevelCompose dftPacketClosedRows
  venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_block_plan_append:
  !(R : 'row -> venom_state -> (string # num) list # exec_result)
    plan_eval ds entry E t full Ec u partial.
  plan_eval = (\plan ent.
    FOLDL (\(es,r) row. case r of
      OK v => (es ++ FST (R row v),SND (R row v))
    | other => (es,other)) ([],OK ent) plan) /\
  plan_eval ds entry = (E,OK t) /\ R full t = (Ec,OK u) ==>
  plan_eval (ds ++ [full;partial]) entry =
    (E ++ Ec ++ FST (R partial u),SND (R partial u))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[FOLDL_APPEND,FOLDL,APPEND_ASSOC]
QED

Theorem dft_packet_block_plan_append_stopped:
  !(R : 'row -> venom_state -> (string # num) list # exec_result)
    plan_eval ds entry E r more.
  plan_eval = (\plan ent.
    FOLDL (\(es,r) row. case r of
      OK v => (es ++ FST (R row v),SND (R row v))
    | other => (es,other)) ([],OK ent) plan) /\
  plan_eval ds entry = (E,r) /\ (!u. r <> OK u) ==>
  plan_eval (ds ++ more) entry = (E,r)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> simp[FOLDL_APPEND] >>
  Induct_on `more` >> simp[] >> Cases_on `r` >> gvs[]
QED
