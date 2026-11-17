Theory dftPacketBlockAppendValidity
Ancestors
  dftPacketBlockAppendShape
  venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_block_append_validity:
  !plan_eval row_eval rooted_eval call_setup plan_ok levels_ok
    F C pre sf rows bb d z0 Z bb1 z1 paths incoming root_fn entry root_path root_depth B u0.
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK entry) plan) /\
  rooted_eval = (\F C levels entry.
    FOLDL (\(prior,r) (sf,plan,call).
      case r of
        OK ent =>
         (prior ++ FST (plan_eval F C sf.fn_name plan ent),
          case SND (plan_eval F C sf.fn_name plan ent) of
            OK caller => (case call of NONE => OK caller | SOME c => call_setup C c caller)
          | other => other)
      | other => (prior,other)) ([],OK entry) levels) /\
  plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan = GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        EVERY (\i. ~is_terminator i.inst_opcode) z)) /\
    (!r bb e z es s.
      r < LENGTH plan /\ EL r plan = (bb,e,z) /\
      plan_eval F C sf.fn_name (TAKE r plan) entry = (es,OK s) ==>
      lookup_block s.vs_current_bb sf.fn_blocks = SOME bb /\
      (0 < r ==> ~s.vs_halted))) /\
  levels_ok = (\F C levels paths incoming root_fn root_entry root_path root_depth.
    levels <> [] /\ LENGTH paths = LENGTH levels /\
    LENGTH incoming = LENGTH levels /\
    HD paths = root_path /\ HD incoming = root_depth /\
    FST (HD levels) = root_fn /\
    (!i sf plan call.
      i < LENGTH levels /\ EL i levels = (sf,plan,call) ==>
      plan <> [] /\
      (!prior ent.
        rooted_eval F C (TAKE i levels) root_entry = (prior,OK ent) ==>
        plan_ok F C sf (EL i incoming) plan ent) /\
      (if SUC i < LENGTH levels then
        ?c nm ops bb e z.
          call = SOME c /\ LAST plan = (bb,e,z) /\
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\ EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok F C (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)])
    paths incoming root_fn entry root_path root_depth /\
  Z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
  SUC d <= F /\ MEM bb1 sf.fn_blocks /\
  bb.bb_instructions <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  LENGTH z1 < LENGTH (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  z1 = TAKE (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
  (!ent. row_eval F C sf.fn_name (bb,d,Z) ent =
    (case SND (row_eval F C sf.fn_name (bb,d,z0) ent) of
       OK u => (FST (row_eval F C sf.fn_name (bb,d,z0) ent) ++ FST (B u), SND (B u))
     | r => (FST (row_eval F C sf.fn_name (bb,d,z0) ent),r))) /\
  (!ev u. rooted_eval F C (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) entry = (ev,OK u) ==>
    u = u0) /\
  (!ev v. B u0 = (ev,OK v) ==>
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\ ~v.vs_halted) ==>
  levels_ok F C
    (pre ++ [(sf,rows ++ [(bb,d,Z);(bb1,SUC d,z1)],NONE)])
    paths incoming root_fn entry root_path root_depth
Proof
  rpt gen_tac >> strip_tac >> rename1 `SUC d <= fuel` >>
  `!prior ent ev v.
    rooted_eval fuel C pre entry = (prior,OK ent) /\
    plan_eval fuel C sf.fn_name (rows ++ [(bb,d,Z)]) ent = (ev,OK v) ==>
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\ ~v.vs_halted` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `z1 = _` kall_tac >>
     qpat_x_assum `!ev u. rooted_eval _ _ _ _ = _ ==> _` (mk_asm "alignment") >>
     qpat_x_assum `!ev v. B u0 = _ ==> _` (mk_asm "body") >>
     qpat_x_assum `plan_eval fuel C sf.fn_name _ ent = (ev,OK v)` mp_tac >>
     qpat_assum `plan_eval = _` (fn th => simp[NoAsms,th,FOLDL_APPEND,FOLDL]) >>
     qmatch_goalsub_abbrev_tac `FOLDL rstep` >>
     Cases_on `FOLDL rstep ([],OK ent) rows` >>
     rename1 `FOLDL rstep ([],OK ent) rows = (events,result)` >>
     Cases_on `result` >>
     qpat_assum `Abbrev (rstep = _)`
       (fn th => simp[NoAsms,REWRITE_RULE [markerTheory.Abbrev_def] th]) >>
     rename1 `FOLDL rstep ([],OK ent) rows = (events,OK t)` >>
     Cases_on `row_eval fuel C sf.fn_name (bb,d,z0) t` >>
     rename1 `row_eval fuel C sf.fn_name (bb,d,z0) t = (e0,r0)` >>
     qpat_x_assum `!ent. row_eval _ _ _ _ _ = _` (qspec_then `t` mp_tac) >>
     Cases_on `r0` >>
     qpat_assum `row_eval fuel C sf.fn_name (bb,d,z0) t = _`
       (fn th => simp[NoAsms,th]) >>
     disch_then (fn th => simp[NoAsms,th]) >> strip_tac >>
     rename1 `row_eval fuel C sf.fn_name (bb,d,z0) t = (e0,OK u)` >>
     `plan_eval fuel C sf.fn_name rows ent = (events,OK t)` by
       (qpat_assum `plan_eval = _` (fn th => simp[NoAsms,th]) >>
        qpat_assum `Abbrev (rstep = _)`
          (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        first_assum ACCEPT_TAC) >>
     `plan_eval fuel C sf.fn_name (rows ++ [(bb,d,z0)]) ent = (events ++ e0,OK u)` by
       (qpat_assum `plan_eval = _` (fn th => simp[NoAsms,th,FOLDL_APPEND,FOLDL]) >>
        qpat_assum `Abbrev (rstep = _)`
          (fn th => rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
        simp[Abbr `rstep`]) >>
     `rooted_eval fuel C (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) entry =
        (prior ++ events ++ e0,OK u)` by
       (qpat_x_assum `rooted_eval fuel C pre entry = _` mp_tac >>
        qpat_assum `rooted_eval = _` (fn th => simp[NoAsms,th,FOLDL_APPEND,FOLDL]) >>
        disch_then SUBST1_TAC >> simp[]) >>
     asm "alignment" drule >> disch_then SUBST_ALL_TAC >>
     asm "body" irule >> qexists `FST (B u0)` >>
     Cases_on `B u0` >> gvs[]) >>
  qpat_x_assum `Z = _` SUBST_ALL_TAC >>
  drule_all dft_packet_block_levels_ok_append >> simp[]
QED
