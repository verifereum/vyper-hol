Theory dftPacketBlockAppendShape
Ancestors
  dftPacketRootedOperational venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_block_plan_ok_append:
  !plan_eval row_eval plan_ok F C sf inc rows bb d z0 bb1 z1 ent.
  plan_eval = (\F C owner plan entry.
    FOLDL (\(es,r) row. case r of
      OK s => (es ++ FST (row_eval F C owner row s), SND (row_eval F C owner row s))
    | other => (es,other)) ([],OK entry) plan) /\
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
  plan_ok F C sf inc (rows ++ [(bb,d,z0)]) ent /\
  SUC d <= F /\ MEM bb1 sf.fn_blocks /\
  bb.bb_instructions <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  LENGTH z1 < LENGTH (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  z1 = TAKE (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
  (!ev v. plan_eval F C sf.fn_name
    (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)]) ent = (ev,OK v) ==>
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\ ~v.vs_halted) ==>
  plan_ok F C sf inc
    (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)]) ent
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `plan_ok = _` SUBST_ALL_TAC >> BETA_TAC >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `_ /\ _ /\ _ /\ _` strip_assume_tac >>
  simp[] >> rpt conj_tac
  >- (qpat_x_assum `MAP _ _ = _` mp_tac >>
      simp[GSYM arithmeticTheory.ADD1,GENLIST,SNOC_APPEND,APPEND_11] >>
      strip_tac >>
      `LENGTH rows + 2 = SUC (SUC (LENGTH rows))` by decide_tac >>
      simp[GENLIST,SNOC_APPEND,APPEND_ASSOC])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `r < LENGTH rows`
      >- (qpat_x_assum `!r bb e z. _ ==> _ <= _ /\ _`
            (qspecl_then [`r`,`bb'`,`e`,`z`] mp_tac) >>
          gvs[EL_APPEND_EQN]) >>
      Cases_on `r = LENGTH rows`
      >- (gvs[EL_APPEND_EQN] >>
          qpat_x_assum `!r bb e z. _ ==> _ <= _ /\ _`
            (qspecl_then [`LENGTH rows`,`bb`,`d`,`z0`] mp_tac) >>
          simp[EL_APPEND_EQN]) >>
      `r = SUC (LENGTH rows)` by decide_tac >>
      gvs[EL_APPEND_EQN]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `r <= LENGTH rows`
  >- (`TAKE r (rows ++ [(bb,d,z0)]) = TAKE r rows /\
       TAKE r (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)]) = TAKE r rows`
        by simp[TAKE_APPEND1] >>
      Cases_on `r < LENGTH rows`
      >- (gvs[EL_APPEND_EQN] >>
          qpat_x_assum `!r bb e z es s. _`
            (qspecl_then [`r`,`bb'`,`e`,`z`,`es`,`s`] mp_tac) >>
          simp[EL_APPEND_EQN,TAKE_APPEND1]) >>
      `r = LENGTH rows` by decide_tac >> gvs[EL_APPEND_EQN] >>
      qpat_x_assum `!r bb e z es s. _`
        (qspecl_then [`LENGTH rows`,`bb`,`d`,`z0`,`es`,`s`] mp_tac) >>
      simp[EL_APPEND_EQN,TAKE_APPEND1]) >>
  `r = SUC (LENGTH rows)` by decide_tac >>
  gvs[EL_APPEND_EQN,TAKE_APPEND,TAKE_LENGTH_TOO_LONG] >>
  first_x_assum drule >> simp[]
QED

Theorem dft_packet_block_levels_ok_append:
  !plan_eval row_eval rooted_eval call_setup plan_ok levels_ok
    F C pre sf rows bb d z0 bb1 z1 paths incoming root_fn entry root_path root_depth.
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
  SUC d <= F /\ MEM bb1 sf.fn_blocks /\
  bb.bb_instructions <> [] /\
  EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
  is_terminator (LAST bb.bb_instructions).inst_opcode /\
  ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
  LENGTH z1 < LENGTH (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  z1 = TAKE (LENGTH z1) (DROP (phi_prefix_length bb1.bb_instructions) bb1.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 /\
  (!prior ent ev v.
    rooted_eval F C pre entry = (prior,OK ent) /\
    plan_eval F C sf.fn_name
      (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)]) ent = (ev,OK v) ==>
    lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\ ~v.vs_halted) ==>
  levels_ok F C
    (pre ++ [(sf,rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)],NONE)])
    paths incoming root_fn entry root_path root_depth
Proof
  rpt gen_tac >> strip_tac >> rename1 `SUC d <= fuel` >>
  `!a ent prior.
    rooted_eval fuel C pre entry = (prior,OK ent) /\
    plan_ok fuel C sf a (rows ++ [(bb,d,z0)]) ent ==>
    plan_ok fuel C sf a
      (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)]) ent` by
    (rpt gen_tac >> strip_tac >>
     `!ev v. plan_eval fuel C sf.fn_name
       (rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)]) ent = (ev,OK v) ==>
       lookup_block v.vs_current_bb sf.fn_blocks = SOME bb1 /\ ~v.vs_halted`
       by metis_tac[] >>
     drule_all dft_packet_block_plan_ok_append >> simp[]) >>
  qpat_x_assum `plan_ok = _` kall_tac >>
  qpat_x_assum `plan_eval = _` kall_tac >>
  qpat_x_assum `rooted_eval = _` kall_tac >>
  gvs[] >> conj_tac
  >- (Cases_on `pre` >> simp[]) >>
  map_every qx_gen_tac [`i`,`sfi`,`plan`,`call`] >> strip_tac >>
  `i <= LENGTH pre` by decide_tac >>
  `TAKE i (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)]) = TAKE i pre /\
   TAKE i (pre ++ [(sf,rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)],NONE)]) = TAKE i pre`
    by simp[TAKE_APPEND1] >>
  `!k. k <= LENGTH pre ==>
    FST (EL k (pre ++ [(sf,rows ++ [(bb,d,z0)],NONE)])) =
    FST (EL k (pre ++ [(sf,rows ++ [(bb,d,DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions);(bb1,SUC d,z1)],NONE)]))` by
    (rpt strip_tac >> Cases_on `k < LENGTH pre` >> simp[EL_APPEND_EQN] >>
     `k = LENGTH pre` by decide_tac >> simp[]) >>
  Cases_on `i < LENGTH pre`
  >- (qpat_x_assum `!i sf plan call. _`
        (qspecl_then [`i`,`sfi`,`plan`,`call`] mp_tac) >>
      gvs[EL_APPEND_EQN,TAKE_APPEND1]) >>
  `i = LENGTH pre` by decide_tac >> gvs[EL_APPEND_EQN] >>
  qpat_x_assum `!i sf plan call. _`
    (qspecl_then [`LENGTH pre`,`sf`,`rows ++ [(bb,d,z0)]`,`NONE`] mp_tac) >>
  simp[EL_APPEND_EQN,TAKE_APPEND1] >> metis_tac[]
QED
