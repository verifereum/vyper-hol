Theory dftPacketLastRowValidity
Ancestors
  venomExecSemantics venomInst venomState list rich_list

Theorem dft_packet_levels_last_row_replace:
  !F. plan_ok = (\F C sf a plan entry.
    plan <> [] /\
    MAP (\(bb,e,z). e) plan =
      GENLIST (\r. a + SUC r) (LENGTH plan) /\
    (!r bb e z. r < LENGTH plan /\ EL r plan = (bb,e,z) ==>
      e <= F /\ MEM bb sf.fn_blocks /\
      (if SUC r < LENGTH plan then
        bb.bb_instructions <> [] /\
        EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions) /\
        is_terminator (LAST bb.bb_instructions).inst_opcode /\
        ~MEM (LAST bb.bb_instructions).inst_opcode [RET;RETFMP;DRET] /\
        z = DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions
       else
        LENGTH z < LENGTH (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
        z = TAKE (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
          bb.bb_instructions) /\
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
          c = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
            bb.bb_instructions) /\
          c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
          lookup_function nm C.ctx_functions = SOME (FST (EL (SUC i) levels)) /\
          EL (SUC i) incoming = e /\
          EL (SUC i) paths = (e,c.inst_id)::EL i paths
       else call = NONE))) /\
  levels_ok F C (pre ++ [(sf,rows ++ [(bb,e,z0)],NONE)])
    paths incoming root_fn entry root_path root_depth /\
  LENGTH z1 < LENGTH (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  z1 = TAKE (LENGTH z1)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode) z1 ==>
  levels_ok F C (pre ++ [(sf,rows ++ [(bb,e,z1)],NONE)])
    paths incoming root_fn entry root_path root_depth
Proof
  qx_gen_tac `fuel` >> strip_tac >>
  `!a ent. plan_ok fuel C sf a (rows ++ [(bb,e,z0)]) ent ==>
     plan_ok fuel C sf a (rows ++ [(bb,e,z1)]) ent` by
    (qpat_x_assum `levels_ok = _` kall_tac >>
     qpat_x_assum `levels_ok _ _ _ _ _ _ _ _ _` kall_tac >>
     rpt gen_tac >> qpat_x_assum `plan_ok = _` (fn th => rewrite_tac[th]) >>
     simp[] >> strip_tac >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         Cases_on `r < LENGTH rows`
         >- (fs[EL_APPEND_EQN] >> qpat_x_assum `!r b n z. _ ==> _` (qspecl_then [`r`,`bb'`,`e'`,`z`] mp_tac) >>
             simp[EL_APPEND_EQN]) >>
         `r = LENGTH rows` by decide_tac >> gvs[EL_APPEND_EQN] >>
         qpat_x_assum `!r b n z. _ ==> _` (qspecl_then [`LENGTH rows`,`bb`,`e`,`z0`] mp_tac) >>
         simp[EL_APPEND_EQN]) >>
     rpt gen_tac >> strip_tac >>
     `r <= LENGTH rows` by decide_tac >>
     `TAKE r (rows ++ [(bb,e,z1)]) = TAKE r rows /\
      TAKE r (rows ++ [(bb,e,z0)]) = TAKE r rows` by simp[TAKE_APPEND1] >>
     Cases_on `r < LENGTH rows` >> gvs[EL_APPEND_EQN] >> metis_tac[]) >>
  qpat_x_assum `plan_ok = _` kall_tac >>
  gvs[] >> FAIL_TAC "levels"
QED
