Theory dftPacketNumericCutExtension
Ancestors
  dftPacketCutExtension rich_list arithmetic

Theorem dft_packet_levels_call_extend_num:
  !(F:num) C rooted_eval plan_ok levels_ok pre sf plan
    (paths:(num # num) list list) (incoming:num list) root_fn entry
    a bb0 (e0:num) z0 c nm ops csf bb (e:num) (z:instruction list).
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
  levels_ok F C (pre ++ [(sf,plan,NONE)]) paths incoming root_fn entry [] 0 /\
  LAST paths = a /\ LAST plan = (bb0,e0,z0) /\
  c = EL (LENGTH z0) (DROP (phi_prefix_length bb0.bb_instructions)
    bb0.bb_instructions) /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME csf /\
  (!prior ent.
    rooted_eval F C (pre ++ [(sf,plan,SOME c)]) entry = (prior,OK ent) ==>
    plan_ok F C csf e0 [(bb,e,z)] ent) ==>
  levels_ok F C (pre ++ [(sf,plan,SOME c);(csf,[(bb,e,z)],NONE)])
    (paths ++ [(e0,c.inst_id)::a]) (incoming ++ [e0]) root_fn entry [] 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `levels_ok = _` SUBST_ALL_TAC >>
  gvs[] >>
  rpt conj_tac
  >- (Cases_on `paths` >> gvs[])
  >- (Cases_on `incoming` >> gvs[])
  >- (Cases_on `pre` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i < LENGTH pre`
  >- (qpat_x_assum `EL i (pre ++ _) = _` mp_tac >>
      simp[EL_APPEND] >> strip_tac >>
      qpat_x_assum `!i sf' plan' call. _`
        (qspecl_then [`i`,`sf'`,`plan'`,`call`] mp_tac) >>
      `i <= LENGTH pre /\ SUC i <= LENGTH pre` by decide_tac >>
      simp[TAKE_APPEND1,EL_APPEND] >>
      Cases_on `SUC i < LENGTH pre`
      >- (simp[] >> metis_tac[]) >>
      `SUC i = LENGTH pre` by decide_tac >> simp[] >> metis_tac[]) >>
  Cases_on `i = LENGTH pre`
  >- (gvs[EL_APPEND] >>
      qpat_x_assum `!i sf' plan' call. _`
        (qspecl_then [`LENGTH pre`,`sf`,`plan`,`NONE`] mp_tac) >>
      simp[EL_APPEND,TAKE_APPEND1] >> strip_tac >>
      `paths <> []` by (Cases_on `paths` >> gvs[]) >>
      simp[GSYM arithmeticTheory.ADD1,listTheory.LAST_EL]) >>
  `i = LENGTH pre + 1` by decide_tac >>
  gvs[EL_APPEND,arithmeticTheory.ADD1,TAKE_APPEND] >>
  simp[listTheory.TAKE_LENGTH_TOO_LONG]
QED
