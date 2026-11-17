Theory dftPacketFreshCutGeometry
Ancestors
  dftPacketNumericCutExtension list rich_list arithmetic

Theorem dft_packet_call_fresh_cut_geometry:
  !(F:num) C rooted_eval plan_ok levels_ok pre sf plan incoming root_fn entry
    bb0 d z0 c nm ops csf cb z p cuts b cuts' levels' q.
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
  MAP (\(ai,ds,ei,qi,zi). ai)
    (cuts : ((num # num) list # num list # num # num # instruction list) list) =
      REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
  LENGTH cuts = LENGTH (pre ++ [(sf,plan,NONE)]) /\
  levels_ok F C (pre ++ [(sf,plan,NONE)])
    (MAP (\(ai,ds,ei,qi,zi). ai) cuts) incoming root_fn entry [] 0 /\
  LAST plan = (bb0,d,z0) /\
  c = EL (LENGTH z0) (DROP (phi_prefix_length bb0.bb_instructions)
    bb0.bb_instructions) /\
  c.inst_opcode = INVOKE /\ decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME csf /\
  (!prior ent.
    rooted_eval F C (pre ++ [(sf,plan,SOME c)]) entry = (prior,OK ent) ==>
    plan_ok F C csf d [(cb,SUC d,z)] ent) /\
  b = (d,c.inst_id)::p /\
  cuts' = cuts ++ [(b,[],SUC d,q,z)] /\
  levels' = pre ++ [(sf,plan,SOME c);(csf,[(cb,SUC d,z)],NONE)] ==>
  MAP (\(ai,ds,ei,qi,zi). ai) cuts' =
    REVERSE (GENLIST (\i. DROP i b) (SUC (LENGTH b))) /\
  LENGTH cuts' = LENGTH levels' /\
  levels_ok F C levels' (MAP (\(ai,ds,ei,qi,zi). ai) cuts')
    (incoming ++ [d]) root_fn entry [] 0
Proof
  rpt gen_tac >> strip_tac >>
  `GENLIST (\i. DROP i b) (SUC (LENGTH b)) =
    b :: GENLIST (\i. DROP i p) (SUC (LENGTH p))` by
    simp[Once listTheory.GENLIST_CONS,combinTheory.o_DEF] >>
  `LAST (MAP (\(ai,ds,ei,qi,zi). ai) cuts) = p` by
    simp[Once listTheory.GENLIST_CONS] >>
  conj_tac >- simp[] >>
  conj_tac >- gvs[] >>
  qpat_x_assum `levels' = _` SUBST_ALL_TAC >>
  qpat_x_assum `cuts' = _` SUBST_ALL_TAC >>
  qpat_x_assum `b = _` SUBST_ALL_TAC >>
  simp[NoAsms,MAP_APPEND] >>
  irule dft_packet_levels_call_extend_num >>
  conj_tac
  >- (qexistsl_tac [`plan_ok`,`rooted_eval`] >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  conj_tac
  >- (qexistsl_tac [`nm`,`ops`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`bb0`,`z0`] >> asm_rewrite_tac[]
QED
