(* Entry ghost identities for the checked Bool decoder loop. *)
Theory ctorDeployMemoryRunPtrPrefixBoolLoop
Ancestors
  ctorDeployMemoryRunPtrPrefixBoolHeader
  ctorDeployMemoryRunPtrPrefixBoolBody
  ctorDeployMemoryRunPtrPrefixBoolShape
  ctorDeployMemoryRunPtrPrefixBlocks
  ptrDiscipline ptrSafeRun venomState venomExecSemantics venomInst abiDecoderExecution abiDecoderContract list

Theorem prefix_no_phi_entry:
  !s fn bb G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (bb.bb_instructions = [] \/
     ?inst rest. bb.bb_instructions = inst::rest /\ inst.inst_opcode <> PHI) ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn /\
    eval_phis s bb.bb_instructions = OK s /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt strip_tac >>
  gvs[entry_prov_def, phis_prov_def, entry_taint_vars_def,
      phis_taint_def, eval_phis_def, phi_prefix_length_def]
QED

Theorem prefix_bool_mload_entry:
  !s fn bb iid ops outs rest G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = mk_inst iid MLOAD ops outs :: rest ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn /\
    eval_phis s bb.bb_instructions = OK s /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >> irule prefix_no_phi_entry >>
  simp[mk_inst_def]
QED

Theorem prefix_bool_header_entry:
  !s fn bb hid ip src hiv cv cmp done body_lbl exit_lbl G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions =
      abi_decode_header_insts hid (Var ip) (Var src) DLOAD
        hiv cv cmp done body_lbl exit_lbl ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn /\
    eval_phis s bb.bb_instructions = OK s /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >> irule prefix_no_phi_entry >>
  simp[abi_decode_header_insts_def, mk_inst_def]
QED

(* The body's checked indexed trace is also an actual basic-block edge.
   No semantic instruction is re-executed in this adapter. *)
Theorem prefix_bool_body_exec_block:
  let I =
    [mk_inst iid MLOAD [Var ip] [iv];
     mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
     mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
     mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
     mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
     mk_inst (iid+6) ADD [Var dp0;Var idst] [dp];
     mk_inst (iid+7) DLOAD [Var sp] [x];
     mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
     mk_inst (iid+9) ISZERO [Var y] [z];
     mk_inst (iid+10) ASSERT [Var z] [];
     mk_inst (iid+11) MSTORE [Var dp;Var x] [];
     mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
     mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
     mk_inst (iid+14) JMP [Label hdr] []]
  in
    bb.bb_instructions = I /\ ~t.vs_halted /\
    (!j. j <= 14 ==> (V j).vs_inst_idx = j) /\
    (!j f. j < 14 ==> step_inst f ctx (EL j I) (V j) =
      OK ((V (SUC j)) with vs_inst_idx := j)) /\
    (!f. step_inst f ctx (EL 14 I) (V 14) = OK t) ==>
    !f. exec_block f ctx bb (V 0) = OK t
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `bb.bb_instructions = insns` >>
  strip_tac >> gen_tac >>
  `LENGTH insns = 15 /\
   (!j. j < 14 ==> ~is_terminator (EL j insns).inst_opcode) /\
   is_terminator (EL 14 insns).inst_opcode` by
    (simp[Abbr `insns`, mk_inst_def, is_terminator_def] >>
     rpt strip_tac >>
     `j=0 \/ j=1 \/ j=2 \/ j=3 \/ j=4 \/ j=5 \/ j=6 \/
      j=7 \/ j=8 \/ j=9 \/ j=10 \/ j=11 \/ j=12 \/ j=13` by decide_tac >>
     gvs[EL, mk_inst_def, is_terminator_def]) >>
  `!n. n <= 14 ==> exec_block f ctx bb (V (14-n)) = OK t` suffices_by
    (disch_then (qspec_then `14` mp_tac) >> simp[]) >>
  Induct >-
    (simp[Once exec_block_def, get_instruction_def] >>
     simp[]) >>
  strip_tac >>
  `14-SUC n < 14 /\ SUC (14-SUC n) = 14-n /\ n <= 14 /\ 14-n <= 14`
    by decide_tac >>
  `V (14-n) with vs_inst_idx := 14-n = V (14-n)` by
    (simp[fetch "venomState" "venom_state_component_equality"]) >>
  simp[Once exec_block_def, get_instruction_def]
QED

(* Existential form of the closed header boundary: consumers do not name
   the four intermediate machine states or the four ghost updates. *)
Theorem prefix_bool_header_endpoint:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  s.vs_current_bb = hdr /\
  ALL_DISTINCT [ip;src;dst;iv;cv;cmp;done] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  mload scratch s = n2w i /\
  abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
  i <= ncount /\ ncount < dimword(:256) /\
  FLOOKUP G ip = SOME (scratch,32) /\
  scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  allocas_from lo s /\ lo <= scratch /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var src) = {} /\
  (!k. k < 32 ==> scratch+k NOTIN tn.t_mem) /\
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr;
      bb_instructions := abi_decode_header_insts hid (Var ip) (Var src)
        DLOAD iv cv cmp done body_lbl exit_lbl|> ==>
  ?t Gt tt.
    (!f. exec_block f ctx
      <|bb_label := hdr;
        bb_instructions := abi_decode_header_insts hid (Var ip) (Var src)
          DLOAD iv cv cmp done body_lbl exit_lbl|> s = OK t) /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if i < ncount then body_lbl else exit_lbl) /\
    ((!f. ptr_safe_blocks D lo f ctx fn PG
       (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
       !f. ptr_safe_blocks D lo f ctx fn PG G tn s) /\
    t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\
    tt.t_mem = tn.t_mem /\ tt.t_stor = tn.t_stor /\
    tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
    (!v. MEM v [ip;src;dst] ==>
      eval_operand (Var v) t = eval_operand (Var v) s /\
      FLOOKUP Gt v = FLOOKUP G v /\ op_taint tt (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  mp_tac (Q.INST [`id` |-> `hid`]
    (SRULE [LET_THM] prefix_bool_header_closed)) >>
  (impl_tac >- gvs[ALL_DISTINCT]) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `exec_block _ _ _ _ = OK t` >>
  qmatch_asmsub_abbrev_tac `entry_prov fn t gh` >>
  qmatch_asmsub_abbrev_tac `th.t_mem = tn.t_mem` >>
  qexistsl [`t`,`gh`,`th`] >>
  rpt conj_tac
  >- simp[]
  >- simp[Abbr `t`, jump_to_def, update_var_def]
  >- simp[Abbr `t`, jump_to_def]
  >- simp[Abbr `t`, jump_to_def]
  >- (strip_tac >> Cases >> simp[ptr_safe_blocks_def])
  >- simp[]
  >- simp[]
  >- simp[]
  >- simp[]
  >- (qpat_x_assum `allocas_from lo s` mp_tac >>
      simp[Abbr `t`, jump_to_def, update_var_def, allocas_from_def])
  >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem prefix_bool_body_endpoint:
  let insns =
    [mk_inst iid MLOAD [Var ip] [iv];
     mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
     mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
     mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
     mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
     mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
     mk_inst (iid+6) ADD [Var dp0;Var idst] [dp];
     mk_inst (iid+7) DLOAD [Var sp] [x];
     mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
     mk_inst (iid+9) ISZERO [Var y] [z];
     mk_inst (iid+10) ASSERT [Var z] [];
     mk_inst (iid+11) MSTORE [Var dp;Var x] [];
     mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
     mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
     mk_inst (iid+14) JMP [Label hdr] []];
      bb = <|bb_label := body_lbl; bb_instructions := insns|>;
      w = abi_decode_load DLOAD (n2w (a+32+32*i):bytes32) s
  in
  ALL_DISTINCT [ip;src;dst;iv;sp0;isrc;sp;dp0;idst;dp;x;y;z;inc] /\
  eval_operand (Var ip) s = SOME (n2w scratch) /\
  eval_operand (Var src) s = SOME (n2w a) /\
  eval_operand (Var dst) s = SOME (n2w d) /\
  FLOOKUP G ip = SOME (scratch,32) /\ FLOOKUP G src = NONE /\
  FLOOKUP G dst = SOME (b,sz) /\
  op_taint tn (Var ip) = {} /\ op_taint tn (Var src) = {} /\
  op_taint tn (Var dst) = {} /\ i < ncount /\ ncount < dimword(:256) /\
  a+32*(ncount+1) < dimword(:256) /\
  b <= d /\ d+32*(ncount+1) <= b+sz /\ b+sz <= s.vs_alloca_next /\
  scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
  (d+32*(ncount+1) <= scratch \/ scratch+32 <= d) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  mload scratch s = n2w i /\ mload d s = n2w ncount /\
  (!j. j<i ==> mload (d+32+32*j) s = value j) /\
  (!r. r<32 ==> scratch+r NOTIN tn.t_mem) /\
  (!r. r<32*(i+1) ==> d+r NOTIN tn.t_mem) /\
  s.vs_inst_idx = 0 /\ s.vs_current_bb = body_lbl /\
  lookup_block body_lbl fn.fn_blocks = SOME bb ==>
  if w2n w < 2 then
    ?t Gt tt.
      (!f. exec_block f ctx bb s = OK t) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
      mload d t = n2w ncount /\ mload scratch t = n2w (SUC i) /\
      (!j. j<SUC i ==> mload (d+32+32*j) t = if j=i then w else value j) /\
      (!r. r<32 ==> scratch+r NOTIN tt.t_mem) /\
      (!r. r<32*(SUC i+1) ==> d+r NOTIN tt.t_mem) /\
      (!v. MEM v [ip;src;dst] ==>
        eval_operand (Var v) t = eval_operand (Var v) s /\
        FLOOKUP Gt v = FLOOKUP G v /\ op_taint tt (Var v) = op_taint tn (Var v)) /\
      t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
      t.vs_alloca_next = s.vs_alloca_next /\ allocas_from lo t /\
      tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
        (p+len<=scratch \/ scratch+32<=p) ==>
        mem_bytes_at p len t.vs_memory = mem_bytes_at p len s.vs_memory) /\
      ((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
        !f. ptr_safe_blocks D lo f ctx fn PG G tn s)
  else
    (?vh. run_inst_seq insns s = Abort Revert_abort vh) /\
    (!f. ptr_safe_blocks D lo f ctx fn PG G tn s)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `lookup_block body_lbl fn.fn_blocks = SOME bb` >>
  qmatch_goalsub_abbrev_tac `run_inst_seq insns s` >>
  qmatch_goalsub_abbrev_tac `w2n w < 2` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (PURE_REWRITE_RULE [LET_THM] prefix_bool_body_paired) >>
  (impl_tac >- simp[]) >> BETA_TAC >>
  pure_rewrite_tac[APPEND] >>
  qmatch_goalsub_abbrev_tac `run_inst_seq body_insts s =
    if w2n _ < 2 then OK jstate else Abort Revert_abort astate` >>
  `body_insts = insns` by simp[Abbr `body_insts`, Abbr `insns`] >>
  qpat_x_assum `body_insts = insns` SUBST_ALL_TAC >>
  qmatch_goalsub_abbrev_tac `LENGTH _ = nn+1` >>
  qmatch_goalsub_abbrev_tac `step_inst _ _ _ (vv _)` >>
  qmatch_goalsub_abbrev_tac `OK ((EL (_+1) uu) with vs_inst_idx := _)` >>
  strip_tac >>
  `vv 0 = s` by simp[Abbr `vv`, Abbr `uu`, EL] >>
  `!j. j <= 14 ==> (vv j).vs_inst_idx = j` by simp[Abbr `vv`] >>
  `!j. vv (SUC j) with vs_inst_idx := j =
        (EL (j+1) uu) with vs_inst_idx := j` by
    simp[Abbr `vv`, arithmeticTheory.ADD1] >>
  `eval_phis s bb.bb_instructions = OK s /\
   phi_prefix_length bb.bb_instructions = 0` by
    simp[Abbr `bb`, Abbr `insns`, eval_phis_def,
         phi_prefix_length_def, mk_inst_def] >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  qpat_x_assum `_ <= scratch \/ scratch+32 <= d` kall_tac >>
  qpat_x_assum `Abbrev (jstate = _)` kall_tac >>
  qpat_x_assum `Abbrev (astate = _)` kall_tac >>
  qpat_x_assum `Abbrev (uu = _)` kall_tac >>
  Cases_on `w2n w < 2`
  >- suspend "success"
  >> suspend "failure"
QED

Resume prefix_bool_body_endpoint[success]:
  fs[Abbr `w`, Abbr `nn`] >>
  qexistsl [`jstate`,`LAST gs`,`LAST ts`] >>
  conj_tac >- suspend "edge" >>
  simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "success_safety"
QED

Resume prefix_bool_body_endpoint[failure]:
  fs[Abbr `w`, Abbr `nn`] >>
  Cases >> simp[Once ptr_safe_blocks_def] >>
  qpat_x_assum `!bb'. _ ==> !f. ptr_safe_block _ _ _ _ _ _ _ _ _ _`
    (qspec_then `bb` mp_tac) >>
  simp[Abbr `bb`]
QED

Resume prefix_bool_body_endpoint[edge]:
  `!f. exec_block f ctx bb (vv 0) = OK jstate` suffices_by simp[] >>
  mp_tac (Q.INST [`V` |-> `vv`, `t` |-> `jstate`]
    (PURE_REWRITE_RULE [LET_THM] prefix_bool_body_exec_block)) >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `bb.bb_instructions = body_insts` >>
  `body_insts = insns` by simp[Abbr `body_insts`, Abbr `insns`] >>
  qpat_x_assum `body_insts = insns` SUBST_ALL_TAC >>
  (impl_tac >-
    (simp[Abbr `bb`] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `!j f. j<14 ==> _` (qspecl_then [`j`,`f`] mp_tac) >>
     simp[])) >> simp[]
QED

Resume prefix_bool_body_endpoint[success_safety]:
  strip_tac >> Cases >> simp[Once ptr_safe_blocks_def] >>
  qpat_x_assum `!bb'. _ ==> _ ==> !f. ptr_safe_block _ _ _ _ _ _ _ _ _ _`
    (qspec_then `bb` mp_tac) >>
  simp[Abbr `bb`]
QED

Finalise prefix_bool_body_endpoint

(* The invariant is local to this theorem.  In particular its data section and
   memory frame are anchored at the original input, not at the latest edge. *)
Theorem prefix_bool_loop_from_header:
  let H = abi_decode_header_insts hid (Var ip) (Var src) DLOAD
            hiv cv cmp done body_lbl exit_lbl;
      B =
        [mk_inst iid MLOAD [Var ip] [iv];
         mk_inst (iid+1) ADD [Var src;Lit 32w] [sp0];
         mk_inst (iid+2) MUL [Var iv;Lit 32w] [isrc];
         mk_inst (iid+3) ADD [Var sp0;Var isrc] [sp];
         mk_inst (iid+4) ADD [Var dst;Lit 32w] [dp0];
         mk_inst (iid+5) MUL [Var iv;Lit 32w] [idst];
         mk_inst (iid+6) ADD [Var dp0;Var idst] [dp];
         mk_inst (iid+7) DLOAD [Var sp] [x];
         mk_inst (iid+8) SHR [Lit 1w;Var x] [y];
         mk_inst (iid+9) ISZERO [Var y] [z];
         mk_inst (iid+10) ASSERT [Var z] [];
         mk_inst (iid+11) MSTORE [Var dp;Var x] [];
         mk_inst (iid+12) ADD [Var iv;Lit 1w] [inc];
         mk_inst (iid+13) MSTORE [Var ip;Var inc] [];
         mk_inst (iid+14) JMP [Label hdr] []];
      R = (\v w. ?bb.
        lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
        eval_phis v bb.bb_instructions = OK v /\
        phi_prefix_length bb.bb_instructions = 0 /\ v.vs_inst_idx = 0 /\
        (!f. exec_block f ctx bb v = OK w) /\ ~w.vs_halted);
      value = (\j. abi_decode_load DLOAD (n2w (a+32+32*j):bytes32) s);
      inv = (\k q gh th.
        ~q.vs_halted /\ q.vs_inst_idx = 0 /\ k <= ncount /\
        eval_operand (Var ip) q = SOME (n2w scratch) /\
        eval_operand (Var src) q = SOME (n2w a) /\
        eval_operand (Var dst) q = SOME (n2w d) /\
        FLOOKUP gh ip = SOME (scratch,32) /\ FLOOKUP gh src = NONE /\
        FLOOKUP gh dst = SOME (b,sz) /\
        op_taint th (Var ip) = {} /\ op_taint th (Var src) = {} /\
        op_taint th (Var dst) = {} /\
        q.vs_data_section = s.vs_data_section /\
        q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
        allocas_from lo q /\
        th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\
        th.t_imm = tn.t_imm /\
        mload scratch q = n2w k /\ mload d q = n2w ncount /\
        (!j. j<k ==> w2n (value j) < 2 /\
                       mload (d+32+32*j) q = value j) /\
        (!r. r<32 ==> scratch+r NOTIN th.t_mem) /\
        (!r. r<32*(k+1) ==> d+r NOTIN th.t_mem) /\
        (!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
          (p+len<=scratch \/ scratch+32<=p) ==>
          mem_bytes_at p len q.vs_memory = mem_bytes_at p len s.vs_memory))
  in
    lookup_block hdr fn.fn_blocks = SOME
      <|bb_label := hdr; bb_instructions := H|> /\
    lookup_block body_lbl fn.fn_blocks = SOME
      <|bb_label := body_lbl; bb_instructions := B|> /\
    hdr <> body_lbl /\ hdr <> exit_lbl /\ body_lbl <> exit_lbl /\
    ALL_DISTINCT [ip;src;dst;hiv;cv;cmp;done;iv;sp0;isrc;sp;dp0;idst;dp;x;y;z;inc] /\
    ncount < dimword(:256) /\ a+32*(ncount+1) < dimword(:256) /\
    b <= d /\ d+32*(ncount+1) <= b+sz /\ b+sz <= s.vs_alloca_next /\
    scratch+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword(:256) /\
    lo <= scratch /\ ~ctx_has_dalloca ctx /\
    (d+32*(ncount+1)<=scratch \/ scratch+32<=d) /\
    abi_decode_load DLOAD (n2w a:bytes32) s = n2w ncount /\
    inv i s G tn /\ s.vs_current_bb = hdr ==>
    (?t Gt tt.
      RTC R s t /\ t.vs_current_bb = exit_lbl /\ inv ncount t Gt tt /\
      ((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
        !f. ptr_safe_blocks D lo f ctx fn PG G tn s)) \/
    (?v j. RTC R s v /\ ~v.vs_halted /\ v.vs_current_bb = body_lbl /\
      v.vs_inst_idx = 0 /\ i<=j /\ j<ncount /\ 2<=w2n (value j) /\
      (!k. i<=k /\ k<j ==> w2n (value k)<2) /\
      (?vh. run_inst_seq B v = Abort Revert_abort vh) /\
      (!f. ptr_safe_blocks D lo f ctx fn PG G tn s))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `RTC R` >>
  qmatch_goalsub_abbrev_tac `w2n (value _)` >>
  qmatch_goalsub_abbrev_tac `loop_inv i s G tn` >>
  qmatch_goalsub_abbrev_tac `run_inst_seq body_is _` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!remaining k q gh th.
    remaining = ncount-k /\ loop_inv k q gh th /\ q.vs_current_bb = hdr ==>
    (?t Gt tt. RTC R q t /\ t.vs_current_bb = exit_lbl /\
      loop_inv ncount t Gt tt /\
      ((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
       !f. ptr_safe_blocks D lo f ctx fn PG gh th q)) \/
    (?v j. RTC R q v /\ ~v.vs_halted /\ v.vs_current_bb = body_lbl /\
      v.vs_inst_idx = 0 /\ k<=j /\ j<ncount /\ 2<=w2n (value j) /\
      (!l. k<=l /\ l<j ==> w2n (value l)<2) /\
      (?vh. run_inst_seq body_is v = Abort Revert_abort vh) /\
      (!f. ptr_safe_blocks D lo f ctx fn PG gh th q))`
    suffices_by (disch_then (qspecl_then [`ncount-i`,`i`,`s`,`G`,`tn`] mp_tac) >> simp[]) >>
  ho_match_mp_tac arithmeticTheory.COMPLETE_INDUCTION >>
  qx_gen_tac `remaining` >> strip_tac >>
  map_every qx_gen_tac [`k`,`q`,`gh`,`th`] >> strip_tac >>
  `?h hg ht.
    (!f. exec_block f ctx
      <|bb_label := hdr; bb_instructions :=
        abi_decode_header_insts hid (Var ip) (Var src) DLOAD
          hiv cv cmp done body_lbl exit_lbl|> q = OK h) /\
    h.vs_current_bb = (if k<ncount then body_lbl else exit_lbl) /\
    loop_inv k h hg ht /\ RTC R q h /\
    ((!f. ptr_safe_blocks D lo f ctx fn PG
       (entry_prov fn h hg) (entry_taint_vars fn h ht) h) ==>
       !f. ptr_safe_blocks D lo f ctx fn PG gh th q)` by
    suspend "header" >>
  Cases_on `k=ncount`
  >- (disj1_tac >> qexistsl [`h`,`hg`,`ht`] >> gvs[]) >>
  `k<ncount` by
    (qpat_x_assum `loop_inv k q gh th` mp_tac >> simp[Abbr `loop_inv`]) >>
  suspend "iteration"
QED

Resume prefix_bool_loop_from_header[header]:
  mp_tac (Q.INST [`s` |-> `q`, `G` |-> `gh`, `tn` |-> `th`,
    `i` |-> `k`, `iv` |-> `hiv`] prefix_bool_header_endpoint) >>
  (impl_tac >-
    (qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
     qpat_x_assum `loop_inv i s G tn` kall_tac >>
     gvs[Abbr `loop_inv`, ALL_DISTINCT] >>
     gvs[abi_decode_load_def, abi_decode_source_def])) >>
  disch_then (qx_choose_then `hstate` (qx_choose_then `hghost`
    (qx_choose_then `htaint` strip_assume_tac))) >>
  qexistsl [`hstate`,`hghost`,`htaint`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "header_inv" >>
  conj_tac >- suspend "header_rtc" >> simp[]
QED

Resume prefix_bool_loop_from_header[header_inv]:
  qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
  qpat_x_assum `loop_inv i s G tn` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  gvs[Abbr `loop_inv`] >>
  fs[mload_def] >>
  first_assum ACCEPT_TAC
QED

Resume prefix_bool_loop_from_header[header_rtc]:
  irule relationTheory.RTC_SINGLE >>
  simp[Abbr `R`] >>
  simp[abi_decode_header_insts_def, eval_phis_def,
       phi_prefix_length_def, mk_inst_def] >>
  gvs[Abbr `loop_inv`]
QED

Resume prefix_bool_loop_from_header[iteration]:
  `h.vs_current_bb = body_lbl` by simp[] >>
  `entry_prov fn h hg = hg /\ entry_taint_vars fn h ht = ht` by
    (simp[entry_prov_def, entry_taint_vars_def, Abbr `body_is`,
          phis_prov_def, phis_taint_def, mk_inst_def]) >>
  mp_tac (Q.INST [`s` |-> `h`, `G` |-> `hg`, `tn` |-> `ht`,
    `i` |-> `k`] (PURE_REWRITE_RULE [LET_THM] prefix_bool_body_endpoint)) >>
  BETA_TAC >>
  (impl_tac >- suspend "body_premises") >>
  `abi_decode_load DLOAD (n2w (a+32+32*k):bytes32) h = value k` by
    (qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
     qpat_x_assum `loop_inv i s G tn` kall_tac >>
     gvs[Abbr `loop_inv`, Abbr `value`, abi_decode_load_def, abi_decode_source_def]) >>
  simp[] >> Cases_on `w2n (value k)<2`
  >- suspend "body_success" >>
  suspend "body_failure"
QED

Resume prefix_bool_loop_from_header[body_premises]:
  qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
  qpat_x_assum `loop_inv i s G tn` kall_tac >>
  qpat_x_assum `loop_inv k q gh th` kall_tac >>
  gvs[Abbr `loop_inv`, Abbr `body_is`, ALL_DISTINCT] >>
  first_assum ACCEPT_TAC
QED

Resume prefix_bool_loop_from_header[body_failure]:
  simp[] >> strip_tac >> disj2_tac >> qexistsl [`h`,`k`] >>
  simp[Abbr `body_is`] >>
  qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
  qpat_x_assum `loop_inv i s G tn` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  gvs[Abbr `loop_inv`]
QED

Resume prefix_bool_loop_from_header[body_success]:
  simp[] >> disch_then (qx_choose_then `u` (qx_choose_then `ug`
    (qx_choose_then `ut` strip_assume_tac))) >>
  `loop_inv (SUC k) u ug ut` by suspend "next_inv" >>
  `RTC R h u` by suspend "body_rtc" >>
  `entry_prov fn u ug = ug /\ entry_taint_vars fn u ut = ut` by
    (simp[entry_prov_def, entry_taint_vars_def,
      abi_decode_header_insts_def, phis_prov_def, phis_taint_def, mk_inst_def]) >>
  `ncount-SUC k < remaining` by decide_tac >>
  qpat_x_assum `!remaining'. remaining' < remaining ==> _`
    (qspec_then `ncount-SUC k` mp_tac) >>
  simp[] >> disch_then (qspecl_then [`SUC k`,`u`,`ug`,`ut`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "recur_success" >>
  suspend "recur_failure"
QED

Resume prefix_bool_loop_from_header[next_inv]:
  qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
  qpat_x_assum `loop_inv i s G tn` kall_tac >>
  qpat_x_assum `loop_inv k q gh th` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  gvs[Abbr `loop_inv`] >>
  (conj_tac
   >- (rpt strip_tac >> Cases_on `j=k` >> gvs[] >>
       `j<k` by decide_tac >> simp[]) >>
   rpt strip_tac >>
   qpat_x_assum `!p len. _ ==> mem_bytes_at p len u.vs_memory = _`
     (qspecl_then [`p`,`len`] mp_tac) >>
   qpat_x_assum `!p len. _ ==> mem_bytes_at p len h.vs_memory = _`
     (qspecl_then [`p`,`len`] mp_tac) >>
   simp[])
QED

Resume prefix_bool_loop_from_header[body_rtc]:
  qpat_x_assum `!remaining'. remaining' < remaining ==> _` kall_tac >>
  qpat_x_assum `ALL_DISTINCT _` kall_tac >>
  irule relationTheory.RTC_SINGLE >>
  simp[Abbr `R`, Abbr `body_is`, eval_phis_def,
       phi_prefix_length_def, mk_inst_def] >>
  `h.vs_inst_idx = 0` by
    (qpat_x_assum `loop_inv k h hg ht` mp_tac >>
     simp[Abbr `loop_inv`]) >>
  simp[] >>
  qpat_x_assum `!f. run_block_non_phis f ctx _ h = OK u` mp_tac >>
  simp[mk_inst_def]
QED

Resume prefix_bool_loop_from_header[recur_success]:
  disj1_tac >> qexistsl [`t`,`Gt'`,`tt`] >>
  conj_tac >- metis_tac[relationTheory.RTC_TRANS] >>
  simp[] >> metis_tac[]
QED

Resume prefix_bool_loop_from_header[recur_failure]:
  disj2_tac >> qexistsl [`v`,`j`] >>
  conj_tac >- metis_tac[relationTheory.RTC_TRANS] >>
  `k<=j` by decide_tac >>
  simp[] >> rpt strip_tac >> Cases_on `l=k`
  >- simp[] >>
  `SUC k<=l` by decide_tac >> simp[]
QED

Finalise prefix_bool_loop_from_header

val _ = export_theory();
