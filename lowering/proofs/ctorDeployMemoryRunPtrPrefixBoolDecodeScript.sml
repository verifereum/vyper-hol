Theory ctorDeployMemoryRunPtrPrefixBoolDecode
Ancestors
  list words arithmetic relation venomInst abiDecoderContract
  ctorDeployMemoryRunPtrPrefixBoolShape
  ctorDeployMemoryRunPtrPrefixBoolPreheader
  ctorDeployMemoryRunPtrPrefixBoolLoop

(* Compiler-indexed entry boundary: callers never specialize loop temporaries. *)
Theorem prefix_bool_decode_loop_initial:
  let x = (\k. "%" ++ toString(st.cs_next_var+k));
      hdr = EL 1 sf.cs_blocks; bod = EL 0 sf.cs_blocks;
      R = (\v w. ?bb.
        lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
        eval_phis v bb.bb_instructions = OK v /\
        phi_prefix_length bb.bb_instructions = 0 /\ v.vs_inst_idx = 0 /\
        (!f. exec_block f ctx bb v = OK w) /\ ~w.vs_halted);
      value = (\j. abi_decode_load DLOAD (n2w(a+32+32*j):bytes32) h);
      inv = (\k q gh th.
        ~q.vs_halted /\ q.vs_inst_idx = 0 /\ k <= ncount /\
        eval_operand (Var(x 9)) q = SOME(n2w scratch) /\
        eval_operand (Var src) q = SOME(n2w a) /\
        eval_operand (Var dst) q = SOME(n2w d) /\
        FLOOKUP gh (x 9) = SOME(scratch,32) /\ FLOOKUP gh src = NONE /\
        FLOOKUP gh dst = SOME(b,sz) /\
        op_taint th (Var(x 9)) = {} /\ op_taint th (Var src) = {} /\
        op_taint th (Var dst) = {} /\
        q.vs_data_section = h.vs_data_section /\
        q.vs_allocas = h.vs_allocas /\ q.vs_alloca_next = h.vs_alloca_next /\
        allocas_from lo q /\
        th.t_stor = tn.t_stor /\ th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
        mload scratch q = n2w k /\ mload d q = n2w ncount /\
        (!j. j<k ==> w2n(value j)<2 /\ mload (d+32+32*j) q = value j) /\
        (!r. r<32 ==> scratch+r NOTIN th.t_mem) /\
        (!r. r<32*(k+1) ==> d+r NOTIN th.t_mem) /\
        (!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
          (p+len<=scratch \/ scratch+32<=p) ==>
          mem_bytes_at p len q.vs_memory = mem_bytes_at p len h.vs_memory))
  in
    0 < data_size /\ data_size < dimword(:256) /\
    compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit(n2w data_size))
      (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) /\
    fn_has_code st sf fn /\
    not_fresh_at st src /\ not_fresh_at st dst /\ src<>dst /\
    ~h.vs_halted /\ h.vs_inst_idx=0 /\ h.vs_current_bb=hdr.bb_label /\
    eval_operand (Var(x 9)) h = SOME(n2w scratch) /\
    eval_operand (Var src) h = SOME(n2w a) /\
    eval_operand (Var dst) h = SOME(n2w d) /\
    FLOOKUP G (x 9) = SOME(scratch,32) /\ FLOOKUP G src = NONE /\
    FLOOKUP G dst = SOME(b,sz) /\
    op_taint tn (Var(x 9)) = {} /\ op_taint tn (Var src) = {} /\
    op_taint tn (Var dst) = {} /\
    mload scratch h = 0w /\ mload d h = n2w ncount /\
    (!r. r<32 ==> scratch+r NOTIN tn.t_mem /\ d+r NOTIN tn.t_mem) /\
    allocas_from lo h /\
    ncount < dimword(:256) /\ a+32*(ncount+1) < dimword(:256) /\
    b<=d /\ d+32*(ncount+1)<=b+sz /\ b+sz<=scratch /\
    scratch+32<=h.vs_alloca_next /\ h.vs_alloca_next<dimword(:256) /\
    lo<=scratch /\ ~ctx_has_dalloca ctx /\
    abi_decode_load DLOAD (n2w a:bytes32) h = n2w ncount ==>
    (?t Gt tt. RTC R h t /\ t.vs_current_bb=sf.cs_current_bb /\
      inv ncount t Gt tt /\
      ((!f. ptr_safe_blocks D lo f ctx fn PG
         (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
       !f. ptr_safe_blocks D lo f ctx fn PG G tn h)) \/
    (?v j. RTC R h v /\ ~v.vs_halted /\ v.vs_current_bb=bod.bb_label /\
      v.vs_inst_idx=0 /\ j<ncount /\ 2<=w2n(value j) /\
      (!k. k<j ==> w2n(value k)<2) /\
      (?vh. run_inst_seq bod.bb_instructions v = Abort Revert_abort vh) /\
      (!f. ptr_safe_blocks D lo f ctx fn PG G tn h))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qmatch_goalsub_abbrev_tac `RTC R` >>
  qmatch_goalsub_abbrev_tac `loop_inv ncount` >>
  drule_all prefix_bool_decode_compile >>
  disch_then (qspecl_then [`st`,`dst`,`src`,`max_count`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `(_, sfcode)` >> strip_tac >>
  `sf = sfcode` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sfcode)` mp_tac >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sf)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sfcode)` kall_tac >>
  `sf.cs_blocks = EL 0 sf.cs_blocks :: EL 1 sf.cs_blocks ::
     EL 2 sf.cs_blocks :: st.cs_blocks /\ sf.cs_current_insts = []` by
    simp[Abbr `sfcode`] >>
  drule_all prefix_bool_decode_blocks_lookup >> strip_tac >>
  qabbrev_tac `bod = EL 0 sf.cs_blocks` >>
  qabbrev_tac `hdr = EL 1 sf.cs_blocks` >>
  qabbrev_tac `x = (\k. "%" ++ toString(st.cs_next_var+k))` >>
  `lookup_block hdr.bb_label fn.fn_blocks = SOME
    <|bb_label := hdr.bb_label; bb_instructions :=
      abi_decode_header_insts (st.cs_next_id+15) (Var(x 9)) (Var src) DLOAD
        (x 10) (x 11) (x 12) (x 13) bod.bb_label sf.cs_current_bb|>` by
    simp[Abbr `hdr`, Abbr `bod`, Abbr `sfcode`, Abbr `x`,
         basic_block_component_equality] >>
  `lookup_block bod.bb_label fn.fn_blocks = SOME
    <|bb_label := bod.bb_label; bb_instructions :=
      [mk_inst (st.cs_next_id+20) MLOAD [Var(x 9)] [x 14];
       mk_inst ((st.cs_next_id+20)+1) ADD [Var src;Lit 32w] [x 15];
       mk_inst ((st.cs_next_id+20)+2) MUL [Var(x 14);Lit 32w] [x 16];
       mk_inst ((st.cs_next_id+20)+3) ADD [Var(x 15);Var(x 16)] [x 17];
       mk_inst ((st.cs_next_id+20)+4) ADD [Var dst;Lit 32w] [x 18];
       mk_inst ((st.cs_next_id+20)+5) MUL [Var(x 14);Lit 32w] [x 19];
       mk_inst ((st.cs_next_id+20)+6) ADD [Var(x 18);Var(x 19)] [x 20];
       mk_inst ((st.cs_next_id+20)+7) DLOAD [Var(x 17)] [x 21];
       mk_inst ((st.cs_next_id+20)+8) SHR [Lit 1w;Var(x 21)] [x 22];
       mk_inst ((st.cs_next_id+20)+9) ISZERO [Var(x 22)] [x 23];
       mk_inst ((st.cs_next_id+20)+10) ASSERT [Var(x 23)] [];
       mk_inst ((st.cs_next_id+20)+11) MSTORE [Var(x 20);Var(x 21)] [];
       mk_inst ((st.cs_next_id+20)+12) ADD [Var(x 14);Lit 1w] [x 24];
       mk_inst ((st.cs_next_id+20)+13) MSTORE [Var(x 9);Var(x 24)] [];
       mk_inst ((st.cs_next_id+20)+14) JMP [Label hdr.bb_label] []]|>` by
    simp[Abbr `hdr`, Abbr `bod`, Abbr `sfcode`, Abbr `x`,
         basic_block_component_equality] >>
  qpat_x_assum `lookup_block bod.bb_label fn.fn_blocks = SOME bod` mp_tac >>
  simp[basic_block_component_equality] >> strip_tac >>
  drule (Q.INST [`i` |-> `0`]
    (BETA_RULE (PURE_REWRITE_RULE [LET_THM] prefix_bool_loop_from_header))) >>
  disch_then drule >>
  suspend "instantiate"
QED
Resume prefix_bool_decode_loop_initial[instantiate]:
  `hdr.bb_label <> bod.bb_label /\ hdr.bb_label <> sf.cs_current_bb /\
     bod.bb_label <> sf.cs_current_bb` by
    (mp_tac (Q.SPEC `st` prefix_bool_decode_labels_distinct) >>
     simp[Abbr `hdr`, Abbr `bod`, Abbr `sfcode`, ALL_DISTINCT]) >>
  `(!i j. x i = x j <=> i=j) /\ (!i. src <> x i) /\ (!i. dst <> x i)` by
    (conj_tac >- simp[Abbr `x`, prefix_bool_decode_var_inj] >>
     conj_tac
     >- (qpat_assum `not_fresh_at st src`
           (mp_tac o MATCH_MP prefix_bool_decode_var_separation) >> simp[Abbr `x`]) >>
     qpat_assum `not_fresh_at st dst`
       (mp_tac o MATCH_MP prefix_bool_decode_var_separation) >> simp[Abbr `x`]) >>
  `ALL_DISTINCT [x 9;src;dst;x 10;x 11;x 12;x 13;x 14;x 15;x 16;
     x 17;x 18;x 19;x 20;x 21;x 22;x 23;x 24]` by simp[ALL_DISTINCT] >>
  `b+sz <= h.vs_alloca_next /\ d+32*(ncount+1)<=scratch` by decide_tac >>
  `!r. r<32 ==> scratch+r NOTIN tn.t_mem` by simp[] >>
  `!r. r<32 ==> d+r NOTIN tn.t_mem` by simp[] >>
  qpat_x_assum `Abbrev (sfcode = _)` kall_tac >>
  disch_then (mp_tac o Q.INST [`s''` |-> `h`] o SPEC_ALL) >>
  (impl_tac >- (simp[Abbr `loop_inv`] >> metis_tac[ADD_COMM])) >>
  strip_tac
  >- (disj1_tac >> qexistsl [`t`,`Gt'`,`tt`] >>
      gvs[Abbr `R`, Abbr `loop_inv`] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`v`,`j`] >>
  gvs[Abbr `R`]
QED
Finalise prefix_bool_decode_loop_initial

Theorem prefix_bool_decode_paired:
  let x = (\k. "%" ++ toString (st.cs_next_var+k));
      pre = EL 2 sf.cs_blocks;
      body = EL 0 sf.cs_blocks;
      scratch = s.vs_alloca_next;
      ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s);
      R = (\v w. ?bb.
        lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
        eval_phis v bb.bb_instructions = OK v /\
        phi_prefix_length bb.bb_instructions = 0 /\ v.vs_inst_idx = 0 /\
        (!f. exec_block f ctx bb v = OK w) /\ ~w.vs_halted)
  in
    0 < data_size /\ data_size < dimword(:256) /\
    compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit(n2w data_size))
      (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),sf) /\
    fn_has_code st sf fn /\
    not_fresh_at st src /\ not_fresh_at st dst /\ src <> dst /\
    fresh_vars_wrt st s /\
    (!k. FLOOKUP G (x k) = NONE /\ op_taint tn (Var(x k)) = {}) /\
    s.vs_inst_idx = LENGTH st.cs_current_insts /\
    s.vs_current_bb = st.cs_current_bb /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    eval_operand (Var src) s = SOME(n2w a) /\
    eval_operand (Var dst) s = SOME(n2w d) /\
    FLOOKUP G src = NONE /\ FLOOKUP G dst = SOME(b,sz) /\
    op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
    allocas_from lo s /\ lo <= scratch /\ scratch+32 < dimword(:256) /\
    FLOOKUP s.vs_allocas (st.cs_next_id+12) = NONE /\
    b <= d /\ d+32*(max_count+1) <= b+sz /\ b+sz <= scratch /\
    max_count < dimword(:256) /\ a+32*(max_count+1) < dimword(:256) ==>
    (?vh. (!f. exec_block f ctx pre s = Abort Revert_abort vh) /\
      (!f. ptr_safe_block D lo f ctx fn PG G tn pre s)) \/
    (?h t Gt tt.
      (!f. exec_block f ctx pre s = OK h) /\ RTC R h t /\
      t.vs_current_bb = sf.cs_current_bb /\ ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      ncount <= max_count /\ a+32*(ncount+1) <= data_size /\
      eval_operand (Var src) t = SOME(n2w a) /\
      eval_operand (Var dst) t = SOME(n2w d) /\
      FLOOKUP Gt src = NONE /\ FLOOKUP Gt dst = SOME(b,sz) /\
      op_taint tt (Var src) = {} /\ op_taint tt (Var dst) = {} /\
      mload scratch t = n2w ncount /\ mload d t = n2w ncount /\
      (!j. j<ncount ==> w2n (abi_decode_load DLOAD (n2w(a+32+32*j):bytes32) s)<2 /\
        mload (d+32+32*j) t = abi_decode_load DLOAD (n2w(a+32+32*j):bytes32) s) /\
      (!r. r<32 ==> scratch+r NOTIN tt.t_mem) /\
      (!r. r<32*(ncount+1) ==> d+r NOTIN tt.t_mem) /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_allocas = s.vs_allocas |+ (st.cs_next_id+12,(scratch,32)) /\
      t.vs_alloca_next = scratch+32 /\ allocas_from lo t /\
      tt.t_stor = tn.t_stor /\ tt.t_trans = tn.t_trans /\ tt.t_imm = tn.t_imm /\
      (!p len. (p+len<=d \/ d+32*(ncount+1)<=p) /\
        (p+len<=scratch \/ scratch+32<=p) ==>
        mem_bytes_at p len t.vs_memory = mem_bytes_at p len s.vs_memory) /\
      ((!f. ptr_safe_blocks D lo f ctx fn PG
        (entry_prov fn t Gt) (entry_taint_vars fn t tt) t) ==>
       !f. ptr_safe_block D lo f ctx fn PG G tn pre s)) \/
    (?h v j vh.
      (!f. exec_block f ctx pre s = OK h) /\ RTC R h v /\
      ~v.vs_halted /\ v.vs_current_bb = body.bb_label /\ v.vs_inst_idx = 0 /\
      j<ncount /\ 2<=w2n (abi_decode_load DLOAD (n2w(a+32+32*j):bytes32) s) /\
      (!k. k<j ==> w2n (abi_decode_load DLOAD (n2w(a+32+32*k):bytes32) s)<2) /\
      run_inst_seq body.bb_instructions v = Abort Revert_abort vh /\
      (!f. ptr_safe_block D lo f ctx fn PG G tn pre s))
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all prefix_bool_decode_compile >>
  disch_then (qspecl_then [`st`,`dst`,`src`,`max_count`] mp_tac) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `(_, sfcode)` >>
  strip_tac >>
  `sf = sfcode` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sfcode)` mp_tac >>
     qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sf)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = (_,sfcode)` kall_tac >>
  `sf.cs_blocks = EL 0 sf.cs_blocks :: EL 1 sf.cs_blocks ::
     EL 2 sf.cs_blocks :: st.cs_blocks /\ sf.cs_current_insts = []` by
    simp[Abbr `sfcode`] >>
  drule_all prefix_bool_decode_blocks_lookup >> strip_tac >>
  qabbrev_tac `bod = EL 0 sf.cs_blocks` >>
  qabbrev_tac `hdr = EL 1 sf.cs_blocks` >>
  qabbrev_tac `pre = EL 2 sf.cs_blocks` >>
  qabbrev_tac `x = (\k. "%" ++ toString(st.cs_next_var+k))` >>
  `!k. "%" ++ toString(st.cs_next_var+k) = x k` by simp[Abbr `x`] >>
  `pre.bb_label = st.cs_current_bb` by simp[Abbr `pre`, Abbr `sfcode`] >>
  `pre.bb_instructions = st.cs_current_insts ++
    [mk_inst st.cs_next_id DLOAD [Var src] [x 0];
     mk_inst (st.cs_next_id+1) GT [Var(x 0);Lit(n2w max_count)] [x 1];
     mk_inst (st.cs_next_id+2) ISZERO [Var(x 1)] [x 2];
     mk_inst (st.cs_next_id+3) ASSERT [Var(x 2)] [];
     mk_inst (st.cs_next_id+4) MUL [Var(x 0);Lit 32w] [x 3];
     mk_inst (st.cs_next_id+5) ADD [Var(x 3);Lit 32w] [x 4];
     mk_inst (st.cs_next_id+6) ADD [Var src;Var(x 4)] [x 5];
     mk_inst (st.cs_next_id+7) GT [Var(x 5);Lit(n2w data_size)] [x 6];
     mk_inst (st.cs_next_id+8) ISZERO [Var(x 6)] [x 7];
     mk_inst (st.cs_next_id+9) ASSERT [Var(x 7)] [];
     mk_inst (st.cs_next_id+10) DLOAD [Var src] [x 8];
     mk_inst (st.cs_next_id+11) MSTORE [Var dst;Var(x 8)] [];
     mk_inst (st.cs_next_id+12) ALLOCA [Lit 32w] [x 9];
     mk_inst (st.cs_next_id+13) MSTORE [Var(x 9);Lit 0w] [];
     mk_inst (st.cs_next_id+14) JMP [Label hdr.bb_label] []]` by
    simp[Abbr `pre`, Abbr `hdr`, Abbr `sfcode`, Abbr `x`] >>
  `hdr.bb_instructions = abi_decode_header_insts (st.cs_next_id+15)
     (Var(x 9)) (Var src) DLOAD (x 10) (x 11) (x 12) (x 13)
     bod.bb_label sf.cs_current_bb` by
    simp[Abbr `hdr`, Abbr `bod`, Abbr `sfcode`, Abbr `x`] >>
  `hdr.bb_label <> bod.bb_label /\ hdr.bb_label <> sf.cs_current_bb /\
     bod.bb_label <> sf.cs_current_bb` by
    (mp_tac (Q.SPEC `st` prefix_bool_decode_labels_distinct) >>
     simp[Abbr `hdr`, Abbr `bod`, Abbr `sfcode`, ALL_DISTINCT]) >>
  `(!i j. x i = x j <=> i=j) /\ (!i. src <> x i) /\ (!i. dst <> x i)` by
    (conj_tac >- simp[Abbr `x`, prefix_bool_decode_var_inj] >>
     conj_tac
     >- (qpat_assum `not_fresh_at st src`
           (mp_tac o MATCH_MP prefix_bool_decode_var_separation) >> simp[Abbr `x`]) >>
     qpat_assum `not_fresh_at st dst`
       (mp_tac o MATCH_MP prefix_bool_decode_var_separation) >> simp[Abbr `x`]) >>
  qpat_x_assum `Abbrev (sfcode = _)` kall_tac >>
  suspend "layout"
QED

Resume prefix_bool_decode_paired[layout]:
  `s.vs_current_bb = pre.bb_label` by simp[] >>
  `ALL_DISTINCT [src;dst;x 0;x 1;x 2;x 3;x 4;x 5;x 6;x 7;x 8;x 9]` by
    simp[ALL_DISTINCT] >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] prefix_bool_preheader_paired)) >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
  disch_then (DISJ_CASES_THEN2 mp_tac mp_tac)
  >- (strip_tac >> disj1_tac >> qexists_tac `vh` >> simp[]) >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `RTC R` >>
  qabbrev_tac `ncount = w2n (abi_decode_load DLOAD (n2w a:bytes32) s)` >>
  suspend "loop"
QED
Resume prefix_bool_decode_paired[loop]:
  `ncount < dimword(:256) /\ a+32*(ncount+1)<dimword(:256) /\
   d+32*(ncount+1)<=b+sz /\ b+sz<=s.vs_alloca_next /\
   s.vs_alloca_next+32<=h.vs_alloca_next /\
   h.vs_alloca_next<dimword(:256) /\ lo<=s.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `abi_decode_load DLOAD (n2w a:bytes32) h = n2w ncount` by
    simp[abi_decode_load_def, abi_decode_source_def, Abbr `ncount`] >>
  `lookup_block h.vs_current_bb fn.fn_blocks = SOME hdr` by simp[] >>
  drule_all prefix_bool_header_entry >>
  disch_then (qspecl_then [`Gh`,`th`] strip_assume_tac) >>
  mp_tac (Q.INST [`G` |-> `Gh`, `tn` |-> `th`,
      `scratch` |-> `s.vs_alloca_next`]
    (SPEC_ALL (BETA_RULE (PURE_REWRITE_RULE [LET_THM] prefix_bool_decode_loop_initial)))) >>
  (impl_tac >- simp[Abbr `x`, Abbr `hdr`]) >>
  `!p:bytes32. abi_decode_load DLOAD p h = abi_decode_load DLOAD p s` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  strip_tac
  >- (disj2_tac >> disj1_tac >> qexistsl [`h`,`t`,`Gt'`,`tt`] >>
      gvs[Abbr `R`, Abbr `x`] >>
      rpt gen_tac >> disch_tac >>
          qpat_x_assum `!p len. _ ==> mem_bytes_at p len t.vs_memory = _`
            (qspecl_then [`p`,`len`] mp_tac) >>
          impl_tac >- simp[] >>
          disch_then SUBST1_TAC >>
          qpat_x_assum `!p len. _ ==> mem_bytes_at p len h.vs_memory = _`
            (qspecl_then [`p`,`len`] mp_tac) >>
          impl_tac >- (simp[] >> decide_tac) >> simp[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl [`h`,`v`,`j`,`vh`] >>
  gvs[Abbr `R`, Abbr `bod`]
QED

val _ = export_theory();
