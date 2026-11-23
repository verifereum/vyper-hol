(* The counted storage/transient copy, with its computed states certified in
   the original function's instruction-ID band. *)
Theory createCtorSlotLoopOriginBand
Ancestors
  createCtorStraightBand createCtorSegmentArrival fragGasStorageCopyBodyProps fragGasStorageCopyHeaderProps fragGasCopyLoop fragGasOriginPtrLoop
  fragGasCopySeqLiftProps
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy bodyStorageCopyMemory
  fragGasSeqPtrContext fragGasSeqPtr fragGasSeqAbort fragGasOriginPtr instMemFrontier
  exprLoweringProps ptrDisciplineTaintProps memLocDefs
  fragExec fragExecMem codegenRel contextCodegenRel ptrDiscipline ptrSafeRun memSafeRun
  venomExecSemantics venomExecProofs venomState venomInst instIdxIndep
  list rich_list relation arithmetic words finite_map

Theorem slot_jump_band[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  loId <= i.inst_id /\ i.inst_id < hiId /\ i.inst_opcode <> INVOKE /\
  is_terminator i.inst_opcode /\ step_inst_base i s = OK (jump_to lbl s) /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                 loId <= i.inst_id /\ i.inst_id < hiId /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (jump_to lbl s)
Proof
  strip_tac >> irule RTC_SINGLE >> BETA_TAC >> qexists_tac `i` >>
  simp[ctor_segment_fetch_def, ctor_segment_next_def, ctor_segment_entry_def,
       eval_phis_no_phi, jump_to_def]
QED

Theorem slot_jmp_band[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id JMP [Label lbl] []) /\
  loId <= id /\ id < hiId /\
  lookup_block lbl func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                 loId <= i.inst_id /\ i.inst_id < hiId /\
                 i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v)
    s (jump_to lbl s)
Proof
  strip_tac >> irule slot_jump_band >>
  simp[mk_inst_def, is_terminator_def, step_jmp_behavior]
QED

Theorem slot_init_origin_band[local]:
  MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  DROP s.vs_inst_idx bb.bb_instructions =
    [mk_inst id ASSIGN [Lit 0w] [cv]; mk_inst (id+1) JMP [Label hdr] []] /\
  loId <= id /\ id+1 < hiId /\
  lookup_block hdr func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  !loc D explicit PG. ?t G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                   loId <= i.inst_id /\ i.inst_id < hiId /\
                   i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s t /\
    (toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
     allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t)) /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  `get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by
    (`isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]; mk_inst (id+1) JMP [Label hdr] []]
        (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
     drule instruction_prefix_cursor >> strip_tac >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  drule_all copy_init_origin_ptr >>
  disch_then (qspecl_then [`D`,`explicit`,`PG`,`G`,`tn`] assume_tac) >>
  qabbrev_tac `u = update_var cv 0w s` >>
  qabbrev_tac `t0 = u with vs_inst_idx := s.vs_inst_idx + 1` >>
  qabbrev_tac `i0 = mk_inst id ASSIGN [Lit 0w] [cv]` >>
  qexistsl_tac [`jump_to hdr t0`, `step_prov PG G i0 u`, `step_taint i0 s u tn`] >>
  conj_tac >- fs[Abbr `t0`, Abbr `u`, Abbr `i0`] >>
  conj_tac
  >- (irule RTC_TRANS >> qexists_tac `t0` >> conj_tac
      >- (simp[Abbr `t0`] >>
          irule (SIMP_RULE (srw_ss()) [] (Q.SPEC `[i0]` ctor_straight_band_run)) >>
          qexists_tac `bb` >>
          simp[Abbr `i0`, Abbr `u`, mk_inst_def, is_terminator_def,
               run_inst_seq_def, step_inst_base_def, eval_operands_def,
               eval_operand_def] >> decide_tac) >>
      irule slot_jmp_band >> simp[Abbr `t0`, Abbr `u`, update_var_def] >>
      qexists_tac `id+1` >> simp[] >> decide_tac) >>
  simp[Abbr `t0`, Abbr `u`, Abbr `i0`] >> rpt conj_tac
  >- (pure_rewrite_tac[GSYM update_var_def] >>
      irule toplevel_copy_init_inv >> simp[] >> metis_tac[])
  >- (gvs[allocas_from_def, jump_to_def, update_var_def] >> metis_tac[]) >>
  gvs[jump_to_def, update_var_def, allocas_below_fmp_def] >> metis_tac[]
QED

fun slot_origin_continue path =
  qpat_assum path (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then irule

Theorem slot_header_origin_band[local]:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
    mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  loId <= id /\ id+1 < hiId /\
  lookup_block (if k=n then exit_lbl else body_lbl) func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                   loId <= i.inst_id /\ i.inst_id < hiId /\
                   i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s r /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 r /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)) /\
    ~r.vs_halted /\ r.vs_inst_idx = 0 /\
    r.vs_current_bb = (if k=n then exit_lbl else body_lbl)
Proof
  rpt strip_tac >>
  drule_all storage_copy_header_ptr_run >>
  disch_then (qspecl_then [`D`,`PG`]
    (qx_choosel_then [`u`,`t`,`G1`,`tn1`] strip_assume_tac)) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac)
    run_inst_seq_origin_ptr_lift >>
  qpat_x_assum `t = _ with vs_inst_idx := _`
    (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)` by
    simp[Abbr `t`] >>
  qabbrev_tac `i0 = mk_inst id EQ [Var cv;Lit (n2w n)] [tv]` >>
  qmatch_asmsub_abbrev_tac `get_instruction bb (SUC s.vs_inst_idx) = SOME i1` >>
  qabbrev_tac `lbl = if k=n then exit_lbl else body_lbl` >>
  `get_instruction bb t.vs_inst_idx = SOME i1` by simp[] >>
  `step_inst_base i1 t = OK (jump_to lbl t)` by
    (Cases_on `k=n` >>
     simp[Abbr `i1`, Abbr `lbl`, step_inst_base_def, mk_inst_def, eval_operand_def,
          bool_to_word_def]) >>
  qexistsl_tac [`jump_to lbl t`, `G1`, `tn1`] >>
  conj_tac
  >- (slot_origin_continue `gas_origin_ptr_path _ (s,G,tn) [] (OK t,G1,tn1)` >>
      simp[Abbr `lbl`] >>
      irule (SRULE [bool_to_word_def] (Q.INST [`w` |-> `bool_to_word (k = n)`]
                       (SPEC_ALL jnz_origin_ptr_path))) >> simp[] >>
      qexistsl_tac [`Var tv`, `id+1`] >>
      simp[Abbr `i1`, eval_operand_def, bool_to_word_def]) >>
  conj_tac
  >- (irule RTC_TRANS >> qexists_tac `t` >> conj_tac
      >- (simp[Abbr `t`] >>
          irule (SIMP_RULE (srw_ss()) [] (Q.SPEC `[i0]` ctor_straight_band_run)) >>
          qexistsl_tac [`bb`,`i0`] >>
          fs[Abbr `i0`, mk_inst_def, is_terminator_def] >> decide_tac) >>
      irule slot_jump_band >> simp[] >> simp[Abbr `i1`, mk_inst_def, is_terminator_def] >> decide_tac) >>
  gvs[Abbr `lbl`, jump_to_def, allocas_from_def, allocas_below_fmp_def] >> metis_tac[]
QED

Theorem slot_body_origin_band[local]:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  allocas_from lo s /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
  ~MEM dst [cv;sv;vv;mv;dv;nv] /\
  (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv]) /\
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\ k < n /\
  ~s.vs_halted /\ s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME
    <|bb_label := s.vs_current_bb; bb_instructions :=
      [mk_inst id ADD [src;Var cv] [sv];
       mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
       mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
       mk_inst (id+3) ADD [Var dst;Var mv] [dv];
       mk_inst (id+4) MSTORE [Var dv;Var vv] [];
       mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
       mk_inst (id+6) ASSIGN [Var nv] [cv];
       mk_inst (id+7) JMP [Label hdr] []]|> /\
  loId <= id /\ id+7 < hiId /\
  lookup_block hdr func.fn_blocks = SOME target /\
  phi_prefix_length target.bb_instructions = 0 ==>
  !D explicit PG. ?r G1 tn1.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G1,tn1) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                   loId <= i.inst_id /\ i.inst_id < hiId /\
                   i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s r /\
    (toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 (k+1) G1 tn1 r /\
     allocas_from lo r /\ (ctx_has_dalloca ctx ==> allocas_below_fmp r)) /\
    ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >>
  drule_at (Pat `lookup_block _ _ = SOME <|bb_label := _; bb_instructions := _|>`)
    storage_copy_body_origin_path >>
  disch_then drule_all >>
  disch_then (qspecl_then [`D`, `explicit`, `PG`]
    (qx_choosel_then [`r`, `G1`, `tn1`] strip_assume_tac)) >>
  qexistsl_tac [`r`, `G1`, `tn1`] >> simp[] >>
  rename1 `run_inst_seq code s = OK u` >>
  rename1 `r = jump_to hdr t` >>
  `EVERY (\i. loId <= i.inst_id /\ i.inst_id < hiId) code` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac) >>
  irule RTC_TRANS >> qexists_tac `t` >> conj_tac
  >- (qpat_assum `t = u with vs_inst_idx := _` (pure_rewrite_tac o single) >>
      MATCH_MP_TAC (Q.SPECL [`code`, `s`, `u`, `bb`, `func`, `loId`, `hiId`]
        ctor_straight_band_run) >> simp[]) >>
  `loId <= id+7` by decide_tac >>
  mp_tac (Q.INST [`s` |-> `t`, `lbl` |-> `hdr`, `id` |-> `id+7`]
    slot_jmp_band) >> asm_rewrite_tac[ADD_CLAUSES]
QED

Theorem ctor_slot_loop_origin_band:
  compile_word_copy_loop src (Var dst) n loc LocMemory F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc = LocStorage \/ loc = LocTransient) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  not_fresh_at sa dst /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  n < 2**256 /\ b + 32*n < 2**256 /\ b + 32*n <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME exitbb /\
  phi_prefix_length exitbb.bb_instructions = 0 ==>
  ?t Gf tnf cv ds.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    RTC (\u v. ?i. ctor_segment_fetch func u = SOME i /\
                   sa.cs_next_id <= i.inst_id /\ i.inst_id < sb.cs_next_id /\
                   i.inst_opcode <> INVOKE /\ ctor_segment_next func u i = SOME v) s t /\
    toplevel_copy_inv cv ds dst src loc a b n s G tn n Gf tnf t /\
    (!x. not_fresh_at sa x ==> ~MEM x ds) /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all toplevel_copy_compile_blocks >> strip_tac >>
  drule_all toplevel_copy_layout_freshness >> strip_tac >>
  drule_all toplevel_copy_layout_lookups >> strip_tac >>
  drule_all toplevel_copy_compile_exit >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_blocks sa sb =
    [<|bb_label := loop_body; bb_instructions := body_code|>;
     <|bb_label := hdr; bb_instructions := hdr_code|>;
     <|bb_label := initial; bb_instructions := init_code|>]` >>
  qabbrev_tac `ds = [cv;tv;sv;vv;mv;dv;nv]` >>
  qmatch_goalsub_abbrev_tac `RTC B` >>
  `MEM cv ds /\ dst <> cv /\ (!x. src = Var x ==> x <> cv)` by
    (fs[Abbr `ds`] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   DROP s.vs_inst_idx bb.bb_instructions =
     [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [cv];
      mk_inst (sa.cs_next_id+1) JMP [Label hdr] []]` by simp[] >>
  `phi_prefix_length hdr_code = 0 /\ phi_prefix_length body_code = 0` by
    simp[Abbr `hdr_code`, Abbr `body_code`, phi_prefix_length_def, mk_inst_def] >>
  `?t G1 tn1. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1) /\
      RTC B s t /\ toplevel_copy_inv cv ds dst src loc a b n s G tn 0 G1 tn1 t /\
      allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    (qpat_assum `Abbrev (B = _)`
       (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     `sa.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id+1 < sb.cs_next_id` by simp[] >>
     `phi_prefix_length <|bb_label := hdr; bb_instructions := hdr_code|>.bb_instructions = 0` by simp[] >>
     drule_all slot_init_origin_band >>
     disch_then (qspecl_then [`loc`,`D`,`explicit`,`PG`] strip_assume_tac) >>
     qexistsl_tac [`t`,`G1`,`tn1`] >> fs[Abbr `B`]) >>
  qabbrev_tac `Inv = \j Gj tj q. toplevel_copy_inv cv ds dst src loc a b n s G tn j Gj tj q /\
      allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\ RTC B s q` >>
  `!j Gj tj q. j <= n /\ Inv j Gj tj q /\ ~q.vs_halted /\
      q.vs_current_bb = hdr /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) [] (OK r,Gr,tr) /\
      Inv j Gr tr r /\ ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if j=n then sb.cs_current_bb else loop_body)` by
    (qunabbrev_tac `Inv` >> BETA_TAC >> rpt strip_tac >>
     `cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds` by
       (fs[Abbr `ds`] >> metis_tac[]) >>
     `isPREFIX [mk_inst (sa.cs_next_id+2) EQ [Var cv;Lit (n2w n)] [tv];
        mk_inst ((sa.cs_next_id+2)+1) JNZ [Var tv;Label sb.cs_current_bb;Label loop_body] []]
        (DROP q.vs_inst_idx
          <|bb_label := hdr; bb_instructions := hdr_code|>.bb_instructions)` by
       simp[Abbr `hdr_code`] >>
     `lookup_block q.vs_current_bb func.fn_blocks =
        SOME <|bb_label := hdr; bb_instructions := hdr_code|>` by metis_tac[] >>
     `?target. lookup_block (if j=n then sb.cs_current_bb else loop_body) func.fn_blocks =
        SOME target /\ phi_prefix_length target.bb_instructions = 0` by
       (Cases_on `j=n`
        >- (qexists_tac `exitbb` >> gvs[]) >>
        qexists_tac `<|bb_label := loop_body; bb_instructions := body_code|>` >> gvs[]) >>
     `sa.cs_next_id <= sa.cs_next_id+2 /\ (sa.cs_next_id+2)+1 < sb.cs_next_id` by simp[] >>
     drule_all (Q.INST [`s` |-> `q`, `loId` |-> `sa.cs_next_id`,
                        `hiId` |-> `sb.cs_next_id`] slot_header_origin_band) >>
     disch_then (qspecl_then [`D`,`explicit`,`PG`]
       (qx_choosel_then [`r`,`Gr`,`tr`] strip_assume_tac)) >>
     qexistsl_tac [`r`,`Gr`,`tr`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     irule RTC_TRANS >> qexists_tac `q` >> fs[Abbr `B`]) >>
  `!j Gj tj q. j < n /\ Inv j Gj tj q /\ ~q.vs_halted /\
      q.vs_current_bb = loop_body /\ q.vs_inst_idx = 0 ==>
     ?r Gr tr. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q,Gj,tj) [] (OK r,Gr,tr) /\
      Inv (j+1) Gr tr r /\ ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by
    (qunabbrev_tac `Inv` >> BETA_TAC >> rpt strip_tac >>
     `ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
      EVERY (\x. MEM x ds) [cv;sv;vv;mv;dv;nv] /\
      ~MEM dst [cv;sv;vv;mv;dv;nv] /\
      (!x. src = Var x ==> ~MEM x [cv;sv;vv;mv;dv;nv])` by
       (qpat_x_assum `ALL_DISTINCT ds` mp_tac >>
        qpat_x_assum `~MEM dst ds` mp_tac >>
        qpat_x_assum `!x. src = Var x ==> ~MEM x ds` mp_tac >>
        qunabbrev_tac `ds` >> POP_ASSUM_LIST (K ALL_TAC) >>
        simp[ALL_DISTINCT] >> metis_tac[]) >>
     `lookup_block q.vs_current_bb func.fn_blocks = SOME
        <|bb_label := q.vs_current_bb; bb_instructions :=
          [mk_inst (sa.cs_next_id+4) ADD [src;Var cv] [sv];
           mk_inst ((sa.cs_next_id+4)+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
           mk_inst ((sa.cs_next_id+4)+2) MUL [Var cv;Lit 32w] [mv];
           mk_inst ((sa.cs_next_id+4)+3) ADD [Var dst;Var mv] [dv];
           mk_inst ((sa.cs_next_id+4)+4) MSTORE [Var dv;Var vv] [];
           mk_inst ((sa.cs_next_id+4)+5) ADD [Var cv;Lit 1w] [nv];
           mk_inst ((sa.cs_next_id+4)+6) ASSIGN [Var nv] [cv];
           mk_inst ((sa.cs_next_id+4)+7) JMP [Label hdr] []]|>` by
       gvs[Abbr `body_code`, ADD_ASSOC] >>
     `sa.cs_next_id <= sa.cs_next_id+4 /\ (sa.cs_next_id+4)+7 < sb.cs_next_id` by simp[] >>
     `phi_prefix_length <|bb_label := hdr; bb_instructions := hdr_code|>.bb_instructions = 0` by simp[] >>
     drule_all (Q.INST [`s` |-> `q`, `loId` |-> `sa.cs_next_id`,
                        `hiId` |-> `sb.cs_next_id`] slot_body_origin_band) >>
     disch_then (qspecl_then [`D`,`explicit`,`PG`]
       (qx_choosel_then [`r`,`Gr`,`tr`] strip_assume_tac)) >>
     qexistsl_tac [`r`,`Gr`,`tr`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     irule RTC_TRANS >> qexists_tac `q` >> fs[Abbr `B`]) >>
  qspecl_then [`Inv`, `(D,lo,explicit,ctx,func,PG)`, `n`, `hdr`, `loop_body`,
               `sb.cs_current_bb`, `n`, `0`, `G1`, `tn1`, `t`]
    mp_tac copy_loop_iterate_origin_ptr >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >>
                qunabbrev_tac `Inv` >> BETA_TAC >>
                rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then (qx_choosel_then [`t2`,`Gf`,`tnf`] strip_assume_tac) >>
  qexistsl_tac [`t2`,`Gf`,`tnf`,`cv`,`ds`] >> fs[Abbr `Inv`] >>
  slot_origin_continue `gas_origin_ptr_path _ (s,G,tn) [] (OK t,G1,tn1)` >> simp[]
QED
