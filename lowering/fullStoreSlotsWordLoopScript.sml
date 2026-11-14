(* Runtime-count memory-to-slot loops with uniform joint endpoints. *)
Theory fullStoreSlotsWordLoop
Ancestors
  fullStoreSlotsWordCode fullStoreSlotsWordBody fullStoreSlotsUniformLoop
  placeStoreCopyPath fragGasCopyLoop fragGasSeqAbort bodyMemAssignTopCopyPaths
  codegenRel ptrDiscipline bodyPtrDefs memSafeRun venomState venomInst venomExecSemantics
  words finite_map pred_set list rich_list arithmetic

Theorem store_slots_word_init:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv];
    mk_inst (id+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!y. not_fresh_at sa y ==> y <> cv) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k s 0 u /\
    eval_operand (Var cv) u = SOME 0w /\ op_prov Gf (Var cv) = NONE /\
    op_taint tnf (Var cv) = {} /\ allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
       op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  `get_instruction bb (s.vs_inst_idx+1) =
     SOME (mk_inst (id+1) JMP [Label hdr] [])` by gvs[ADD1] >>
  drule_all copy_init_origin_ptr >>
  simp[step_prov_def,out_prov_def,first_prov_def,op_prov_def,set_prov_def,
    step_taint_def,set_var_taint_def,out_taint_def,mem_taint_def,
    imm_taint_def,store_taint_def,adopt_reset_def,step_writes_def,
    source_memory_write_ranges_def,written_taint_def,range_bytes_def,
    new_site_bytes_def,eval_operand_def,mk_inst_def,update_var_def,
    op_taint_def,FLOOKUP_DEF,SF CONJ_ss,taint_component_equality] >> strip_tac >>
  qexistsl_tac [`jump_to hdr (update_var cv 0w s with vs_inst_idx := s.vs_inst_idx+1)`,
    `DRESTRICT G (COMPL {cv})`,
    `<|t_mem := tn.t_mem; t_var := tn.t_var |+ (cv,{});
       t_stor := tn.t_stor; t_trans := tn.t_trans; t_imm := tn.t_imm|>`] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- (simp[] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
  simp[jump_to_def,update_var_def,eval_operand_def,lookup_var_def,
    FLOOKUP_UPDATE,op_prov_def,op_taint_def,FLOOKUP_DRESTRICT] >>
  gvs[allocas_from_def,FDOM_DRESTRICT,DRESTRICT_DEF,FAPPLY_FUPDATE_THM] >>
  metis_tac[]
QED

Theorem store_slots_word_header_frame:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv;cnt] [tv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var tv;Label yes;Label no] []) /\
  eval_operand (Var cv) s = SOME (n2w j) /\ eval_operand cnt s = SOME (n2w n) /\
  op_taint tn (Var cv) = {} /\ op_taint tn cnt = {} /\
  op_prov G (Var cv) = NONE /\ op_prov G cnt = NONE /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ (!y. not_fresh_at sa y ==> y <> tv) /\
  store_copy_frame sa loc b k sbase j s /\ j <= n /\ n < dimword (:256) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k sbase j u /\
    eval_operand (Var cv) u = SOME (n2w j) /\
    op_prov Gf (Var cv) = NONE /\ op_taint tnf (Var cv) = {} /\
    allocas_from lo u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if j=n then yes else no) /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans
Proof
  strip_tac >>
  drule_all store_slots_word_header_origin_ptr >>
  `((n2w j):bytes32 = n2w n) <=> j=n` by simp[n2w_11,LESS_MOD] >>
  simp[] >> strip_tac >>
  qexistsl [`jump_to (if j=n then yes else no)
    (update_var tv (bool_to_word (j=n)) s with vs_inst_idx := SUC s.vs_inst_idx)`,
    `DRESTRICT G (COMPL {tv})`, `tn with t_var := tn.t_var |+ (tv,{})`] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[] >> irule topcopy_frame_update >> simp[] >> metis_tac[]) >>
  gvs[jump_to_def,update_var_def,eval_operand_def,lookup_var_def,
    FLOOKUP_UPDATE,op_prov_def,op_taint_def,FLOOKUP_DRESTRICT,allocas_from_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `y <> tv` by metis_tac[] >> simp[]
QED


Theorem store_slots_word_init_invariant:
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id ASSIGN [Lit 0w] [cv];
    mk_inst (id+1) JMP [Label hdr] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  (!y. not_fresh_at sa y ==> y <> cv) ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    (\j Gj tj q.
      store_copy_frame sa loc b k s j q /\
      eval_operand (Var cv) q = SOME (n2w j) /\
      op_taint tj (Var cv) = {} /\ op_prov Gj (Var cv) = NONE /\
      allocas_from lo q /\
      (!y. not_fresh_at sa y ==> FLOOKUP Gj y = FLOOKUP G y /\
        op_taint tj (Var y) = op_taint tn (Var y)) /\
      tj.t_mem = tn.t_mem /\ tj.t_imm = tn.t_imm /\
      (if loc = LocStorage then tj.t_trans = tn.t_trans else tj.t_stor = tn.t_stor) /\
      toplevel_copy_source_taint loc tj =
        FOLDL (\ta i. key_update ta (k+n2w i)
          (mem_word_taint tn.t_mem (w2n b+32*i)))
          (toplevel_copy_source_taint loc tn) (GENLIST I j)) 0 Gf tf u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0
Proof
  strip_tac >>
  `?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    store_copy_frame sa loc b k s 0 u /\
    eval_operand (Var cv) u = SOME 0w /\ op_prov Gf (Var cv) = NONE /\
    op_taint tf (Var cv) = {} /\ allocas_from lo u /\ ~u.vs_halted /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tf (Var y) = op_taint tn (Var y)) /\
    tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm` by
    (irule store_slots_word_init >>
     simp[Excl "isPREFIX"] >> conj_tac >- metis_tac[] >>
     qexists_tac `id` >> simp[Excl "isPREFIX"]) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >>
  simp[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def]
QED

Theorem store_slots_word_header_invariant:
  Inv = (\i Gi ti q.
    store_copy_frame sa loc b k sbase i q /\
    eval_operand (Var cv) q = SOME (n2w i) /\
    op_taint ti (Var cv) = {} /\ op_prov Gi (Var cv) = NONE /\
    allocas_from lo q /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gi y = FLOOKUP Gbase y /\
      op_taint ti (Var y) = op_taint tbase (Var y)) /\
    ti.t_mem = tbase.t_mem /\ ti.t_imm = tbase.t_imm /\
    (if loc = LocStorage then ti.t_trans = tbase.t_trans else ti.t_stor = tbase.t_stor) /\
    toplevel_copy_source_taint loc ti =
      FOLDL (\ta ii. key_update ta (k+n2w ii)
        (mem_word_taint tbase.t_mem (w2n b+32*ii)))
        (toplevel_copy_source_taint loc tbase) (GENLIST I i)) /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv;cnt] [tv]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst jid JNZ [Var tv;Label yes;Label no] []) /\
  eval_operand cnt s = SOME (n2w n) /\ op_taint tn cnt = {} /\
  op_prov G cnt = NONE /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  cv <> tv /\ (!y. not_fresh_at sa y ==> y <> tv) /\
  Inv j G tn s /\ j <= n /\ n < dimword(:256) ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    Inv j Gf tf u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = (if j=n then yes else no)
Proof
  strip_tac >> gvs[] >>
  drule_all (SRULE [] store_slots_word_header_frame) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> simp[] >>
  gvs[exprSimPtrTopLevelStorageCopyTheory.toplevel_copy_source_taint_def] >>
  metis_tac[]
QED

Theorem store_slots_word_body_invariant:
  Inv = (\i Gi ti q.
    store_copy_frame sa loc b k sbase i q /\
    eval_operand (Var cv) q = SOME (n2w i) /\
    op_taint ti (Var cv) = {} /\ op_prov Gi (Var cv) = NONE /\
    allocas_from lo q /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gi y = FLOOKUP Gbase y /\
      op_taint ti (Var y) = op_taint tbase (Var y)) /\
    ti.t_mem = tbase.t_mem /\ ti.t_imm = tbase.t_imm /\
    (if loc = LocStorage then ti.t_trans = tbase.t_trans else ti.t_stor = tbase.t_stor) /\
    toplevel_copy_source_taint loc ti =
      FOLDL (\ta ii. key_update ta (k+n2w ii)
        (mem_word_taint tbase.t_mem (w2n b+32*ii)))
        (toplevel_copy_source_taint loc tbase) (GENLIST I i)) /\
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  eval_operand (Var x) sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ op_taint tn dst = {} /\
  j < n /\ w2n b + 32*n < dimword (:256) /\
  w2n b + 32*n <= sbase.vs_alloca_next /\
  ~sbase.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  code = [mk_inst id MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+1) ADD [Var x;Var mv] [sv];
    mk_inst (id+2) MLOAD [Var sv] [vv];
    mk_inst (id+3) ADD [dst;Var cv] [dv];
    mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx + LENGTH code) =
    SOME (mk_inst (id+7) JMP [Label hdr] []) /\ Inv j G tn s ==>
  ?u Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tf)) /\
    Inv (j+1) Gf tf u /\ ~u.vs_halted /\ u.vs_inst_idx = 0 /\
    u.vs_current_bb = hdr
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Inv = _` SUBST_ALL_TAC >>
  qpat_x_assum `(\i Gi ti q. _) j G tn s`
    (strip_assume_tac o BETA_RULE) >>
  drule_all store_slots_word_body_scalar_origin_ptr >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  qexistsl_tac [`u`,`Gf`,`tf`] >> fs[ADD1,Excl "isPREFIX"] >>
  gvs[Excl "isPREFIX", GSYM ADD1, GENLIST, FOLDL_SNOC] >> metis_tac[]
QED

Theorem memory_copy_loop_op_origin_ptr_exact:
  compile_word_copy_loop_op (Var x) dst cnt LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc=LocStorage \/ loc=LocTransient) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst=Var y \/ cnt=Var y ==> not_fresh_at sa y) /\
  lookup_var x s=SOME b /\ ptr_covers G tn x s (32*n) /\
  eval_operand dst s=SOME k /\ op_taint tn dst={} /\
  eval_operand cnt s=SOME (n2w n) /\ op_taint tn cnt={} /\ op_prov G cnt=NONE /\
  n<dimword(:256) /\ w2n b+32*n<dimword(:256) /\
  w2n b+32*n<=s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb=sa.cs_current_bb /\ s.vs_inst_idx=LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
    t.vs_current_bb=sb.cs_current_bb /\ t.vs_inst_idx=LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y=FLOOKUP G y /\
      op_taint tnf (Var y)=op_taint tn (Var y)) /\
    tnf.t_mem=tn.t_mem /\ tnf.t_imm=tn.t_imm /\
    (if loc=LocStorage then tnf.t_trans=tn.t_trans else tnf.t_stor=tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      FOLDL (\ta i. key_update ta (k+n2w i)
        (mem_word_taint tn.t_mem (w2n b+32*i)))
        (toplevel_copy_source_taint loc tn) (GENLIST I n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  qabbrev_tac `Inv = \i Gi ti q.
    store_copy_frame sa loc b k s i q /\
    eval_operand (Var cv) q=SOME (n2w i) /\
    op_taint ti (Var cv)={} /\ op_prov Gi (Var cv)=NONE /\
    allocas_from lo q /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gi y=FLOOKUP G y /\
      op_taint ti (Var y)=op_taint tn (Var y)) /\
    ti.t_mem=tn.t_mem /\ ti.t_imm=tn.t_imm /\
    (if loc=LocStorage then ti.t_trans=tn.t_trans else ti.t_stor=tn.t_stor) /\
    toplevel_copy_source_taint loc ti =
      FOLDL (\ta ii. key_update ta (k+n2w ii)
        (mem_word_taint tn.t_mem (w2n b+32*ii)))
        (toplevel_copy_source_taint loc tn) (GENLIST I i)` >>
  `?q G1 t1.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK q,G1,t1)) /\ Inv 0 G1 t1 q /\
    ~q.vs_halted /\ q.vs_current_bb=hdr /\ q.vs_inst_idx=0` by
    (qunabbrev_tac `Inv` >> irule store_slots_word_init_invariant >>
     simp[Excl "isPREFIX"] >>
     conj_tac >- (qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
       simp[] >> metis_tac[]) >> qexists_tac `id0` >> asm_rewrite_tac[]) >>
  suspend "iterate"
QED

Resume memory_copy_loop_op_origin_ptr_exact[iterate]:
  `!j Gj tj r. j<=n /\ Inv j Gj tj r /\ ~r.vs_halted /\
    r.vs_current_bb=hdr /\ r.vs_inst_idx=0 ==>
    ?z Gz tz. (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (r,Gj,tj) [] (OK z,Gz,tz)) /\ Inv j Gz tz z /\ ~z.vs_halted /\
      z.vs_inst_idx=0 /\ z.vs_current_bb=(if j=n then exit else body_lbl)` by
    suspend "header" >>
  `!j Gj tj r. j<n /\ Inv j Gj tj r /\ ~r.vs_halted /\
    r.vs_current_bb=body_lbl /\ r.vs_inst_idx=0 ==>
    ?z Gz tz. (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (r,Gj,tj) [] (OK z,Gz,tz)) /\ Inv (j+1) Gz tz z /\ ~z.vs_halted /\
      z.vs_current_bb=hdr /\ z.vs_inst_idx=0` by suspend "body" >>
  `?t Gf tf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (q,G1,t1) [] (OK t,Gf,tf)) /\ Inv n Gf tf t /\ ~t.vs_halted /\
    t.vs_current_bb=exit /\ t.vs_inst_idx=0` by
    (irule store_slots_uniform_loop_iterate >>
     asm_rewrite_tac[] >> conj_tac
     >- (qexistsl_tac [`body_lbl`,`hdr`] >> asm_rewrite_tac[]) >>
     qexistsl_tac [`0`,`n`] >> simp[]) >>
  qexistsl_tac [`t`,`Gf`,`tf`] >>
  conj_tac >- metis_tac[origin_ptr_path_then] >>
  qpat_x_assum `Inv n Gf tf t` mp_tac >> simp[Abbr `Inv`]
QED

Resume memory_copy_loop_op_origin_ptr_exact[header]:
  rpt gen_tac >> strip_tac >>
  `eval_operand cnt r=SOME(n2w n) /\ op_taint tj cnt={} /\ op_prov Gj cnt=NONE` by
    (qpat_x_assum `Inv j Gj tj r` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
     `eval_operand cnt r=SOME(n2w n)` by
       (irule topcopy_frame_operand >> metis_tac[]) >>
     Cases_on `cnt` >> gvs[op_taint_def,op_prov_def]) >>
  `isPREFIX [mk_inst idh EQ [Var cv;cnt] [tv];
    mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] []]
    (DROP 0 bbh.bb_instructions)` by asm_rewrite_tac[DROP_0] >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `cv <> tv /\ (!y. not_fresh_at sa y ==> y <> tv)` by
    (qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >>
     fs[] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (Inv = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at (Pat `Inv = _`) store_slots_word_header_invariant >>
  disch_then (drule_at (Pat `Inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[Excl "isPREFIX"] >> disch_then irule >> simp[Excl "isPREFIX"] >>
  qexistsl_tac [`idh`,`idh+1`,`tv`] >> simp[] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `get_instruction bbh (SUC 0) = _` mp_tac >> simp[]
QED

Resume memory_copy_loop_op_origin_ptr_exact[body]:
  rpt gen_tac >> strip_tac >>
  `ptr_covers Gj tj x r (32*n) /\ op_taint tj dst={}` by
    (qpat_assum `Inv j Gj tj r` mp_tac >> qunabbrev_tac `Inv` >>
     disch_then (strip_assume_tac o BETA_RULE) >>
     `eval_operand (Var x) r=SOME b` by
       (irule topcopy_frame_operand >> simp[eval_operand_def] >> metis_tac[]) >>
     conj_tac >- (gvs[ptr_covers_def,eval_operand_def,Excl "isPREFIX"] >> metis_tac[]) >>
     Cases_on `dst` >> gvs[op_taint_def] >> metis_tac[]) >>
  qpat_x_assum `Abbrev (Inv = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at (Pat `Inv = _`) store_slots_word_body_invariant >>
  disch_then (drule_at (Pat `Inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[eval_operand_def,Excl "isPREFIX"] >>
  CONV_TAC (RAND_CONV (STRIP_QUANT_CONV
    (RAND_CONV (RAND_CONV (RAND_CONV (REWR_CONV CONJ_COMM)))))) >>
  disch_then irule >> simp[Excl "isPREFIX"] >>
  qexistsl_tac [`dst`,`dv`,`idb`,`mv`,`nv`,`sv`,`vv`] >>
  conj_tac >- (qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >> simp[]) >>
  qpat_x_assum `ALL_DISTINCT _` (strip_assume_tac o SRULE []) >>
  simp[Excl "isPREFIX"] >>
  qpat_x_assum `isPREFIX (_::_::_::_::_::_::_::_::_) bbb.bb_instructions`
    (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  asm_rewrite_tac[get_instruction_def,APPEND,LENGTH,EL] >> simp[]
QED

Finalise memory_copy_loop_op_origin_ptr_exact

Theorem store_slots_taint_fold_bound:
  !n. FOLDL (\ta i. key_update ta ((k:bytes32)+n2w i)
        (mem_word_taint M (c+32*i))) ta0 (GENLIST I n) SUBSET
    (ta0 DIFF {(k+n2w i,j) | (i,j) | i<n}) UNION
    {(k+n2w i,j) | i<n /\ j<32 /\ c+32*i+j IN M}
Proof
  Induct >- simp[] >>
  simp[GENLIST, FOLDL_SNOC] >>
  drule copy_store_taint_bound_step >> simp[ADD1]
QED

Theorem memory_copy_loop_op_origin_ptr:
  compile_word_copy_loop_op (Var x) dst cnt LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ (loc=LocStorage \/ loc=LocTransient) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ ~s.vs_call_ctx.cc_static /\
  not_fresh_at sa x /\ (!y. dst=Var y \/ cnt=Var y ==> not_fresh_at sa y) /\
  lookup_var x s=SOME b /\ ptr_covers G tn x s (32*n) /\
  eval_operand dst s=SOME k /\ op_taint tn dst={} /\
  eval_operand cnt s=SOME (n2w n) /\ op_taint tn cnt={} /\ op_prov G cnt=NONE /\
  n<dimword(:256) /\ w2n b+32*n<dimword(:256) /\
  w2n b+32*n<=s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb=sa.cs_current_bb /\ s.vs_inst_idx=LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf)) /\
    store_copy_frame sa loc b k s n t /\ ~t.vs_halted /\
    t.vs_current_bb=sb.cs_current_bb /\ t.vs_inst_idx=LENGTH sb.cs_current_insts /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y=FLOOKUP G y /\
      op_taint tnf (Var y)=op_taint tn (Var y)) /\
    tnf.t_mem=tn.t_mem /\ tnf.t_imm=tn.t_imm /\
    (if loc=LocStorage then tnf.t_trans=tn.t_trans else tnf.t_stor=tn.t_stor) /\
    toplevel_copy_source_taint loc tnf SUBSET
      toplevel_copy_source_taint loc tn DIFF {(k+n2w i,j) | (i,j) | i<n} UNION
      {(k+n2w i,j) | i<n /\ j<32 /\ w2n b+32*i+j IN tn.t_mem}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all memory_copy_loop_op_origin_ptr_exact >> strip_tac >>
  qexistsl [`t`,`Gf`,`tnf`] >> simp[] >>
  mp_tac (Q.INST [`c` |-> `w2n (b:bytes32)`, `M` |-> `tn.t_mem`,
    `ta0` |-> `toplevel_copy_source_taint loc tn`] store_slots_taint_fold_bound) >>
  simp[]
QED
