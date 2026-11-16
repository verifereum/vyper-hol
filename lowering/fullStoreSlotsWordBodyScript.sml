(* Uniform endpoints for the memory-to-slot loop body. *)
Theory fullStoreSlotsWordBody
Ancestors
  fragGasCopyLoop fragGasSeqPtr fragGasSeqPtrContext fragGasOriginPtrLoop ptrDiscipline bodyPtrDefs
  bodyMemAssignTopCopyPaths bodyMemAssignTopCopyLoop
  decoderGhostFramePtr finite_map pred_set
  venomInst venomExecSemantics venomState words list arithmetic

Theorem store_slots_scalar_update_suffix:
  !prefix s G tn Gf tnf.
    EVERY (\i. ~MEM cv i.inst_outputs) prefix /\
    op_prov G (Var cv) = NONE /\
    inst_seq_ptr D lo ctx func PG G tn
      (prefix ++ [mk_inst ai ADD [Var cv;Lit w] [nv];
                  mk_inst si ASSIGN [Var nv] [cv]]) s Gf tnf ==>
    op_prov Gf (Var cv) = NONE
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac
  >- (Cases_on `step_inst_base (mk_inst ai ADD [Var cv;Lit w] [nv]) s` >>
      gvs[] >>
      Cases_on `step_inst_base (mk_inst si ASSIGN [Var nv] [cv])
        (v with vs_inst_idx := SUC s.vs_inst_idx)` >>
      gvs[inst_seq_ptr_def] >>
      gvs[step_prov_def,out_prov_def,first_prov_def,set_prov_def,
        op_prov_def,mk_inst_def,FLOOKUP_DRESTRICT]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  simp[op_prov_def,step_prov_other_output] >> gvs[op_prov_def]
QED

Theorem store_slots_inst_seq_ghost_unique:
  !code s G tn H1 t1 H2 t2.
    EVERY (\i. i.inst_opcode <> PARAM) code /\
    inst_seq_ptr D1 lo ctx fn PG1 G tn code s H1 t1 /\
    inst_seq_ptr D2 lo ctx fn PG2 G tn code s H2 t2 ==>
    H1 = H2 /\ t1 = t2
Proof
  Induct >> simp[inst_seq_ptr_def] >> rpt gen_tac >> strip_tac >>
  `!u. step_prov PG1 G h u = step_prov PG2 G h u` by
    simp[step_prov_def,out_prov_def] >>
  Cases_on `step_inst_base h s` >> gvs[] >> metis_tac[]
QED

Theorem store_slots_word_body_ptr_uniform:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\ ~MEM x [cv;mv;sv;vv;dv;nv] /\
  (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ lookup_var x s = SOME b /\
  eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w j) /\ op_taint tn (Var cv) = {} /\
  j < n /\ w2n b + 32*n < dimword (:256) /\ ~s.vs_call_ctx.cc_static /\
  code = [mk_inst id MUL [Var cv;Lit 32w] [mv];
    mk_inst (id+1) ADD [Var x;Var mv] [sv];
    mk_inst (id+2) MLOAD [Var sv] [vv];
    mk_inst (id+3) ADD [dst;Var cv] [dv];
    mk_inst (id+4) (if loc = LocStorage then SSTORE else TSTORE) [Var dv;Var vv] [];
    mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
    mk_inst (id+6) ASSIGN [Var nv] [cv]] ==>
  ?Gf tnf.
    (!D PG. inst_seq_ptr D 0 ctx func PG G tn code s Gf tnf) /\
    op_taint tnf (Var cv) = {} /\
    (!y. ~MEM y [cv;mv;sv;vv;dv;nv] ==>
      FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      key_update (toplevel_copy_source_taint loc tn) (k+n2w j)
        (mem_word_taint tn.t_mem (w2n b+32*j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac memory_copy_body_ptr >>
  qpat_assum `!id D fn PG. _`
    (qspecl_then [`id`,`ARB`,`func`,`[]`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tnf`] >> reverse conj_tac >- simp[] >>
  rpt gen_tac >>
  qpat_x_assum `!id D fn PG. _`
    (qspecl_then [`id`,`D`,`func`,`PG`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> PARAM) code` by
    (simp[] >> Cases_on `loc = LocStorage` >> simp[mk_inst_def]) >>
  metis_tac[store_slots_inst_seq_ghost_unique]
QED

Theorem store_slots_body_jump_uniform:
  ~s.vs_halted /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
    i.inst_opcode <> DALLOCA) code /\
  run_inst_seq_mem_ok code s /\ run_inst_seq code s = OK t /\
  (!D PG. inst_seq_ptr D 0 ctx func PG G tn code s Gf tnf) /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
  get_instruction bb (s.vs_inst_idx + LENGTH code) =
    SOME (mk_inst id JMP [Label hdr] []) ==>
  (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to hdr (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)),Gf,tnf)) /\
  allocas_from lo t
Proof
  strip_tac >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (strip_tac >> irule run_inst_seq_allocas_below_fmp >>
     goal_assum (drule_at Any) >> gvs[EVERY_MEM]) >>
  `!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code),Gf,tnf) /\
     allocas_from lo t` by
    (rpt gen_tac >> irule run_inst_seq_origin_ptr_lift >>
     simp[] >> gvs[EVERY_MEM]) >>
  conj_tac >-
    (rpt gen_tac >> irule gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gf`,`t with vs_inst_idx := s.vs_inst_idx + LENGTH code`,`tnf`] >>
     conj_tac >- simp[] >>
     irule copy_jmp_origin_ptr >> simp[allocas_from_def] >>
     conj_tac >- (qexists_tac `id` >> metis_tac[ADD_COMM]) >>
     qpat_x_assum `!D explicit PG. _`
       (qspecl_then [`D`,`explicit`,`PG`] strip_assume_tac) >>
     gvs[allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem store_slots_word_body_origin_ptr_core:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  store_copy_frame sa loc b k sbase j s /\
  eval_operand (Var x) sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w j) /\ op_taint tn (Var cv) = {} /\
  j < n /\ w2n b + 32*n < dimword (:256) /\
  w2n b + 32*n <= sbase.vs_alloca_next /\
  ~sbase.vs_call_ctx.cc_static /\ ~s.vs_halted /\ allocas_from lo s /\
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
    SOME (mk_inst (id+7) JMP [Label hdr] []) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k sbase (SUC j) u /\
    eval_operand (Var cv) u = SOME (n2w (SUC j)) /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    allocas_from lo u /\ op_taint tnf (Var cv) = {} /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      key_update (toplevel_copy_source_taint loc tn) (k+n2w j)
        (mem_word_taint tn.t_mem (w2n b+32*j)) /\
    (op_prov G (Var cv) = NONE ==> op_prov Gf (Var cv) = NONE)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `eval_operand (Var x) s = SOME b /\ eval_operand dst s = SOME k` by
    (conj_tac >> irule topcopy_frame_operand >>
     qexistsl_tac [`b`,`j`,`k`,`loc`,`sa`,`sbase`] >> simp[]) >>
  `lookup_var x s = SOME b` by gvs[eval_operand_def] >>
  `~s.vs_call_ctx.cc_static` by metis_tac[topcopy_frame_call_ctx] >>
  `~MEM x [cv;mv;sv;vv;dv;nv] /\
   (!y. dst = Var y ==> ~MEM y [cv;mv;sv;vv;dv;nv])` by metis_tac[] >>
  drule_all store_slots_word_body_ptr_uniform >>
  disch_then (qspec_then `func` strip_assume_tac) >>
  `!y. Var x = Var y \/ dst = Var y ==> not_fresh_at sa y` by
    (rpt strip_tac >> gvs[]) >>
  drule_all topcopy_body_run >>
  disch_then (qspec_then `id` (qx_choose_then `t` strip_assume_tac)) >>
  `run_inst_seq code s = OK t` by gvs[] >>
  `op_prov G (Var cv) = NONE ==> op_prov Gf (Var cv) = NONE` by
    (strip_tac >>
     `inst_seq_ptr ARB 0 ctx func [] G tn
        (TAKE 5 code ++ [mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
          mk_inst (id+6) ASSIGN [Var nv] [cv]]) s Gf tnf` by
       (qpat_assum `!D PG. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
          (qspecl_then [`ARB`,`[]`] mp_tac) >> gvs[]) >>
     drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
       store_slots_scalar_update_suffix >>
     simp[] >> gvs[ALL_DISTINCT]) >>
  `w2n b + 32*(j+1) <= s.vs_alloca_next` by
    metis_tac[topcopy_frame_index_bound] >>
  `run_inst_seq_mem_ok code s` by
    (simp[] >> irule body_mem_storage_iteration_mem_ok_modular >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS /\
    ~is_alloca_op i.inst_opcode /\ i.inst_opcode <> SETFMP /\
    i.inst_opcode <> DALLOCA) code` by
    (simp[] >> Cases_on `loc = LocStorage` >> simp[mk_inst_def,is_terminator_def,is_alloca_op_def]) >>
  drule_all_then strip_assume_tac store_slots_body_jump_uniform >>
  qexistsl_tac [`jump_to hdr (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)`,
    `Gf`,`tnf`] >>
  simp[] >>
  gvs[jump_to_def,eval_operand_def,lookup_var_def,allocas_from_def] >>
  metis_tac[]
QED

Theorem store_slots_word_body_origin_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  store_copy_frame sa loc b k sbase j s /\
  eval_operand (Var x) sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w j) /\ op_taint tn (Var cv) = {} /\
  j < n /\ w2n b + 32*n < dimword (:256) /\
  w2n b + 32*n <= sbase.vs_alloca_next /\
  ~sbase.vs_call_ctx.cc_static /\ ~s.vs_halted /\ allocas_from lo s /\
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
    SOME (mk_inst (id+7) JMP [Label hdr] []) ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k sbase (SUC j) u /\
    eval_operand (Var cv) u = SOME (n2w (SUC j)) /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    allocas_from lo u /\ op_taint tnf (Var cv) = {} /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      key_update (toplevel_copy_source_taint loc tn) (k+n2w j)
        (mem_word_taint tn.t_mem (w2n b+32*j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all store_slots_word_body_origin_ptr_core >>
  strip_tac >> qexistsl [`u`,`Gf`,`tnf`] >> simp[]
QED

Theorem store_slots_word_body_scalar_origin_ptr:
  (loc = LocStorage \/ loc = LocTransient) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  store_copy_frame sa loc b k sbase j s /\
  eval_operand (Var x) sbase = SOME b /\ eval_operand dst sbase = SOME k /\
  not_fresh_at sa x /\ (!y. dst = Var y ==> not_fresh_at sa y) /\
  ALL_DISTINCT [cv;mv;sv;vv;dv;nv] /\
  (!y. not_fresh_at sa y ==> ~MEM y [cv;mv;sv;vv;dv;nv]) /\
  ptr_covers G tn x s (32*n) /\ op_taint tn dst = {} /\
  eval_operand (Var cv) s = SOME (n2w j) /\ op_taint tn (Var cv) = {} /\
  j < n /\ w2n b + 32*n < dimword (:256) /\
  w2n b + 32*n <= sbase.vs_alloca_next /\
  ~sbase.vs_call_ctx.cc_static /\ ~s.vs_halted /\ allocas_from lo s /\
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
    SOME (mk_inst (id+7) JMP [Label hdr] []) /\ op_prov G (Var cv) = NONE ==>
  ?u Gf tnf.
    (!D explicit PG. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK u,Gf,tnf)) /\
    store_copy_frame sa loc b k sbase (SUC j) u /\
    eval_operand (Var cv) u = SOME (n2w (SUC j)) /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    allocas_from lo u /\ op_taint tnf (Var cv) = {} /\
    (!y. not_fresh_at sa y ==> FLOOKUP Gf y = FLOOKUP G y /\
      op_taint tnf (Var y) = op_taint tn (Var y)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    (if loc = LocStorage then tnf.t_trans = tn.t_trans else tnf.t_stor = tn.t_stor) /\
    toplevel_copy_source_taint loc tnf =
      key_update (toplevel_copy_source_taint loc tn) (k+n2w j)
        (mem_word_taint tn.t_mem (w2n b+32*j)) /\ op_prov Gf (Var cv) = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all store_slots_word_body_origin_ptr_core >>
  strip_tac >> qexistsl [`u`,`Gf`,`tnf`] >> simp[]
QED
