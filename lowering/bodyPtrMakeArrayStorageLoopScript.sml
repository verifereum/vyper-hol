(* Control-edge transport and counted CFG iteration for storage copies. *)
Theory bodyPtrMakeArrayStorageLoop
Ancestors
  bodyPtrMakeArrayStorageSuccessor bodyPtrMakeArrayStorageEndpoints
  bodyPtrMakeArrayStorageControl exprSimStorageCopy ptrDiscipline
  bodyPtrDefs venomState finite_map pred_set words ifJumpPtr emitHelperProps fragGasPathPtr

Theorem storage_loop_test_inv:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s /\
  tv IN writes /\ tv <> cv /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) ==>
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (jump_to lbl (update_var tv w s))
Proof
  strip_tac >>
  `dst <> tv /\ (!x. src = Var x ==> x <> tv)` by metis_tac[] >>
  `copy_prefix loc a b n sbase k (jump_to lbl (update_var tv w s))` by
    (simp[copy_prefix_jump, copy_prefix_update_var] >>
     metis_tac[storage_body_inv_prefix]) >>
  Cases_on `src` >>
  gvs[storage_body_inv_def, storage_body_frame_def, ptr_covers_def,
    copy_static_def, jump_to_def, update_var_def, lookup_var_def,
    op_prov_def, op_taint_def, eval_operand_def, FLOOKUP_DRESTRICT,
    FLOOKUP_UPDATE, allocas_from_def] >> metis_tac[]
QED

Theorem storage_loop_jump_inv:
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn (jump_to lbl s)
Proof
  Cases_on `src` >> strip_tac >>
  gvs[storage_body_inv_def, storage_body_frame_def, copy_prefix_def, copy_static_def,
    jump_to_def, lookup_var_def, eval_operand_def, ptr_covers_def,
    allocas_from_def] >> metis_tac[]
QED

Theorem storage_loop_header:
  same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
  emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
  emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
  fn_has_code sth stj fn /\ fn_has_code stj st2 fn /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sth.cs_current_bb /\
  s.vs_inst_idx = LENGTH sth.cs_current_insts /\
  tv IN writes /\ tv <> cv /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) /\
  k <= n /\ n < dimword(:256) /\
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  ?t H tm.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k H tm t /\
    t.vs_current_bb = (if k = n then exit else loop_body) /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  `~s.vs_halted /\ lookup_var cv s = SOME (n2w k) /\ op_taint tn (Var cv) = {}` by
    gvs[storage_body_inv_def] >>
  drule_all storage_control_header >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qexistsl_tac [`jump_to (if k = n then exit else loop_body)
    (update_var tv (bool_to_word (k = n)) s)`,
    `DRESTRICT G (COMPL {tv})`, `tn with t_var := tn.t_var |+ (tv,{})`] >>
  simp[] >> conj_tac >- (irule storage_loop_test_inv >> metis_tac[]) >>
  simp[jump_to_def]
QED

Theorem storage_loop_backedge:
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\ fn_has_code ste st3 fn /\
  ~ctx_has_dalloca ctx /\ s.vs_current_bb = ste.cs_current_bb /\
  s.vs_inst_idx = LENGTH ste.cs_current_insts /\
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to hdr s)) /\
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn (jump_to hdr s)
Proof
  strip_tac >> conj_tac
  >- (drule emit_inst_extends >> strip_tac >>
      irule if_emit_jump_zero_path_ptr >>
      simp[] >> conj_tac >- gvs[storage_body_inv_def] >>
      qexistsl_tac [`ste`, `st3`] >> simp[]) >>
  irule storage_loop_jump_inv >> simp[]
QED

(* The quantified body boundary is instantiated once with the installed seven
   instructions and the backedge. It keeps compiler layout out of induction. *)
Theorem storage_loop_iterate:
  same_blocks sth stj /\ isPREFIX sth.cs_current_insts stj.cs_current_insts /\
  emitted_insts sth stj = [mk_inst sth.cs_next_id EQ [Var cv; Lit (n2w n)] [tv]] /\
  emit_inst JNZ [Var tv; Label exit; Label loop_body] [] stj = ((),st2) /\
  fn_has_code sth stj fn /\ fn_has_code stj st2 fn /\
  sth.cs_current_bb = hdr /\ sth.cs_current_insts = [] /\
  ~ctx_has_dalloca ctx /\ tv IN writes /\ tv <> cv /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) /\ n < dimword(:256) /\
  (!j H tm t.
    j < n /\ t.vs_current_bb = loop_body /\ t.vs_inst_idx = 0 /\
    storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase j H tm t ==>
    ?u J tu. gas_path_ptr D 0 ctx fn PG H tm t 0 J tu (OK u) /\
      storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase (j+1) J tu u /\
      u.vs_current_bb = hdr /\ u.vs_inst_idx = 0) ==>
  !k G tn s.
    k <= n /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
    storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
    ?u H tm. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u) /\
      storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase n H tm u /\
      u.vs_current_bb = exit /\ u.vs_inst_idx = 0
Proof
  strip_tac >> completeInduct_on `n-k` >> rpt strip_tac >>
  `s.vs_current_bb = sth.cs_current_bb /\
   s.vs_inst_idx = LENGTH sth.cs_current_insts` by simp[] >>
  drule_all storage_loop_header >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `tm` strip_assume_tac)))) >>
  Cases_on `k = n`
  >- (qexistsl_tac [`t`, `H`, `tm`] >> gvs[]) >>
  `k < n` by decide_tac >>
  qpat_assum `!j H tm t. _` (qspecl_then [`k`, `H`, `tm`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `J` (qx_choose_then `tu` strip_assume_tac))) >>
  suspend "induction"
QED
Resume storage_loop_iterate[induction]:
  `n - (k+1) < v` by decide_tac >>
  qpat_x_assum `!m. m < v ==> _` (qspec_then `n-(k+1)` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`n`, `k+1`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`J`, `tu`, `u`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `sf` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac))) >>
  qexistsl_tac [`sf`, `Gf`, `tf`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`H`, `t`, `tm`] >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`J`, `u`, `tu`] >> simp[]
QED
Finalise storage_loop_iterate

Theorem storage_loop_body_backedge:
  (loc = LocStorage \/ loc = LocTransient) /\ ~ctx_has_dalloca ctx /\
  lookup_block loop_body fn.fn_blocks = SOME bb /\
  (!j. j < 7 ==> get_instruction bb j = SOME (EL j
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+3) ADD [Var dst;Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv]])) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\ fn_has_code ste st3 fn /\
  ste.cs_current_bb = loop_body /\ LENGTH ste.cs_current_insts = 7 /\
  ALL_DISTINCT [cv;sv;vv;mv;dv;nv] /\
  {cv;sv;vv;mv;dv;nv} SUBSET writes /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) /\
  k < n /\ b+32*n < dimword(:256) /\
  s.vs_current_bb = loop_body /\ s.vs_inst_idx = 0 /\
  storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase k G tn s ==>
  ?u H tm. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK u) /\
    storage_body_inv src dst cv writes loc a b n Gbase tnbase sbase (k+1) H tm u /\
    u.vs_current_bb = hdr /\ u.vs_inst_idx = 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `get_instruction bb 0 = SOME (mk_inst id ADD [src;Var cv] [sv]) /\
   get_instruction bb 1 = SOME
     (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
   get_instruction bb 2 = SOME (mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]) /\
   get_instruction bb 3 = SOME (mk_inst (id+3) ADD [Var dst;Var mv] [dv]) /\
   get_instruction bb 4 = SOME (mk_inst (id+4) MSTORE [Var dv;Var vv] []) /\
   get_instruction bb 5 = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
   get_instruction bb 6 = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv])` by
    simp[] >>
  suspend "successor"
QED
Resume storage_loop_body_backedge[successor]:
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME (mk_inst id ADD [src;Var cv] [sv]) /\
   get_instruction bb (SUC s.vs_inst_idx) = SOME
     (mk_inst (id+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
   get_instruction bb (s.vs_inst_idx+2) = SOME (mk_inst (id+2) MUL [Var cv;Lit 32w] [mv]) /\
   get_instruction bb (s.vs_inst_idx+3) = SOME (mk_inst (id+3) ADD [Var dst;Var mv] [dv]) /\
   get_instruction bb (s.vs_inst_idx+4) = SOME (mk_inst (id+4) MSTORE [Var dv;Var vv] []) /\
   get_instruction bb (s.vs_inst_idx+5) = SOME (mk_inst (id+5) ADD [Var cv;Lit 1w] [nv]) /\
   get_instruction bb (s.vs_inst_idx+6) = SOME (mk_inst (id+6) ASSIGN [Var nv] [cv])` by simp[] >>
  drule_all storage_copy_body_ptr_successor >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `t` (qx_choose_then `H` (qx_choose_then `tm` strip_assume_tac)))) >>
  `t.vs_current_bb = ste.cs_current_bb /\
   t.vs_inst_idx = LENGTH ste.cs_current_insts` by simp[] >>
  drule_all storage_loop_backedge >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`jump_to hdr t`, `H`, `tm`] >>
  simp[jump_to_def] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`H`, `t`, `tm`] >> gvs[jump_to_def]
QED
Finalise storage_loop_body_backedge

Theorem storage_loop_init_inv:
  cv IN writes /\ dst NOTIN writes /\
  (!x. src = Var x ==> x NOTIN writes) /\
  eval_operand src s = SOME a /\ op_prov G src = NONE /\ op_taint tn src = {} /\
  lookup_var dst s = SOME (n2w b) /\ ptr_covers G tn dst s (32*n) /\
  allocas_from 0 s /\ ~s.vs_halted ==>
  storage_body_inv src dst cv writes loc a b n G tn s 0
    (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
    (jump_to hdr (update_var cv 0w s))
Proof
  strip_tac >>
  `dst <> cv /\ (!x. src = Var x ==> x <> cv)` by metis_tac[] >>
  `copy_prefix loc a b n s 0 (jump_to hdr (update_var cv 0w s))` by
    simp[copy_prefix_jump, copy_prefix_update_var, copy_prefix_zero] >>
  `storage_body_frame writes G tn s (DRESTRICT G (COMPL {cv}))
     (tn with t_var := tn.t_var |+ (cv,{})) (jump_to hdr (update_var cv 0w s))` by
    (simp[storage_body_frame_def, copy_static_def, jump_to_def, update_var_def,
      lookup_var_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
      FLOOKUP_UPDATE] >> metis_tac[]) >>
  `ptr_covers (DRESTRICT G (COMPL {cv})) (tn with t_var := tn.t_var |+ (cv,{}))
     dst (jump_to hdr (update_var cv 0w s)) (32*n)` by
    (irule storage_body_frame_covers >> metis_tac[]) >>
  `eval_operand src (jump_to hdr (update_var cv 0w s)) = SOME a /\
   op_prov (DRESTRICT G (COMPL {cv})) src = NONE /\
   op_taint (tn with t_var := tn.t_var |+ (cv,{})) src = {}` by
    (drule storage_body_frame_operand >> disch_then (qspec_then `src` mp_tac) >> simp[]) >>
  simp[storage_body_inv_def, jump_to_def, update_var_def, lookup_var_def,
    FLOOKUP_UPDATE, op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, allocas_from_def] >>
  gvs[lookup_var_def]
QED
