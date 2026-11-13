(* Counted storage/transient copying: all observations refer to the endpoint
   selected by the checked path. *)
Theory storageCopyLoopPtr
Ancestors
  storageCopyBodyPtr storageCopyControlPtr exprSimStorageCopy normalizerAllocationFrame
  fragGasPathPtr bodyPtrDefs ptrDiscipline venomExecSemantics venomState venomInst
  finite_map list arithmetic words pred_set

Theorem storage_copy_header_frame:
  t = jump_to lbl (update_var tv w s) /\
  G' = DRESTRICT G (COMPL {tv}) /\
  tn' = (tn with t_var := tn.t_var |+ (tv,{})) /\
  root <> tv /\ src <> Var tv /\
  ptr_covers G tn root s span /\
  copy_prefix loc a b n sbase k s ==>
  copy_prefix loc a b n sbase k t /\
  ptr_covers G' tn' root t span /\
  copy_static t = copy_static s /\
  t.vs_memory = s.vs_memory /\
  eval_operand src t = eval_operand src s /\ op_taint tn' src = op_taint tn src /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!x. x <> tv ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  gvs[] >>
  simp[copy_prefix_jump, copy_prefix_update_var] >>
  simp[ptr_covers_def, copy_static_def, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  fs[ptr_covers_def, lookup_var_def, op_taint_def] >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, op_taint_def,
                           FLOOKUP_UPDATE]
QED

Theorem storage_copy_loop_path_ptr:
  !r k s G tn.
  r+k = n /\ ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  lookup_block hdr fn.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst hid EQ [Var cv; Lit (n2w n)] [tv];
     mk_inst (hid+1) JNZ [Var tv; Label exit_lbl; Label body_lbl] []] /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  bbb.bb_instructions =
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+3) ADD [Var root;Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv];
     mk_inst (id+7) JMP [Label hdr] []] /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  lookup_var cv s = SOME (n2w k) /\ FLOOKUP G cv = NONE /\
  op_taint tn src = {} /\ op_taint tn (Var cv) = {} /\
  ptr_covers G tn root s span /\ 32*n <= span /\
  w2n b+32*n < dimword(:256) /\ n < dimword(:256) /\
  ALL_DISTINCT [root;tv;cv;sv;vv;mv;dv;nv] /\
  (!x. MEM x [tv;cv;sv;vv;mv;dv;nv] ==> src <> Var x) /\
  ~ctx_has_dalloca ctx /\
  copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n sbase k s /\
  (!i h. i < k /\ h < 32 ==>
     (w2n b+32*i+h IN tn.t_mem <=>
      (a+n2w i,h) IN (if tr then tn.t_trans else tn.t_stor))) /\
  (!i. (i < w2n b \/ w2n b+32*k <= i) ==> (i IN tn.t_mem <=> i IN M0)) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    eval_operand src t = SOME a /\ op_taint tn' src = {} /\
    lookup_var root t = SOME b /\ ptr_covers G' tn' root t span /\
    copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n sbase n t /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i h. i < n /\ h < 32 ==>
       (w2n b+32*i+h IN tn'.t_mem <=>
        (a+n2w i,h) IN (if tr then tn'.t_trans else tn'.t_stor))) /\
    (!i. (i < w2n b \/ w2n b+32*n <= i) ==> (i IN tn'.t_mem <=> i IN M0)) /\
    (!x. ~MEM x [tv;cv;sv;vv;mv;dv;nv] ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  Induct_on `r` >- suspend "done" >>
  rpt gen_tac >> strip_tac >>
  suspend "step"
QED

Resume storage_copy_loop_path_ptr[done]:
  rpt gen_tac >> strip_tac >> `k = n` by decide_tac >> gvs[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0
    (DRESTRICT G (COMPL {tv})) (tn with t_var := tn.t_var |+ (tv,{}))
    (OK (jump_to exit_lbl (update_var tv (bool_to_word T) s)))` by
    (`k <= k /\ k < dimword(:256)` by decide_tac >>
     drule_all copy_loop_header_path_ptr >> simp[]) >>
  `root <> tv /\ src <> Var tv` by fs[ALL_DISTINCT] >>
  drule_all (SRULE [] (Q.GENL [`t`, `G'`, `tn'`] storage_copy_header_frame)) >>
  disch_then (qspecl_then [`bool_to_word T`, `exit_lbl`] strip_assume_tac) >>
  qexistsl [`DRESTRICT G (COMPL {tv})`,
            `tn with t_var := tn.t_var |+ (tv,{})`,
            `jump_to exit_lbl (update_var tv (bool_to_word T) s)`] >>
  simp[jump_to_def, update_var_def] >>
  fs[ALL_DISTINCT] >> metis_tac[]
QED
Resume storage_copy_loop_path_ptr[step]:
  `k < n /\ k <= n` by decide_tac >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME hbb` by fs[] >>
  drule_all copy_loop_header_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] mp_tac) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `OK hs` >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gh th` >>
  `root <> tv /\ src <> Var tv` by fs[ALL_DISTINCT] >>
  drule_all (SRULE [] (Q.GENL [`t`, `G'`, `tn'`] storage_copy_header_frame)) >>
  disch_then (qspecl_then [`0w`, `body_lbl`] strip_assume_tac) >>
  `~hs.vs_halted /\ hs.vs_current_bb = body_lbl /\ hs.vs_inst_idx = 0 /\
   eval_operand src hs = SOME a /\ lookup_var root hs = SOME b /\
   lookup_var cv hs = SOME (n2w k) /\ FLOOKUP Gh cv = NONE /\
   op_taint th src = {} /\ op_taint th (Var cv) = {} /\
   ptr_covers Gh th root hs span /\
   copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n sbase k hs /\
   th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
   th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm` by
    (simp[Abbr `hs`, Abbr `Gh`, Abbr `th`] >>
     fs[] >> simp[jump_to_def, update_var_def, lookup_var_def,
                   FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     fs[ALL_DISTINCT, op_taint_def]) >>
  suspend "body"
QED
Resume storage_copy_loop_path_ptr[body]:
  `ALL_DISTINCT [root;cv;sv;vv;mv;dv;nv] /\
   (!x. MEM x [cv;sv;vv;mv;dv;nv] ==> src <> Var x)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `32*k+32 <= span /\ w2n b+32*k < dimword(:256)` by decide_tac >>
  `lookup_block hs.vs_current_bb fn.fn_blocks = SOME bbb` by fs[] >>
  drule_all (PURE_REWRITE_RULE [APPEND, LENGTH, ADD_CLAUSES] (Q.INST [`pre` |-> `[]`,
    `post` |-> `[mk_inst (id+7) JMP [Label hdr] []]`] storage_copy_body_path_ptr)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gh th hs 0 Gb tb (OK bs)` >>
  suspend "advance"
QED
Resume storage_copy_loop_path_ptr[advance]:
  `(!i h. i < k /\ h < 32 ==>
     (w2n b+32*i+h IN th.t_mem <=>
      (a+n2w i,h) IN (if tr then th.t_trans else th.t_stor))) /\
   (!i. (i < w2n b \/ w2n b+32*k <= i) ==> (i IN th.t_mem <=> i IN M0))`
     by (simp[Abbr `th`] >> conj_tac >-
           (qpat_x_assum `!i h. i < k /\ h < 32 ==> _` (mp_tac o SRULE []) >> simp[]) >>
         qpat_x_assum `!i. _ \/ _ <= i ==> _` (mp_tac o SRULE []) >> simp[]) >>
  drule_all storage_copy_body_invariant_advance >> strip_tac >>
  `~bs.vs_halted` by (drule copy_static_fields >> fs[] >> metis_tac[]) >>
  `lookup_block bs.vs_current_bb fn.fn_blocks = SOME bbb /\
   get_instruction bbb bs.vs_inst_idx = SOME (mk_inst (id+7) JMP [Label hdr] [])`
     by fs[get_instruction_def] >>
  drule_all storage_copy_backedge_path_ptr >>
  disch_then (qspec_then `src` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK (jump_to hdr bs)` >>
  suspend "recur"
QED
Resume storage_copy_loop_path_ptr[recur]:
  qpat_x_assum `!k s G tn. _` (qspecl_then
    [`k+1`, `jump_to hdr bs`, `Gb`, `tb`] mp_tac) >>
  (impl_tac >-
    (qpat_x_assum `bs = _` kall_tac >>
     qpat_x_assum `tb.t_mem = _` kall_tac >>
     fs[] >> simp[copy_prefix_jump, jump_to_def, lookup_var_def] >>
     fs[lookup_var_def] >>
     rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE []))) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gb tb (jump_to hdr bs) 0 Gf tf (OK fin)` >>
  suspend "finish"
QED
Resume storage_copy_loop_path_ptr[finish]:
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  qpat_x_assum `gas_path_ptr D 0 ctx fn PG Gb tb (jump_to hdr bs) 0 Gf tf _` kall_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx fn PG Gh th hs 0 Gb tb (OK (jump_to hdr bs))` kall_tac >>
  qpat_x_assum `gas_path_ptr D 0 ctx fn PG Gh th hs 0 Gb tb (OK bs)` kall_tac >>
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  qexistsl [`Gf`, `tf`, `fin`] >>
  qpat_x_assum `bs = _` kall_tac >>
  qpat_x_assum `tb.t_mem = _` kall_tac >>
  simp[] >>
  suspend "frames"
QED
Resume storage_copy_loop_path_ptr[frames]:
  conj_tac >-
    (qpat_x_assum `!i h. i < n /\ h < 32 ==> _` mp_tac >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `!i. _ \/ _ <= i ==> (i IN tf.t_mem <=> _)` (mp_tac o SRULE []) >> simp[]) >>
  simp[Abbr `hs`, Abbr `Gh`, Abbr `th`, jump_to_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def]

QED
Finalise storage_copy_loop_path_ptr

(* Includes the initializer and final test; n=0 follows the same path. *)
Theorem storage_copy_entry_loop_path_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME ebb /\
  ebb.bb_instructions = pre ++
    [mk_inst eid ASSIGN [Lit 0w] [cv]; mk_inst (eid+1) JMP [Label hdr] []] /\
  s.vs_inst_idx = LENGTH pre /\
  lookup_block hdr fn.fn_blocks = SOME hbb /\
  hbb.bb_instructions =
    [mk_inst hid EQ [Var cv; Lit (n2w n)] [tv];
     mk_inst (hid+1) JNZ [Var tv; Label exit_lbl; Label body_lbl] []] /\
  lookup_block body_lbl fn.fn_blocks = SOME bbb /\
  bbb.bb_instructions =
    [mk_inst id ADD [src;Var cv] [sv];
     mk_inst (id+1) (if tr then TLOAD else SLOAD) [Var sv] [vv];
     mk_inst (id+2) MUL [Var cv;Lit 32w] [mv];
     mk_inst (id+3) ADD [Var root;Var mv] [dv];
     mk_inst (id+4) MSTORE [Var dv;Var vv] [];
     mk_inst (id+5) ADD [Var cv;Lit 1w] [nv];
     mk_inst (id+6) ASSIGN [Var nv] [cv];
     mk_inst (id+7) JMP [Label hdr] []] /\
  eval_operand src s = SOME a /\ lookup_var root s = SOME b /\
  op_taint tn src = {} /\ ptr_covers G tn root s span /\ 32*n <= span /\
  w2n b+32*n < dimword(:256) /\ n < dimword(:256) /\
  ALL_DISTINCT [root;tv;cv;sv;vv;mv;dv;nv] /\
  (!x. MEM x [tv;cv;sv;vv;mv;dv;nv] ==> src <> Var x) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
    i.inst_operands = [Lit w] /\
    FLOOKUP s.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    eval_operand src t = SOME a /\ op_taint tn' src = {} /\
    lookup_var root t = SOME b /\ ptr_covers G' tn' root t span /\
    copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n s n t /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!i h. i < n /\ h < 32 ==>
       (w2n b+32*i+h IN tn'.t_mem <=>
        (a+n2w i,h) IN (if tr then tn'.t_trans else tn'.t_stor))) /\
    (!i. (i < w2n b \/ w2n b+32*n <= i) ==> (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!x. ~MEM x [tv;cv;sv;vv;mv;dv;nv] ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    ((t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) /\
     alloca_inv t /\ alloca_room ctx fn t /\
     (!i w p sz. MEM i (fn_insts fn) /\ i.inst_opcode = ALLOCA /\
       i.inst_operands = [Lit w] /\
       FLOOKUP t.vs_allocas i.inst_id = SOME (p,sz) ==> sz = w2n w))
Proof
  strip_tac >>
  drule_all copy_loop_entry_path_ptr >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] assume_tac) >>
  `root <> cv /\ src <> Var cv` by fs[ALL_DISTINCT] >>
  `copy_prefix (if tr then LocTransient else LocStorage) a (w2n b) n s 0 s`
    by simp[copy_prefix_zero] >>
  drule_all (SRULE [] (Q.GENL [`t`, `G'`, `tn'`] storage_copy_header_frame)) >>
  disch_then (qspecl_then [`0w`, `hdr`] strip_assume_tac) >>
  suspend "initialize"
QED
Resume storage_copy_entry_loop_path_ptr[initialize]:
  qspecl_then [`n`, `0`, `jump_to hdr (update_var cv 0w s)`,
    `DRESTRICT G (COMPL {cv})`, `tn with t_var := tn.t_var |+ (cv,{})`]
    mp_tac (Q.INST [`sbase` |-> `s`, `M0` |-> `tn.t_mem`] storage_copy_loop_path_ptr) >>
  (impl_tac >-
    (simp[] >> simp[jump_to_def, update_var_def, lookup_var_def,
                    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
     fs[op_taint_def, ALL_DISTINCT])) >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG _ _ (jump_to hdr (update_var cv 0w s)) 0 Gf tf (OK fin)` >>
  drule_all gas_path_ptr_then >> disch_then (assume_tac o SRULE []) >>
  drule_all copy_prefix_recorded_resources >> strip_tac >>
  qexistsl [`Gf`, `tf`, `fin`] >> simp[] >>
  suspend "entry_frames"
QED
Resume storage_copy_entry_loop_path_ptr[entry_frames]:
  qpat_x_assum `!i. _ \/ _ <= i ==> (i IN tf.t_mem <=> _)` mp_tac >> simp[] >>
  strip_tac >> conj_tac >- (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!i w p sz. _ ==> sz = w2n w`
    (qspecl_then [`i`, `w`, `p`, `sz`] mp_tac) >> simp[]
QED
Finalise storage_copy_entry_loop_path_ptr
