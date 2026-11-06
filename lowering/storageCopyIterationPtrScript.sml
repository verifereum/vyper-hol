(* Counted iteration of the checked storage/transient word-copy loop. *)
Theory storageCopyIterationPtr
Ancestors
  storageCopyIterationBodyPtr storageCopyControlPtr storageCopyInvariantPtr
  fragGasPathPtr ptrDiscipline ptrSafeRun bodyPtrDefs exprSimStorageCopy
  venomState venomInst finite_map pred_set words

Theorem storage_copy_header_inv_path_ptr:
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  test IN scratch /\ test <> root /\ test <> cv /\ src <> Var test /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ k <= n /\ n < dimword(:256) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv; Lit (n2w n)] [test]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst jid JNZ [Var test; Label exit; Label body_lbl] []) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G' tn' t /\
    t.vs_current_bb = (if k = n then exit else body_lbl) /\ t.vs_inst_idx = 0 /\
    ~t.vs_halted
Proof
  strip_tac >>
  `lookup_var cv s = SOME (n2w k) /\ op_taint tn (Var cv) = {}` by
    fs[storage_copy_inv_ptr_def] >>
  drule_all storage_copy_header_path_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] assume_tac) >>
  qexistsl_tac [`DRESTRICT G (COMPL {test})`, `tn with t_var := tn.t_var |+ (test,{})`,
    `jump_to (if k = n then exit else body_lbl)
      (update_var test (bool_to_word (k = n)) s with vs_inst_idx := SUC s.vs_inst_idx)`] >>
  simp[] >> conj_tac
  >- (irule storage_copy_inv_ptr_scratch >> simp[] >> qexists_tac `G` >>
      simp[FLOOKUP_DRESTRICT]) >>
  simp[jump_to_def, update_var_def]
QED

Theorem storage_copy_iterate_path_ptr:
  !remaining k G tn s.
  storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase k G tn s /\
  k+remaining = n /\ n < dimword(:256) /\ b+32*n < dimword(:256) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  ALL_DISTINCT [sv;vv;mv;dv;nv;cv;root;test] /\
  EVERY (\x. x IN scratch /\ src <> Var x) [sv;vv;mv;dv;nv;cv;test] /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
  lookup_block hdr fn.fn_blocks = SOME hb /\
  hb.bb_instructions =
    [mk_inst hid EQ [Var cv; Lit (n2w n)] [test];
     mk_inst (hid+1) JNZ [Var test; Label exit; Label body_lbl] []] /\
  lookup_block body_lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions =
    [mk_inst bid ADD [src; Var cv] [sv];
     mk_inst (bid+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv];
     mk_inst (bid+2) MUL [Var cv; Lit 32w] [mv];
     mk_inst (bid+3) ADD [Var root; Var mv] [dv];
     mk_inst (bid+4) MSTORE [Var dv; Var vv] [];
     mk_inst (bid+5) ADD [Var cv; Lit 1w] [nv];
     mk_inst (bid+6) ASSIGN [Var nv] [cv];
     mk_inst (backedge_id) JMP [Label hdr] []] ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase n G' tn' t /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  Induct_on `remaining`
  >- suspend "zero" >>
  suspend "step"
QED

Resume storage_copy_iterate_path_ptr[zero]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `k = n /\ k <= n` by decide_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [listTheory.ALL_DISTINCT, listTheory.EVERY_DEF]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `test <> root /\ test <> cv` by metis_tac[] >>
  `get_instruction hb s.vs_inst_idx = SOME (mk_inst hid EQ [Var cv; Lit (n2w n)] [test]) /\
   get_instruction hb (SUC s.vs_inst_idx) = SOME
     (mk_inst (hid+1) JNZ [Var test; Label exit; Label body_lbl] []) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME hb` by
    simp[get_instruction_def] >>
  drule_all storage_copy_header_inv_path_ptr >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED

Resume storage_copy_iterate_path_ptr[step]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `k < n /\ k <= n` by decide_tac >>
  rule_assum_tac (SIMP_RULE (srw_ss()) [listTheory.ALL_DISTINCT, listTheory.EVERY_DEF]) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  `test <> root /\ test <> cv` by metis_tac[] >>
  `get_instruction hb s.vs_inst_idx = SOME (mk_inst hid EQ [Var cv; Lit (n2w n)] [test]) /\
   get_instruction hb (SUC s.vs_inst_idx) = SOME
     (mk_inst (hid+1) JNZ [Var test; Label exit; Label body_lbl] []) /\
   lookup_block s.vs_current_bb fn.fn_blocks = SOME hb` by
    simp[get_instruction_def] >>
  drule_all storage_copy_header_inv_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  `s1.vs_current_bb = body_lbl` by simp[] >>
  suspend "body"
QED

Resume storage_copy_iterate_path_ptr[body]:
  `ALL_DISTINCT [sv;vv;mv;dv;nv;cv;root] /\
   EVERY (\x. x IN scratch /\ src <> Var x) [sv;vv;mv;dv;nv;cv]` by
    simp[listTheory.ALL_DISTINCT] >>
  `get_instruction bb s1.vs_inst_idx = SOME (mk_inst bid ADD [src; Var cv] [sv]) /\
   get_instruction bb (s1.vs_inst_idx+1) = SOME
     (mk_inst (bid+1) (if loc = LocStorage then SLOAD else TLOAD) [Var sv] [vv]) /\
   get_instruction bb (s1.vs_inst_idx+2) = SOME (mk_inst (bid+2) MUL [Var cv; Lit 32w] [mv]) /\
   get_instruction bb (s1.vs_inst_idx+3) = SOME (mk_inst (bid+3) ADD [Var root; Var mv] [dv]) /\
   get_instruction bb (s1.vs_inst_idx+4) = SOME (mk_inst (bid+4) MSTORE [Var dv; Var vv] []) /\
   get_instruction bb (s1.vs_inst_idx+5) = SOME (mk_inst (bid+5) ADD [Var cv; Lit 1w] [nv]) /\
   get_instruction bb (s1.vs_inst_idx+6) = SOME (mk_inst (bid+6) ASSIGN [Var nv] [cv]) /\
   lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb` by
    simp[get_instruction_def] >>
  drule_all storage_copy_body_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` >>
  `gas_path_ptr D 0 ctx fn PG G2 tn2 s2 0 G2 tn2 (OK (jump_to hdr s2))` by
    (irule storage_copy_jump_path_ptr >> simp[] >>
     qexists_tac `backedge_id` >> simp[get_instruction_def]) >>
  `storage_copy_inv_ptr loc src root cv scratch a b n sbase Gbase tnbase (k+1)
    G2 tn2 (jump_to hdr s2)` by simp[] >>
  `k+1+remaining = n` by decide_tac >>
  first_x_assum (qspecl_then [`k+1`, `G2`, `tn2`, `jump_to hdr s2`] mp_tac) >>
  simp[jump_to_def] >> strip_tac >>
  suspend "compose"
QED

Resume storage_copy_iterate_path_ptr[compose]:
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >>
  irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`G1`, `s1`, `tn1`] >> conj_tac >- simp[] >>
  irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`G2`, `s2`, `tn2`] >> conj_tac >- simp[] >>
  irule (SRULE[] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
  qexistsl_tac [`G2`, `jump_to hdr s2`, `tn2`] >>
  simp[jump_to_def]
QED

Finalise storage_copy_iterate_path_ptr
