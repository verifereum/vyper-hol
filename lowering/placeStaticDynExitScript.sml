Theory placeStaticDynExit
Ancestors
  placeStaticStoreExit placeStaticCopyExit placeDynStoragePath placeDynExecutionLayout
  placeDynCompile placeCopyControlPath placeStoreCopyPath stmtSimStoreCopy
  fragExec fragGasSeq fragGasSeqAbort fragGasMode slotCopyExecution emitHelperProps
  exprLoweringProps exprLowering context compileEnv venomInst venomState
  venomExecSemantics list rich_list words arithmetic
Libs
  stepInstBaseLib

Theorem place_zero_word_copy_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst 0 LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 0 t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_copy_code >> strip_tac >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\
       store_copy_frame sa loc b k s0 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\
       store_copy_frame sa loc b k s0 0 t /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by suspend "header" >>
  qexists_tac `t` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_zero_word_copy_path[init]:
  qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s0.vs_inst_idx bb0.bb_instructions)` by simp[] >>
  `!x. not_fresh_at sa x ==> x <> cv` by (fs[] >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  drule_all place_store_copy_init_path >>
  disch_then (qspecl_then [`loc`, `k`, `ctx`, `b`] strip_assume_tac) >>
  `get_instruction bb0 t.vs_inst_idx =
   SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Resume place_zero_word_copy_path[header]:
  qpat_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst idh EQ [Var cv; Lit (n2w 0)] [tv]]
    (DROP r.vs_inst_idx bbh.bb_instructions)` by simp[] >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block r.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  `eval_operand (Var cv) r = SOME (n2w 0)` by simp[] >>
  `0 <= (0:num) /\ 0 < dimword (:256)` by simp[] >>
  drule_all place_store_copy_test_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  `get_instruction bbh t.vs_inst_idx =
   SOME (mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bbh` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `jump_to exit t` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  fs[place_store_frame_control, jump_to_def, eval_operand_def, lookup_var_def]
QED

Finalise place_zero_word_copy_path

Theorem place_static_dyn_single_exit[local]:
  isPREFIX
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MLOAD [Var sv] [vv];
     mk_inst (id+4) ADD [Var ctr;Lit 1w] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv];
     mk_inst (id+6) (if transient then TSTORE else SSTORE) [Var dv;Var vv] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var ctr) s = SOME (n2w j) /\ not_fresh_at sa ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  ALL_DISTINCT [mv;ov;sv;vv;kv;dv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [mv;ov;sv;vv;kv;dv]) ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  strip_tac >>
  qabbrev_tac `a = n2w j * 32w : bytes32` >>
  qabbrev_tac `val = mload (w2n (b+32w+a)) s` >>
  qabbrev_tac `q = update_var dv (k+1w+n2w j)
    (update_var kv (n2w j+1w) (update_var vv val
      (update_var sv (b+32w+a) (update_var ov (32w+a) (update_var mv a s)))))` >>
  qabbrev_tac `code =
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MLOAD [Var sv] [vv];
     mk_inst (id+4) ADD [Var ctr;Lit 1w] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv]]` >>
  `run_inst_seq code s = OK q` by suspend "run" >>
  `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[Abbr `code`]) >>
  drule tuple_run_inst_seq_gas_path >> disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `endpoint = q with vs_inst_idx := s.vs_inst_idx+6` >>
  `gas_marked_path F ctx func s 0 (OK endpoint)` by
    simp[Abbr `endpoint`, gas_marked_path_def] >>
  `?r. gas_marked_path F ctx func endpoint 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r`
    by suspend "fault" >>
  qexists_tac `r` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_dyn_single_exit[run]:
  fs[ALL_DISTINCT] >>
  `!x. MEM x [mv;ov;sv;vv;kv;dv] ==>
    src <> Var x /\ dst <> Var x /\ ctr <> x` by
    (simp[] >> rpt strip_tac >> metis_tac[]) >>
  simp[Abbr `code`, Abbr `q`, Abbr `a`, Abbr `val`,
    run_inst_seq_def, mk_inst_def,
    stepInstBaseLib.simp_opcode_clause ``MUL``,
    stepInstBaseLib.simp_opcode_clause ``ADD``,
    stepInstBaseLib.simp_opcode_clause ``MLOAD``,
    exec_pure2_def, exec_read1_def,
    slot_copy_operand_update, eval_operand_lit, eval_operand_update_var_local,
    WORD_ADD_ASSOC] >>
  fs[update_var_def, mload_def, eval_operand_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE, Excl "isPREFIX"] >>
  simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]
QED

Resume place_static_dyn_single_exit[fault]:
  `endpoint.vs_call_ctx.cc_static /\ ~endpoint.vs_halted /\
   lookup_block endpoint.vs_current_bb func.fn_blocks = SOME bb /\
   endpoint.vs_inst_idx = s.vs_inst_idx+6` by
    simp[Abbr `endpoint`, Abbr `q`, update_var_def] >>
  `eval_operand (Var dv) endpoint = SOME (k+1w+n2w j) /\
   eval_operand (Var vv) endpoint = SOME val` by
    (fs[ALL_DISTINCT] >>
     simp[Abbr `endpoint`, Abbr `q`, update_var_def, eval_operand_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `isPREFIX [mk_inst (id+6) (if transient then TSTORE else SSTORE)
       [Var dv;Var vv] []]
     (DROP endpoint.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `isPREFIX (_::_::_::_::_::_::_::[]) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     `DROP (s.vs_inst_idx+6) bb.bb_instructions =
      DROP 6 (DROP s.vs_inst_idx bb.bb_instructions)` by
       simp[DROP_DROP_T, ADD_COMM] >>
     asm_rewrite_tac[] >> simp[]) >>
  irule place_static_store_prefix_exit >> metis_tac[]
QED

Finalise place_static_dyn_single_exit

Theorem place_static_dyn_multi_path[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  emit_op MUL [Var ctr;Lit (n2w ems)] stb = (mulop,b1) /\
  emit_op ADD [Lit 32w;mulop] b1 = (off,b2) /\
  emit_op ADD [src;off] b2 = (sp,b3) /\
  emit_op MUL [Var ctr;Lit (n2w ew)] b3 = (smul,b4) /\
  emit_op ADD [Lit 1w;smul] b4 = (slot,b5) /\
  emit_op ADD [dst;slot] b5 = (dp,b6) /\
  compile_word_copy_loop sp dp ew LocMemory loc F b6 = (oldcopy,ste) /\
  fn_has_code b6 ste func /\ fn_has_code stb ste func /\
  ew < dimword (:256) /\ not_fresh_at stb ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x) /\
  eval_operand src q = SOME b /\ eval_operand dst q = SOME k /\
  eval_operand (Var ctr) q = SOME (n2w j) /\
  ~q.vs_halted /\ q.vs_call_ctx.cc_static /\
  q.vs_current_bb = stb.cs_current_bb /\
  q.vs_inst_idx = LENGTH stb.cs_current_insts ==>
  if ew = 0 then
    ?r. gas_marked_path F ctx func q 0 (OK r) /\
        store_copy_frame stb loc (b+32w+n2w j*n2w ems)
          (k+1w+n2w j*n2w ew) q 0 r /\
        ~r.vs_halted /\ r.vs_current_bb = ste.cs_current_bb /\
        r.vs_inst_idx = LENGTH ste.cs_current_insts
  else
    ?r. gas_marked_path F ctx func q 0 r /\ exit_result r /\
        stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_dyn_multi_address_layout >> strip_tac >>
  `cs_extends b6 ste` by
    (qspec_then `b6` mp_tac (ci_mono_compile_word_copy_loop |>
       Q.SPECL [`sp`, `dp`, `ew`, `LocMemory`, `loc`, `F`]) >>
     simp[ci_mono_def]) >>
  `cs_extends stb b6` by
    (fs[same_blocks_def, compileEnvTheory.cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code stb b6 func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `?bb. lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts stb b6) (DROP q.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, Excl "isPREFIX"] >>
     gvs[IS_PREFIX_APPEND, Excl "isPREFIX"] >>
     qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
     simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_APPEND,
       IS_PREFIX_APPEND] >> metis_tac[]) >>
  qpat_assum `emitted_insts stb b6 = _`
    (fn th => qpat_x_assum `isPREFIX (emitted_insts _ _) _`
      (assume_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  drule_all place_dyn_address_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `!x. not_fresh_at stb x ==> not_fresh_at b6 x` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, DECIDE ``n <= n+6``]) >>
  `!x. sp = Var x \/ dp = Var x ==> not_fresh_at b6 x` by
    (imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_fresh >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     fs[ci_mono_def, not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `t.vs_call_ctx.cc_static` by
    (qpat_assum `store_copy_normalize q t = q`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def] >>
     metis_tac[]) >>
  `t.vs_current_bb = b6.cs_current_bb /\
   t.vs_inst_idx = LENGTH b6.cs_current_insts` by
    (fs[same_blocks_def, IS_PREFIX_APPEND, Excl "isPREFIX"] >>
     qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `eval_operand sp t = SOME (b+32w+n2w j*n2w ems) /\
   eval_operand dp t = SOME (k+1w+n2w j*n2w ew)` by metis_tac[] >>
  Cases_on `ew = 0`
  >- suspend "zero" >>
  `0 < ew` by decide_tac >>
  drule_all place_static_copy_exit >>
  disch_then (qspecl_then [`ee`, `ctx`, `RetQ`] strip_assume_tac) >>
  simp[] >> qexists_tac `r` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED

Resume place_static_dyn_multi_path[zero]:
  qpat_x_assum `ew = 0` SUBST_ALL_TAC >>
  pure_rewrite_tac[REFL_CLAUSE, COND_CLAUSES] >>
  drule_all place_zero_word_copy_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  simp[] >>
  drule place_store_frame_normalize >>
  disch_then (qspec_then `q` assume_tac) >>
  simp[store_copy_frame_def] >>
  qpat_x_assum `store_copy_frame b6 _ _ _ _ _ _` mp_tac >>
  simp[store_copy_frame_def] >> metis_tac[]
QED

Finalise place_static_dyn_multi_path

Theorem place_static_dyn_storage_exit:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  mload (w2n b) s0 = n2w n /\ n < dimword (:256) /\
  ew < dimword (:256) /\ (ew = 1 ==> ems = 32) /\
  s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s0 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  strip_tac >> drule_all place_dyn_execution_layout >> strip_tac >>
  qabbrev_tac `Inv = \j q.
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s0) /\
    store_copy_normalize s0 q = s0 /\
    eval_operand (Var ctr) q = SOME (n2w j) /\
    eval_operand (Var lv) q = SOME (n2w n)` >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\ Inv 0 r /\
       ~r.vs_halted /\ r.vs_current_bb = cond /\ r.vs_inst_idx = 0`
    by suspend "init" >>
  `!j q. j <= n /\ Inv j q /\ ~q.vs_halted /\
          q.vs_current_bb = cond /\ q.vs_inst_idx = 0 ==>
     ?t. gas_marked_path F ctx func q 0 (OK t) /\ Inv j t /\
         ~t.vs_halted /\ t.vs_inst_idx = 0 /\
         t.vs_current_bb = (if j = n then exit else body_lbl)`
    by suspend "header" >>
  `!u. Inv n u /\ ~u.vs_halted /\ u.vs_current_bb = exit /\
       u.vs_inst_idx = 0 ==>
    ?res. gas_marked_path F ctx func u 0 res /\ exit_result res /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) res`
    by suspend "finish" >>
  Cases_on `ew = 0` >- suspend "zero_loop" >>
  suspend "positive"
QED

Resume place_static_dyn_storage_exit[init]:
  `lv <> ctr /\
   (!x. not_fresh_at sa x ==> x <> lv /\ x <> ctr)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst sa.cs_next_id MLOAD [src] [lv];
            mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]]
      (DROP s0.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX (mk_inst sa.cs_next_id MLOAD _ _::_) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  drule_all place_dyn_init_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (sa.cs_next_id+2) JMP [Label cond] [])` by
    (qpat_assum `isPREFIX [mk_inst sa.cs_next_id MLOAD _ _;_;_] _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX (mk_inst (sa.cs_next_id+1) ASSIGN _ _::_) _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX [mk_inst (sa.cs_next_id+2) JMP _ _] _`
       (mp_then Any mp_tac instruction_prefix_cursor) >> simp[ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to cond t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to cond t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[Abbr `Inv`, jump_to_def, lookup_var_def, eval_operand_def,
    store_copy_normalize_def] >>
  gvs[eval_operand_def, lookup_var_def, store_copy_normalize_def]
QED

Resume place_static_dyn_storage_exit[header]:
  rpt strip_tac >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh /\
   isPREFIX [mk_inst ih LT [Var ctr;Var lv] [tv];
     mk_inst (ih+1) ISZERO [Var tv] [dv];
     mk_inst (ih+2) JNZ [Var dv;Label exit;Label body_lbl] []]
     (DROP q.vs_inst_idx bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  `tv <> dv /\ (!x. not_fresh_at sa x ==> x <> tv /\ x <> dv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  qpat_x_assum `Inv j q` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  drule_all place_dyn_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >>
  conj_tac >-
    (qpat_x_assum `store_copy_normalize q t = q`
       (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
     simp[store_copy_normalize_def]) >>
  fs[ALL_DISTINCT, eval_operand_def] >> metis_tac[]
QED

Resume place_static_dyn_storage_exit[finish]:
  rpt strip_tac >>
  qpat_x_assum `Inv n u` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `u.vs_labels = s0.vs_labels /\ u.vs_call_ctx = s0.vs_call_ctx` by
    (conj_tac >-
      (qpat_assum `store_copy_normalize s0 u = s0`
         (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
       simp_tac (srw_ss()) [store_copy_normalize_def]) >>
     qpat_assum `store_copy_normalize s0 u = s0`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def]) >>
  `eval_operand dst u = SOME k` by
    (Cases_on `dst` >> simp[eval_operand_def] >>
     fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bbx /\
   isPREFIX [mk_inst ix (if transient then TSTORE else SSTORE) [dst;Var lv] []]
     (DROP u.vs_inst_idx bbx.bb_instructions)` by simp[Excl "isPREFIX"] >>
  irule place_static_store_prefix_exit >> metis_tac[]
QED

Resume place_static_dyn_storage_exit[zero_loop]:
  `?u. gas_marked_path F ctx func r 0 (OK u) /\ Inv n u /\
       ~u.vs_halted /\ u.vs_current_bb = exit /\ u.vs_inst_idx = 0` by
    (irule place_copy_iterate_path >> simp[] >>
     reverse conj_tac >- (qexistsl_tac [`0`, `n`] >> simp[]) >>
     qexists_tac `body_lbl` >> simp[] >> suspend "zero_body") >>
  qpat_x_assum `!u. Inv n u /\ _ ==> _` drule >>
  simp[] >> strip_tac >> qexists_tac `res` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED
Resume place_static_dyn_storage_exit[zero_body]:
  qpat_x_assum `!j q. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `!u. Inv n u /\ _ ==> _` kall_tac >>
  qpat_x_assum `Inv 0 r` kall_tac >>
  rpt strip_tac >>
  qpat_x_assum `Inv j q` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `q.vs_labels = s0.vs_labels /\ q.vs_call_ctx = s0.vs_call_ctx` by
    (conj_tac >-
      (qpat_assum `store_copy_normalize s0 q = s0`
         (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
       simp_tac (srw_ss()) [store_copy_normalize_def]) >>
     qpat_assum `store_copy_normalize s0 q = s0`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def]) >>
  `eval_operand src q = SOME b /\ eval_operand dst q = SOME k` by
    (conj_tac >-
      (Cases_on `src` >> simp[eval_operand_def] >>
       fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
     Cases_on `dst` >> simp[eval_operand_def] >>
     fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `not_fresh_at stb ctr /\ not_fresh_at stb lv /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x)` by
    (fs[EVERY_DEF] >> metis_tac[]) >>
  `(if transient then LocTransient else LocStorage) = LocStorage \/
   (if transient then LocTransient else LocStorage) = LocTransient` by
    (Cases_on `transient` >> simp[]) >>
  `q.vs_call_ctx.cc_static /\ q.vs_current_bb = stb.cs_current_bb /\
   q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
  qpat_x_assum `ew = 0` SUBST_ALL_TAC >>
  qpat_x_assum `if 0 = 1 then _ else _` mp_tac >>
  pure_rewrite_tac[DECIDE ``~(0 = 1)``, COND_CLAUSES] >> strip_tac >>
  `?rb. gas_marked_path F ctx func q 0 (OK rb) /\
    store_copy_frame stb (if transient then LocTransient else LocStorage)
      (b+32w+n2w j*n2w ems) (k+1w+n2w j*n2w 0) q 0 rb /\
    ~rb.vs_halted /\ rb.vs_current_bb = ste.cs_current_bb /\
    rb.vs_inst_idx = LENGTH ste.cs_current_insts` by
    (irule (place_static_dyn_multi_path |> SPEC_ALL |>
       Q.INST [`ew` |-> `0`] |> SIMP_RULE (srw_ss()) []) >>
     simp[] >> metis_tac[]) >>
  suspend "zero_increment"
QED
Resume place_static_dyn_storage_exit[zero_increment]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `store_copy_normalize q rb = q` by
    (drule place_store_frame_normalize >>
     disch_then (qspec_then `q` mp_tac) >>
     simp[place_store_prefix_eqs, store_copy_normalize_def,
          venom_state_component_equality]) >>
  `(!x. not_fresh_at stb x ==> lookup_var x rb = lookup_var x q)` by
    fs[store_copy_frame_def] >>
  `ctr <> nv /\ (!x. not_fresh_at ste x ==> x <> nv)` by metis_tac[] >>
  `lookup_block rb.vs_current_bb func.fn_blocks = SOME bbt /\
   isPREFIX [mk_inst it ADD [Var ctr;Lit 1w] [nv];
             mk_inst (it+1) ASSIGN [Var nv] [ctr]]
      (DROP rb.vs_inst_idx bbt.bb_instructions)` by
    (qpat_assum `isPREFIX (mk_inst it ADD _ _::_) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `eval_operand (Var ctr) rb = SOME (n2w j)` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  drule_all place_dyn_increment_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `store_copy_normalize rb ri = rb` >>
  `get_instruction bbt ri.vs_inst_idx =
     SOME (mk_inst (it+2) JMP [Label cond] [])` by
    (qpat_assum `isPREFIX [mk_inst it ADD _ _;_;_] _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX (mk_inst (it+1) ASSIGN _ _::_) _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX [mk_inst (it+2) JMP _ _] _`
       (mp_then Any mp_tac instruction_prefix_cursor) >> simp[ADD1]) >>
  `gas_marked_path F ctx func ri 0 (OK (jump_to cond ri))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  `gas_marked_path F ctx func rb 0 (OK (jump_to cond ri))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexists_tac `jump_to cond ri` >>
  conj_tac >-
    (metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  `store_copy_normalize s0 (jump_to cond ri) = s0` by
    (qpat_assum `store_copy_normalize rb ri = rb`
       (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
     qpat_assum `store_copy_normalize q rb = q`
       (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def, jump_to_def,
                            venom_state_component_equality] >>
     fs[store_copy_normalize_def, venom_state_component_equality]) >>
  simp[ADD1] >>
  simp[jump_to_def, eval_operand_def, lookup_var_def] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> ~MEM x _` mp_tac >>
  simp_tac (srw_ss()) [MEM] >> strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp_tac (srw_ss()) [ALL_DISTINCT, MEM] >> strip_tac >>
  qpat_x_assum `eval_operand (Var lv) q = _` mp_tac >>
  qpat_x_assum `!x. not_fresh_at ste x /\ x <> ctr ==> _` mp_tac >>
  qpat_x_assum `!x. not_fresh_at stb x ==> lookup_var x rb = _` mp_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` mp_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at stb x` mp_tac >>
  qpat_x_assum `!x. not_fresh_at stb x ==> not_fresh_at ste x` mp_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> x <> lv /\ _` mp_tac >>
  qpat_x_assum `not_fresh_at stb lv` mp_tac >>
  qpat_x_assum `lv <> ctr` mp_tac >>
  qpat_x_assum `gas_marked_path _ _ _ q 0 (OK rb)` mp_tac >>
  qpat_x_assum `gas_marked_path _ _ _ rb 0 (OK (jump_to cond ri))` mp_tac >>
  qpat_x_assum `ri.vs_current_bb = rb.vs_current_bb` mp_tac >>
  qpat_x_assum `rb.vs_current_bb = ste.cs_current_bb` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac (srw_ss()) [lookup_var_def, eval_operand_def, jump_to_def] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED
Resume place_static_dyn_storage_exit[positive]:
  qpat_x_assum `!j q. j <= n /\ _ ==> _`
    (qspecl_then [`0`, `r`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `n = 0`
  >- (gvs[] >>
      qpat_x_assum `!u. Inv 0 u /\ _ ==> _` drule >>
      simp[] >> strip_tac >> qexists_tac `res` >> simp[] >>
      metis_tac[gas_marked_path_then, ADD_CLAUSES]) >>
  `t.vs_current_bb = body_lbl` by simp[] >>
  `eval_operand src t = SOME b /\ eval_operand dst t = SOME k /\
   eval_operand (Var ctr) t = SOME (n2w 0) /\
   t.vs_call_ctx.cc_static` by suspend "positive_source" >>
  `?res. gas_marked_path F ctx func t 0 res /\ exit_result res /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) res`
    by suspend "positive_body" >>
  qexists_tac `res` >> simp[] >>
  metis_tac[gas_marked_path_then, ADD_CLAUSES]
QED
Resume place_static_dyn_storage_exit[positive_source]:
  qpat_x_assum `Inv 0 t` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `t.vs_labels = s0.vs_labels /\ t.vs_call_ctx = s0.vs_call_ctx` by
    (qpat_assum `store_copy_normalize s0 t = s0` mp_tac >>
     simp_tac (srw_ss()) [store_copy_normalize_def, venom_state_component_equality]) >>
  simp[] >> conj_tac
  >- (Cases_on `src` >> simp[eval_operand_def] >>
      fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
  Cases_on `dst` >> simp[eval_operand_def] >>
  fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]
QED
Resume place_static_dyn_storage_exit[positive_body]:
  qpat_x_assum `!u. Inv n u /\ _ ==> _` kall_tac >>
  `not_fresh_at stb ctr /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x)` by
    (fs[EVERY_DEF] >> metis_tac[]) >>
  `t.vs_current_bb = stb.cs_current_bb /\
   t.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
  Cases_on `ew = 1` >- suspend "positive_single" >>
  qpat_x_assum `if ew = 1 then _ else _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  SUBGOAL_THEN
    ``(if transient then LocTransient else LocStorage) = LocStorage \/
      (if transient then LocTransient else LocStorage) = LocTransient`` assume_tac
  >- (Cases_on `transient` >> simp[]) >>
  drule_all (place_static_dyn_multi_path |> SPEC_ALL |> Q.INST [`j` |-> `0`] |>
    SIMP_RULE (srw_ss()) []) >>
  simp[]
QED
Resume place_static_dyn_storage_exit[positive_single]:
  qpat_x_assum `if ew = 1 then _ else _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  `emit_void (if transient then TSTORE else SSTORE) [dp;value] b6 = ((),ste)` by
    (Cases_on `transient` >> fs[]) >>
  drule_all place_dyn_single_body_layout >> strip_tac >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts stb ste)
          (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_assum `fn_has_code stb ste func` mp_tac >>
     qpat_assum `same_blocks stb ste` mp_tac >>
     qpat_assum `stb.cs_current_insts = []` mp_tac >>
     qpat_assum `t.vs_current_bb = stb.cs_current_bb` mp_tac >>
     qpat_assum `t.vs_inst_idx = LENGTH stb.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[fn_has_code_def, same_blocks_def, emitted_insts_def,
          Excl "isPREFIX"] >> rpt strip_tac >>
     qexists_tac `bb` >> simp[]) >>
  qpat_assum `emitted_insts stb ste = _`
    (fn th => qpat_x_assum `isPREFIX (emitted_insts _ _) _`
      (assume_tac o PURE_ONCE_REWRITE_RULE [th])) >>
  drule (place_static_dyn_single_exit |> SPEC_ALL |>
    Q.INST [`j` |-> `0`] |> SIMP_RULE (srw_ss()) [Excl "isPREFIX"]) >>
  simp[] >> disch_then (qspec_then `stb` mp_tac) >>
  simp[] >> disch_then irule >>
  qpat_assum `ALL_DISTINCT [mv;ov;sv;vv;kv;_]` mp_tac >>
  qpat_assum `!x. not_fresh_at stb x ==> ~MEM x [mv;ov;sv;vv;kv;_]` mp_tac >>
  qpat_assum `!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x` mp_tac >>
  qpat_assum `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` mp_tac >>
  qpat_assum `t.vs_current_bb = body_lbl` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[ALL_DISTINCT] >> metis_tac[]
QED
Finalise place_static_dyn_storage_exit
