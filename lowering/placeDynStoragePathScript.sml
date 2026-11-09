Theory placeDynStoragePath
Ancestors
  placeStoreCopyPath placeDynCompile placeDynExecutionLayout stmtSimStoreCopy placeCopyControlPath
  list rich_list arithmetic words venomState venomInst venomExecSemantics
  fragExec fragGasSeq fragGasMode slotCopyExecution fragGasSeqAbort
  loweringSlice exprLoweringProps finite_map emitHelperProps compileEnv
Libs
  stepInstBaseLib

Definition place_dyn_prefix_def:
  place_dyn_prefix loc b k ew ems s0 j =
    FOLDL (\t i. store_copy_prefix loc
      (b + 32w + n2w i * n2w ems)
      (k + 1w + n2w i * n2w ew) t ew) s0 (COUNT_LIST j)
End

Theorem place_dyn_prefix_eqs:
  place_dyn_prefix loc b k ew ems s0 0 = s0 /\
  (!j. place_dyn_prefix loc b k ew ems s0 (SUC j) =
    store_copy_prefix loc (b + 32w + n2w j * n2w ems)
      (k + 1w + n2w j * n2w ew)
      (place_dyn_prefix loc b k ew ems s0 j) ew)
Proof
  simp[place_dyn_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC, COUNT_LIST_def]
QED

Theorem place_dyn_prefix_fields:
  (place_dyn_prefix loc b k ew ems s0 j).vs_memory = s0.vs_memory /\
  (place_dyn_prefix loc b k ew ems s0 j).vs_labels = s0.vs_labels /\
  (place_dyn_prefix loc b k ew ems s0 j).vs_call_ctx = s0.vs_call_ctx /\
  (place_dyn_prefix loc b k ew ems s0 j).vs_allocas = s0.vs_allocas /\
  (place_dyn_prefix loc b k ew ems s0 j).vs_alloca_next = s0.vs_alloca_next /\
  (place_dyn_prefix loc b k ew ems s0 j).vs_halted = s0.vs_halted
Proof
  Induct_on `j` >> simp[place_dyn_prefix_eqs, place_store_prefix_fields]
QED

Theorem place_store_prefix_normalize:
  store_copy_normalize sbase (store_copy_prefix loc b k s i) =
  store_copy_prefix loc b k (store_copy_normalize sbase s) i
Proof
  Induct_on `i` >> simp[place_store_prefix_eqs] >>
  first_x_assum (rewrite_tac o single o GSYM) >>
  Cases_on `loc = LocStorage` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def, mload_def]
QED

Theorem place_store_frame_normalize:
  store_copy_frame sa loc b k q i r ==>
  store_copy_normalize s0 r =
    store_copy_prefix loc b k (store_copy_normalize s0 q) i
Proof
  simp[store_copy_frame_def] >> strip_tac >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
  simp[place_store_prefix_normalize, store_copy_normalize_def]
QED

Theorem place_dyn_single_body_path:
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var ctr; Lit 32w] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MLOAD [Var sv] [vv];
     mk_inst (id+4) ADD [Var ctr;Lit 1w] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv];
     mk_inst (id+6) (if loc = LocStorage then SSTORE else TSTORE)
       [Var dv;Var vv] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var ctr) s = SOME (n2w j) /\ not_fresh_at sa ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  ALL_DISTINCT [mv;ov;sv;vv;kv;dv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [mv;ov;sv;vv;kv;dv]) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_frame sa loc (b+32w+n2w j*32w) (k+1w+n2w j) s 1 t /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 7
Proof
  strip_tac >>
  qabbrev_tac `a = n2w j * 32w : bytes32` >>
  qabbrev_tac `val = mload (w2n (b+32w+a)) s` >>
  qabbrev_tac `q = update_var dv (k+1w+n2w j)
    (update_var kv (n2w j+1w) (update_var vv val
      (update_var sv (b+32w+a) (update_var ov (32w+a) (update_var mv a s)))))` >>
  qabbrev_tac `r = (if loc = LocStorage then sstore else tstore)
    (k+1w+n2w j) val q` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    (fs[ALL_DISTINCT] >>
     `!x. MEM x [mv;ov;sv;vv;kv;dv] ==>
       src <> Var x /\ dst <> Var x /\ ctr <> x` by
       (simp[] >> rpt strip_tac >> metis_tac[]) >>
     Cases_on `loc = LocStorage` >>
     simp[Abbr `code`, Abbr `r`, Abbr `q`, Abbr `a`, Abbr `val`,
       run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``MUL``,
       stepInstBaseLib.simp_opcode_clause ``ADD``,
       stepInstBaseLib.simp_opcode_clause ``MLOAD``,
       stepInstBaseLib.simp_opcode_clause ``SSTORE``,
       stepInstBaseLib.simp_opcode_clause ``TSTORE``,
       exec_pure2_def, exec_read1_def, exec_write2_def,
       slot_copy_operand_update, eval_operand_lit, eval_operand_update_var_local,
       WORD_ADD_ASSOC] >>
     fs[update_var_def, mload_def, eval_operand_def, lookup_var_def,
        FLOOKUP_UPDATE, Excl "isPREFIX"] >>
     simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+7` >>
  conj_tac >- (Cases_on `loc = LocStorage` >>
    gvs[gas_marked_path_def, is_terminator_def, Excl "isPREFIX"]) >>
  `COUNT_LIST 1 = [0]` by EVAL_TAC >>
  Cases_on `loc = LocStorage` >>
  gvs[Abbr `r`, Abbr `q`, Abbr `val`, Abbr `a`,
    store_copy_frame_def, store_copy_normalize_def, store_copy_prefix_def,
    COUNT_LIST_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
    sstore_def, tstore_def, Excl "isPREFIX"] >>
  simp[venom_state_component_equality, WORD_ADD_0, WORD_MULT_CLAUSES]
QED

Theorem place_dyn_address_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var ctr;Lit (n2w ems)] [mv];
     mk_inst (id+1) ADD [Lit 32w;Var mv] [ov];
     mk_inst (id+2) ADD [src;Var ov] [sv];
     mk_inst (id+3) MUL [Var ctr;Lit (n2w ew)] [km];
     mk_inst (id+4) ADD [Lit 1w;Var km] [kv];
     mk_inst (id+5) ADD [dst;Var kv] [dv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  eval_operand (Var ctr) s = SOME (n2w j) /\ not_fresh_at sa ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  ALL_DISTINCT [mv;ov;sv;km;kv;dv] /\
  (!x. not_fresh_at sa x ==> ~MEM x [mv;ov;sv;km;kv;dv]) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      eval_operand (Var sv) t = SOME (b+32w+n2w j*n2w ems) /\
      eval_operand (Var dv) t = SOME (k+1w+n2w j*n2w ew) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+6
Proof
  strip_tac >>
  qabbrev_tac `a = n2w j * n2w ems : bytes32` >>
  qabbrev_tac `d = n2w j * n2w ew : bytes32` >>
  qabbrev_tac `r = update_var dv (k+1w+d)
    (update_var kv (1w+d) (update_var km d
      (update_var sv (b+32w+a) (update_var ov (32w+a) (update_var mv a s)))))` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    (fs[ALL_DISTINCT] >>
     `!x. MEM x [mv;ov;sv;km;kv;dv] ==>
       src <> Var x /\ dst <> Var x /\ ctr <> x` by
       (simp[] >> rpt strip_tac >> metis_tac[]) >>
     simp[Abbr `code`, Abbr `r`, Abbr `a`, Abbr `d`,
       run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``MUL``,
       stepInstBaseLib.simp_opcode_clause ``ADD``,
       exec_pure2_def, slot_copy_operand_update, eval_operand_lit,
       eval_operand_update_var_local, WORD_ADD_ASSOC]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+6` >>
  conj_tac >- simp[gas_marked_path_def] >>
  gvs[Abbr `r`, Abbr `a`, Abbr `d`, store_copy_normalize_def,
    update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    Excl "isPREFIX"] >> metis_tac[]
QED

Theorem place_dyn_increment_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id ADD [Var ctr;Lit 1w] [nv];
     mk_inst (id+1) ASSIGN [Var nv] [ctr]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand (Var ctr) s = SOME (n2w j) /\ ctr <> nv /\
  (!x. not_fresh_at sa x ==> x <> nv) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t = s /\
      (!x. not_fresh_at sa x /\ x <> ctr ==>
           lookup_var x t = lookup_var x s) /\
      eval_operand (Var ctr) t = SOME (n2w (j+1)) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+2
Proof
  strip_tac >>
  qabbrev_tac `r = update_var ctr (n2w j+1w)
    (update_var nv (n2w j+1w) s)` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    simp[Abbr `code`, Abbr `r`, run_inst_seq_def, mk_inst_def,
      stepInstBaseLib.simp_opcode_clause ``ADD``,
      stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
      exec_pure2_def, eval_operand_lit, eval_operand_update_var_local] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+2` >>
  conj_tac >- simp[gas_marked_path_def] >>
  gvs[Abbr `r`, store_copy_normalize_def, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE,
    GSYM word_add_n2w, Excl "isPREFIX"] >> metis_tac[]
QED

Theorem place_dyn_body_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if ew = 1 then
     ?mul off sp value slot dp b1 b2 b3 b4 b5 b6.
       emit_op MUL [Var ctr;Lit 32w] stb = (mul,b1) /\
       emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
       emit_op ADD [src;off] b2 = (sp,b3) /\
       emit_op MLOAD [sp] b3 = (value,b4) /\
       emit_op ADD [Var ctr;Lit 1w] b4 = (slot,b5) /\
       emit_op ADD [dst;slot] b5 = (dp,b6) /\
       emit_void (if loc = LocStorage then SSTORE else TSTORE) [dp;value]
         b6 = ((),ste)
   else
     ?mul off sp smul slot dp oldcopy b1 b2 b3 b4 b5 b6.
       emit_op MUL [Var ctr;Lit (n2w ems)] stb = (mul,b1) /\
       emit_op ADD [Lit 32w;mul] b1 = (off,b2) /\
       emit_op ADD [src;off] b2 = (sp,b3) /\
       emit_op MUL [Var ctr;Lit (n2w ew)] b3 = (smul,b4) /\
       emit_op ADD [Lit 1w;smul] b4 = (slot,b5) /\
       emit_op ADD [dst;slot] b5 = (dp,b6) /\
       compile_word_copy_loop sp dp ew LocMemory loc F b6 = (oldcopy,ste) /\
       fn_has_code b6 ste func) /\
  fn_has_code stb ste func /\ ew < dimword (:256) /\
  (ew = 1 ==> ems = 32) /\
  not_fresh_at stb ctr /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x) /\
  eval_operand src q = SOME b /\ eval_operand dst q = SOME k /\
  eval_operand (Var ctr) q = SOME (n2w j) /\
  ~q.vs_halted /\ ~q.vs_call_ctx.cc_static /\
  q.vs_current_bb = stb.cs_current_bb /\
  q.vs_inst_idx = LENGTH stb.cs_current_insts ==>
  ?r. gas_marked_path F ctx func q 0 (OK r) /\
      store_copy_frame stb loc (b+32w+n2w j*n2w ems)
        (k+1w+n2w j*n2w ew) q ew r /\
      ~r.vs_halted /\ r.vs_current_bb = ste.cs_current_bb /\
      r.vs_inst_idx = LENGTH ste.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  Cases_on `ew = 1`
  >- suspend "single"
  >> suspend "multi"
QED

Resume place_dyn_body_path[single]:
  fs[COND_CLAUSES] >>
  Cases_on `loc = LocStorage`
  >- (fs[] >>
      drule_all (place_dyn_single_body_layout |> SPEC_ALL |>
        Q.INST [`transient` |-> `F`] |> REWRITE_RULE [COND_CLAUSES]) >>
      strip_tac >> suspend "single_backend") >>
  fs[] >>
  drule_all (place_dyn_single_body_layout |> SPEC_ALL |>
    Q.INST [`transient` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  strip_tac >> suspend "single_backend"
QED

Resume place_dyn_body_path[single_backend]:
  markerLib.RESUME_TAC >> (rpt strip_tac >>
  `?bb. lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts stb ste) (DROP q.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, Excl "isPREFIX"] >>
     gvs[IS_PREFIX_APPEND, Excl "isPREFIX"] >>
     qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
     simp[emitted_insts_def, DROP_APPEND, DROP_LENGTH_APPEND,
       IS_PREFIX_APPEND] >> metis_tac[]) >>
  qpat_x_assum `isPREFIX (emitted_insts _ _) _` mp_tac >>
  simp[Excl "isPREFIX"] >>
  strip_tac >>
  `isPREFIX (emitted_insts stb ste) (DROP q.vs_inst_idx bb.bb_instructions)` by
    simp[Excl "isPREFIX"] >>
  qpat_assum `q.vs_inst_idx = _`
    (fn th => qpat_x_assum `isPREFIX (_::_::_::_::_::_::_::[]) _`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  Cases_on `loc = LocStorage`
  >- (FULL_SIMP_TAC bool_ss [] >> drule_all (place_dyn_single_body_path |> SPEC_ALL |>
        Q.INST [`loc` |-> `LocStorage`] |> REWRITE_RULE []) >>
      disch_then (qspec_then `ctx` strip_assume_tac) >> suspend "single_finish") >>
  FULL_SIMP_TAC bool_ss [] >>
  drule_all (place_dyn_single_body_path |> SPEC_ALL |>
    Q.INST [`loc` |-> `LocTransient`] |> REWRITE_RULE
      [compileEnvTheory.data_location_distinct, GSYM compileEnvTheory.data_location_distinct]) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> suspend "single_finish")
QED

Resume place_dyn_body_path[single_finish]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  qexists_tac `t` >> simp[WORD_MULT_CLAUSES] >>
  qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
  simp[emitted_insts_def] >>
  fs[same_blocks_def, IS_PREFIX_APPEND, Excl "isPREFIX"] >>
  simp[DROP_LENGTH_APPEND] >>
  disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Resume place_dyn_body_path[multi]:
  qpat_x_assum `if ew = 1 then _ else _` mp_tac >>
  simp[COND_CLAUSES] >> strip_tac >>
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
  `~t.vs_call_ctx.cc_static` by
    (qpat_x_assum `store_copy_normalize q t = q` mp_tac >>
     simp[store_copy_normalize_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >> simp[]) >>
  `t.vs_current_bb = b6.cs_current_bb /\
   t.vs_inst_idx = LENGTH b6.cs_current_insts` by
    (fs[same_blocks_def, IS_PREFIX_APPEND, Excl "isPREFIX"] >>
     qpat_x_assum `emitted_insts _ _ = _` mp_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `eval_operand sp t = SOME (b+32w+n2w j*n2w ems) /\
   eval_operand dp t = SOME (k+1w+n2w j*n2w ew)` by metis_tac[] >>
  drule_all place_store_copy_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t'` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  simp[] >>
  drule place_store_frame_normalize >>
  disch_then (qspec_then `q` assume_tac) >>
  simp[store_copy_frame_def] >>
  qpat_x_assum `store_copy_frame b6 _ _ _ _ _ _` mp_tac >>
  simp[store_copy_frame_def] >> metis_tac[]
QED

Finalise place_dyn_body_path

Theorem place_dyn_body_prefix:
  store_copy_frame stb loc (b+32w+n2w j*n2w ems)
    (k+1w+n2w j*n2w ew) q ew r /\
  store_copy_normalize s0 q = place_dyn_prefix loc b k ew ems s0 j /\
  not_fresh_at stb ctr /\
  (!x. len = Var x ==> not_fresh_at stb x) ==>
  store_copy_normalize s0 r = place_dyn_prefix loc b k ew ems s0 (SUC j) /\
  (!x. not_fresh_at stb x ==> lookup_var x r = lookup_var x q) /\
  eval_operand (Var ctr) r = eval_operand (Var ctr) q /\
  eval_operand len r = eval_operand len q
Proof
  strip_tac >> drule place_store_frame_normalize >>
  disch_then (qspec_then `s0` assume_tac) >>
  conj_tac >- simp[place_dyn_prefix_eqs] >>
  drule place_store_frame_fields >> strip_tac >>
  qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
  simp[store_copy_frame_def] >> strip_tac >>
  simp[eval_operand_def] >>
  Cases_on `len` >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem place_dyn_init_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id MLOAD [src] [lv];
            mk_inst (id+1) ASSIGN [Lit 0w] [ctr]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand src s = SOME b /\ lv <> ctr /\
  (!x. not_fresh_at sa x ==> x <> lv /\ x <> ctr) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      eval_operand (Var lv) t = SOME (mload (w2n b) s) /\
      eval_operand (Var ctr) t = SOME 0w /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 2
Proof
  strip_tac >>
  qabbrev_tac `r = update_var ctr 0w (update_var lv (mload (w2n b) s) s)` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    simp[Abbr `code`, Abbr `r`, run_inst_seq_def, mk_inst_def,
      stepInstBaseLib.simp_opcode_clause ``MLOAD``,
      stepInstBaseLib.simp_opcode_clause ``ASSIGN``, exec_read1_def,
      eval_operand_lit] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+2` >>
  conj_tac >- simp[gas_marked_path_def] >>
  gvs[Abbr `r`, store_copy_normalize_def, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, Excl "isPREFIX"] >>
  metis_tac[]
QED

Theorem place_dyn_test_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id LT [Var ctr;Var lv] [tv];
            mk_inst (id+1) ISZERO [Var tv] [dv]]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand (Var ctr) s = SOME (n2w j) /\
  eval_operand (Var lv) s = SOME (n2w n) /\
  j <= n /\ n < dimword (:256) /\ tv <> dv /\
  (!x. not_fresh_at sa x ==> x <> tv /\ x <> dv) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!x. x <> tv /\ x <> dv ==> lookup_var x t = lookup_var x s) /\
      eval_operand (Var dv) t = SOME (if j = n then 1w else 0w) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx + 2
Proof
  strip_tac >>
  `j < dimword (:256)` by decide_tac >>
  `bool_to_word ((n2w j:bytes32) <+ n2w n) =
    (if j = n then 0w else 1w)` by
    (Cases_on `j = n` >> simp[WORD_LO, LESS_MOD, bool_to_word_def] >>
     `j < n` by decide_tac >> simp[]) >>
  qabbrev_tac `r = update_var dv (if j = n then 1w else 0w)
    (update_var tv (if j = n then 0w else 1w) s)` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    (Cases_on `j = n` >>
     simp[Abbr `code`, Abbr `r`, run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``LT``,
       stepInstBaseLib.simp_opcode_clause ``ISZERO``, exec_pure2_def,
       exec_pure1_def, eval_operand_update_var_local, bool_to_word_def]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+2` >>
  conj_tac >- simp[gas_marked_path_def] >>
  gvs[Abbr `r`, store_copy_normalize_def, update_var_def,
    eval_operand_def, lookup_var_def, FLOOKUP_UPDATE, Excl "isPREFIX"] >>
  metis_tac[]
QED

Theorem place_dyn_length_store_path:
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id (if transient then TSTORE else SSTORE) [dst;len] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand dst s = SOME k /\ eval_operand len s = SOME nw ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!x. lookup_var x t = lookup_var x s) /\
      (!s0. store_copy_normalize s0 t =
        (if transient then tstore else sstore) k nw (store_copy_normalize s0 s)) /\
      ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
      t.vs_inst_idx = s.vs_inst_idx+1
Proof
  strip_tac >>
  qabbrev_tac `r = (if transient then tstore else sstore) k nw s` >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code s = OK r` by
    (Cases_on `transient` >>
     simp[Abbr `code`, Abbr `r`, run_inst_seq_def, mk_inst_def,
       stepInstBaseLib.simp_opcode_clause ``TSTORE``,
       stepInstBaseLib.simp_opcode_clause ``SSTORE``, exec_write2_def]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r with vs_inst_idx := s.vs_inst_idx+1` >>
  conj_tac >- (Cases_on `transient` >>
    gvs[gas_marked_path_def, is_terminator_def, Excl "isPREFIX"]) >>
  Cases_on `transient` >>
  simp[Abbr `r`, sstore_def, tstore_def, lookup_var_def, store_copy_normalize_def]
QED

Theorem place_dyn_header_path:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id LT [Var ctr;Var lv] [tv];
            mk_inst (id+1) ISZERO [Var tv] [dv];
            mk_inst (id+2) JNZ [Var dv;Label exit;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  eval_operand (Var ctr) s = SOME (n2w j) /\
  eval_operand (Var lv) s = SOME (n2w n) /\
  j <= n /\ n < dimword (:256) /\ tv <> dv /\
  (!x. not_fresh_at sa x ==> x <> tv /\ x <> dv) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      store_copy_normalize s t = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!x. x <> tv /\ x <> dv ==> lookup_var x t = lookup_var x s) /\
      ~t.vs_halted /\ t.vs_inst_idx = 0 /\
      t.vs_current_bb = (if j = n then exit else body_lbl)
Proof
  strip_tac >>
  qpat_assum `isPREFIX (_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst id LT [Var ctr;Var lv] [tv];
            mk_inst (id+1) ISZERO [Var tv] [dv]]
    (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all place_dyn_test_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb t.vs_inst_idx =
    SOME (mk_inst (id+2) JNZ [Var dv;Label exit;Label body_lbl] [])` by
    (qpat_assum `isPREFIX (_::_::_::[]) _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     qpat_assum `isPREFIX (_::_::[]) _`
       (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
     drule instruction_prefix_cursor >> simp[ADD1]) >>
  `gas_marked_path F ctx func t 0
    (OK (jump_to (if j = n then exit else body_lbl) t))` by
    (`lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all place_copy_branch_path >>
     disch_then (qspec_then `ctx` mp_tac) >>
     Cases_on `j = n` >> simp[]) >>
  qexists_tac `jump_to (if j = n then exit else body_lbl) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  gvs[jump_to_def, lookup_var_def, store_copy_normalize_def]
QED

Theorem place_dyn_storage_path:
  compile_dynarray_to_storage src dst ew ems transient sa = ((),sb) /\
  fn_has_code sa sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  mload (w2n b) s0 = n2w n /\ n < dimword (:256) /\
  ew < dimword (:256) /\ (ew = 1 ==> ems = 32) /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s0 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
      store_copy_normalize s0 t =
        (if transient then tstore else sstore) k (n2w n)
          (place_dyn_prefix (if transient then LocTransient else LocStorage)
            b k ew ems s0 n) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all place_dyn_execution_layout >> strip_tac >>
  qabbrev_tac `Inv = \j q.
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s0) /\
    store_copy_normalize s0 q =
      place_dyn_prefix (if transient then LocTransient else LocStorage)
        b k ew ems s0 j /\
    eval_operand (Var ctr) q = SOME (n2w j) /\
    eval_operand (Var lv) q = SOME (n2w n)` >>
  `?r. gas_marked_path F ctx func s0 0 (OK r) /\ Inv 0 r /\
       ~r.vs_halted /\ r.vs_current_bb = cond /\ r.vs_inst_idx = 0`
    by suspend "init" >>
  `?u. gas_marked_path F ctx func r 0 (OK u) /\ Inv n u /\
       ~u.vs_halted /\ u.vs_current_bb = exit /\ u.vs_inst_idx = 0`
    by suspend "loop" >>
  `?t. gas_marked_path F ctx func u 0 (OK t) /\
       (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
       store_copy_normalize s0 t =
         (if transient then tstore else sstore) k (n2w n)
           (place_dyn_prefix (if transient then LocTransient else LocStorage)
             b k ew ems s0 n) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts`
    by suspend "finish" >>
  qexists_tac `t` >> simp[] >>
  `gas_marked_path F ctx func r 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qpat_assum `gas_marked_path _ _ _ s0 0 (OK r)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED

Resume place_dyn_storage_path[init]:
  `lv <> ctr /\
   (!x. not_fresh_at sa x ==> x <> lv /\ x <> ctr)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `lookup_block s0.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst sa.cs_next_id MLOAD [src] [lv];
            mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]]
      (DROP s0.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX (mk_inst sa.cs_next_id MLOAD _ _::_) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
     simp[]) >>
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
    place_dyn_prefix_eqs, store_copy_normalize_def] >>
  gvs[eval_operand_def, lookup_var_def, store_copy_normalize_def]
QED
Resume place_dyn_storage_path[loop]:
  irule place_copy_iterate_path >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`0`, `n`] >> simp[]) >>
  qexists_tac `body_lbl` >> simp[] >>
  conj_tac >- suspend "body" >> suspend "header"
QED
Resume place_dyn_storage_path[header]:
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
Resume place_dyn_storage_path[finish]:
  qpat_x_assum `Inv n u` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `eval_operand dst u = SOME k` by
    (`u.vs_labels = s0.vs_labels` by
       (qpat_assum `store_copy_normalize s0 u = _`
          (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
        simp_tac (srw_ss()) [store_copy_normalize_def, place_dyn_prefix_fields]) >>
     Cases_on `dst` >> simp[eval_operand_def] >>
     fs[eval_operand_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `~u.vs_call_ctx.cc_static` by
    (qpat_assum `store_copy_normalize s0 u = _`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def, place_dyn_prefix_fields] >>
     simp[]) >>
  `lookup_block u.vs_current_bb func.fn_blocks = SOME bbx /\
   isPREFIX [mk_inst ix (if transient then TSTORE else SSTORE) [dst;Var lv] []]
     (DROP u.vs_inst_idx bbx.bb_instructions)` by simp[Excl "isPREFIX"] >>
  drule_all place_dyn_length_store_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED
Resume place_dyn_storage_path[body]:
  rpt strip_tac >>
  qpat_x_assum `Inv j q` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `q.vs_labels = s0.vs_labels /\
   q.vs_call_ctx = s0.vs_call_ctx` by
    (conj_tac >-
       (qpat_assum `store_copy_normalize s0 q = _`
          (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
        simp_tac (srw_ss()) [store_copy_normalize_def, place_dyn_prefix_fields]) >>
     qpat_assum `store_copy_normalize s0 q = _`
       (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def, place_dyn_prefix_fields]) >>
  `eval_operand src q = SOME b /\ eval_operand dst q = SOME k` by
    (qpat_assum `!x. src = Var x \/ dst = Var x ==> _` mp_tac >>
     qpat_assum `eval_operand src s0 = _` mp_tac >>
     qpat_assum `eval_operand dst s0 = _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x q = _` mp_tac >>
     qpat_assum `q.vs_labels = s0.vs_labels` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac
     >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
  `not_fresh_at stb ctr /\ not_fresh_at stb lv /\
   (!x. src = Var x \/ dst = Var x ==> not_fresh_at stb x)` by
    (fs[EVERY_DEF] >> metis_tac[]) >>
  `(if transient then LocTransient else LocStorage) = LocStorage \/
   (if transient then LocTransient else LocStorage) = LocTransient` by
    (Cases_on `transient` >> simp[]) >>
  `~q.vs_call_ctx.cc_static /\ q.vs_current_bb = stb.cs_current_bb /\
   q.vs_inst_idx = LENGTH stb.cs_current_insts` by simp[] >>
  qpat_assum `if ew = 1 then _ else _`
    (mp_then Any mp_tac place_dyn_body_path) >>
  simp[] >> disch_then (qspec_then `q` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`j`, `ctx`] mp_tac) >>
  `j < dimword (:256)` by decide_tac >> simp[] >>
  disch_then drule >> strip_tac >>
  rename1 `store_copy_frame stb _ _ _ q ew rb` >>
  `!x. Var lv = Var x ==> not_fresh_at stb x` by simp[] >>
  qpat_assum `store_copy_frame _ _ _ _ _ _ _`
    (mp_then Any mp_tac place_dyn_body_prefix) >>
  disch_then (qspecl_then [`s0`, `Var lv`, `ctr`] mp_tac) >>
  simp[] >> strip_tac >>
  `ctr <> nv /\ (!x. not_fresh_at ste x ==> x <> nv)` by metis_tac[] >>
  `lookup_block rb.vs_current_bb func.fn_blocks = SOME bbt /\
   isPREFIX [mk_inst it ADD [Var ctr;Lit 1w] [nv];
             mk_inst (it+1) ASSIGN [Var nv] [ctr]]
      (DROP rb.vs_inst_idx bbt.bb_instructions)` by
    (qpat_assum `isPREFIX (mk_inst it ADD _ _::_) _`
       (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >> simp[]) >>
  `eval_operand (Var ctr) rb = SOME (n2w j)` by metis_tac[] >>
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
    (qpat_assum `gas_marked_path _ _ _ q 0 (OK rb)`
       (mp_then Any mp_tac gas_marked_path_then) >>
     disch_then drule >> simp[]) >>
  `store_copy_normalize s0 (jump_to cond ri) =
   store_copy_normalize s0 rb` by
    (qpat_assum `store_copy_normalize rb ri = rb`
       (mp_tac o Q.AP_TERM `store_copy_normalize s0`) >>
     simp_tac (srw_ss()) [store_copy_normalize_def, jump_to_def]) >>
  simp[ADD1] >>
  FIRST [fs[ALL_DISTINCT, jump_to_def, eval_operand_def, lookup_var_def,
            Excl "isPREFIX"]] >>
  `ri.vs_current_bb = ste.cs_current_bb` by metis_tac[] >>
  qpat_assum `gas_marked_path _ _ _ q 0 (OK rb)`
    (mp_then Any mp_tac gas_marked_path_then) >>
  disch_then drule >> simp[]
QED
Finalise place_dyn_storage_path
