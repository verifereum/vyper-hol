(* The multiword branch of compile_dynarray_to_storage, including both loops. *)
Theory assignDynStorageCompiledPtr
Ancestors
  assignDynStorageDataPtr assignDynStorageRoundPtr assignTupleDynamicStoragePtr
  countedPtrLoop placeDynExecutionLayout placeDynCompile
  assignBasePtrStorageLoop assignBasePtrStoragePath
  fragExec fragGasSeqAbort fragGasPathPtr ptrDiscipline bodyPtrDefs
  context compileEnv exprLoweringProps loweringStateRelDefs emitHelperProps
  venomState venomInst venomExecSemantics stateFrame typedMemoryCopy
  words arithmetic list rich_list finite_map

Theorem dyn_storage_prefix_three[local]:
  isPREFIX [i0;i1;i2] (DROP n bb.bb_instructions) ==>
  get_instruction bb n = SOME i0 /\
  get_instruction bb (SUC n) = SOME i1 /\
  get_instruction bb (n+2) = SOME i2
Proof
  strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> simp[ADD1]
QED

Theorem dyn_storage_mono_trans[local]:
  ci_mono a b /\ ci_mono b c ==> ci_mono a c
Proof
  simp[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  irule cs_extends_trans >> qexists_tac `b` >> simp[]
QED

Theorem dyn_storage_code_split[local]:
  ci_mono a b /\ ci_mono b c /\ fn_has_code a c fn ==>
  fn_has_code a b fn /\ fn_has_code b c fn
Proof
  metis_tac[fn_has_code_split, ci_mono_def]
QED

Theorem dyn_storage_multi_compiled_counted:
  !tr root dst sa z sb fn s G tn ctx D PG a k n capacity ew ems.
    compile_dynarray_to_storage (Var root) dst ew ems tr sa = (z,sb) /\
    fn_has_code sa sb fn /\ not_fresh_at sa root /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
    eval_operand dst s = SOME k /\ op_taint tn dst = {} /\
    mload (w2n a) s = n2w n /\ mem_word_taint tn.t_mem (w2n a) = {} /\
    n < dimword (:256) /\ 0 < ew /\ ew <> 1 /\ ew < dimword (:256) /\
    ems = 32*ew /\ 32+n*ems <= capacity /\
    w2n a+32+n*ems < dimword (:256) /\
    ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf u v tv.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      assign_base_store_frame (if tr then LocTransient else LocStorage)
        (a+32w) (k+1w) s tn (n*ew) v tv /\
      u = ((if tr then tstore k (n2w n) v else sstore k (n2w n) v)
        with vs_inst_idx := 1) /\
      tf = (if tr then tv with t_trans := key_update tv.t_trans k {}
            else tv with t_stor := key_update tv.t_stor k {}) /\
      ptr_covers Gf tf root u capacity /\ lookup_var root u = SOME a /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
        FLOOKUP Gf x = FLOOKUP G x /\ op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `z` >>
  drule_all place_dyn_execution_layout >> strip_tac >>
  qpat_x_assum `if ew = 1 then _ else _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ASSUME ``ew <> 1``]) >>
  `ci_mono stb b1 /\ ci_mono b1 b2 /\ ci_mono b2 b3 /\
   ci_mono b3 b4 /\ ci_mono b4 b5 /\ ci_mono b5 b6 /\ ci_mono b6 ste` by
    (imp_res_tac typed_copy_emit_op_mono >>
     qspecl_then [`sp`, `dp`, `ew`, `LocMemory`,
       `if tr then LocTransient else LocStorage`, `F`, `b6`] mp_tac
       ci_mono_compile_word_copy_loop >> simp[]) >>
  `ci_mono stb b3 /\ ci_mono b3 b6 /\ ci_mono b3 ste` by
    metis_tac[dyn_storage_mono_trans] >>
  `fn_has_code stb b3 fn /\ fn_has_code b3 ste fn` by
    (irule dyn_storage_code_split >> simp[]) >>
  `fn_has_code b3 b6 fn` by
    metis_tac[dyn_storage_code_split] >>
  `ALL_DISTINCT [root;lv;ctr] /\ 32 <= capacity` by
    (conj_tac >- (fs[ALL_DISTINCT, Excl "isPREFIX"] >> metis_tac[]) >> decide_tac) >>
  `get_instruction bb0 s.vs_inst_idx =
      SOME (mk_inst sa.cs_next_id MLOAD [Var root] [lv]) /\
   get_instruction bb0 (SUC s.vs_inst_idx) =
      SOME (mk_inst (sa.cs_next_id+1) ASSIGN [Lit 0w] [ctr]) /\
   get_instruction bb0 (s.vs_inst_idx+2) =
      SOME (mk_inst (sa.cs_next_id+2) JMP [Label cond] [])` by
    (irule dyn_storage_prefix_three >> simp[Excl "isPREFIX"]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb0` by simp[] >>
  drule_all tuple_dynamic_storage_init_counted >>
  disch_then (qspecl_then [`D`, `PG`, `if tr then LocTransient else LocStorage`, `k`] mp_tac) >>
  disch_then (qx_choosel_then [`G1`, `tn1`, `s1`] strip_assume_tac) >>
  qabbrev_tac `Inv = \j H tt q.
    assign_base_store_frame (if tr then LocTransient else LocStorage)
      (a+32w) (k+1w) s tn (j*ew) q tt /\
    ptr_covers H tt root q capacity /\ lookup_var root q = SOME a /\
    eval_operand dst q = SOME k /\ op_taint tt dst = {} /\
    lookup_var lv q = SOME (n2w n) /\ FLOOKUP H lv = NONE /\
    op_taint tt (Var lv) = {} /\
    lookup_var ctr q = SOME (n2w j) /\ FLOOKUP H ctr = NONE /\
    op_taint tt (Var ctr) = {} /\ q.vs_labels = s1.vs_labels` >>
  `Inv 0 G1 tn1 s1` by
    (simp[Abbr `Inv`] >> Cases_on `dst` >>
     gvs[eval_operand_def, op_taint_def, execution_frame_def, Excl "isPREFIX"] >> metis_tac[]) >>
  `?G2 tn2 s2.
    gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2) /\
    Inv n G2 tn2 s2 /\ s2.vs_current_bb = exit /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x s2 = lookup_var x s1 /\
      FLOOKUP G2 x = FLOOKUP G1 x /\ op_taint tn2 (Var x) = op_taint tn1 (Var x))`
    by suspend "loop" >>
  suspend "finish"
QED

Resume dyn_storage_multi_compiled_counted[loop]:
  mp_tac (Q.INST [`P` |-> `Inv`, `keep` |-> `not_fresh_at sa`,
    `func` |-> `fn`, `hdr` |-> `cond`, `bodylbl` |-> `body_lbl`]
    (Q.SPECL [`n`, `0`, `s1`, `G1`, `tn1`] counted_ptr_loop_keep_remaining)) >>
  (impl_tac >- (simp[] >> conj_tac >- suspend "header" >> suspend "body")) >>
  disch_then ACCEPT_TAC
QED

Resume dyn_storage_multi_compiled_counted[header]:
  qx_genl_tac [`j`, `q`, `H`, `tt`] >> strip_tac >>
  qpat_x_assum `Inv j H tt q` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `lookup_block q.vs_current_bb fn.fn_blocks = SOME bbh /\
   get_instruction bbh q.vs_inst_idx = SOME (mk_inst ih LT [Var ctr;Var lv] [tv]) /\
   get_instruction bbh (SUC q.vs_inst_idx) = SOME (mk_inst (ih+1) ISZERO [Var tv] [dv]) /\
   get_instruction bbh (q.vs_inst_idx+2) =
      SOME (mk_inst (ih+2) JNZ [Var dv;Label exit;Label body_lbl] [])` by
    (mp_tac (Q.INST [`n` |-> `0`, `bb` |-> `bbh`,
       `i0` |-> `mk_inst ih LT [Var ctr;Var lv] [tv]`,
       `i1` |-> `mk_inst (ih+1) ISZERO [Var tv] [dv]`,
       `i2` |-> `mk_inst (ih+2) JNZ [Var dv;Label exit;Label body_lbl] []`]
       dyn_storage_prefix_three) >>
     (impl_tac >- simp[Excl "isPREFIX"]) >> strip_tac >> fs[]) >>
  `ALL_DISTINCT [ctr;lv;tv;dv]` by fs[ALL_DISTINCT] >>
  `root <> tv /\ root <> dv` by (fs[] >> metis_tac[]) >>
  drule_all tuple_dynamic_storage_header_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choosel_then [`H1`, `tt1`, `q1`] strip_assume_tac) >>
  qexistsl_tac [`H1`, `tt1`, `q1`] >> simp[] >>
  `ptr_covers H1 tt1 root q1 capacity /\ lookup_var root q1 = SOME a` by
    (irule assign_base_store_root_transport >> qexistsl_tac [`H`, `q`, `tt`] >>
     simp[] >> metis_tac[]) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
    (a+32w) (k+1w) s tn (j*ew) q1 tt1` by
    (irule assign_base_store_frame_preserve >> qexistsl_tac [`q`, `tt`] >> simp[]) >>
  simp[] >>
  fs[ALL_DISTINCT, execution_frame_def, Excl "isPREFIX"] >>
  Cases_on `dst` >> fs[eval_operand_def, op_taint_def] >> metis_tac[]
QED

Resume dyn_storage_multi_compiled_counted[body]:
  qx_genl_tac [`j`, `q`, `H`, `tt`] >> strip_tac >>
  qpat_x_assum `Inv j H tt q` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `not_fresh_at stb ctr /\ not_fresh_at stb root /\
   (!x. dst = Var x ==> not_fresh_at stb x) /\
   ~q.vs_call_ctx.cc_static /\ q.vs_current_bb = stb.cs_current_bb /\
   q.vs_inst_idx = LENGTH stb.cs_current_insts /\
   op_taint tt (Var root) = {}` by
    (fs[EVERY_DEF, assign_base_store_frame_def, ptr_covers_def,
        Excl "isPREFIX"] >> metis_tac[]) >>
  `SUC j <= n /\ 0 < ems` by (simp[] >> decide_tac) >>
  `j*ems+ems <= n*ems` by
    (qspecl_then [`SUC j`, `n`, `ems`]
       (fn th => mp_tac (MP th (ASSUME ``SUC j <= n``))) LESS_MONO_MULT >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [MULT_CLAUSES, ADD_COMM, MULT_COMM]) >>
  `32+j*ems < capacity /\ 32+j*ems+32*ew <= capacity /\
   w2n a+32+j*ems+32*ew < dimword (:256)` by decide_tac >>
  drule_all dyn_storage_multi_data_counted >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >>
  disch_then (qx_choosel_then [`H3`, `tt3`, `q3`] strip_assume_tac) >>
  suspend "round"
QED

Resume dyn_storage_multi_compiled_counted[round]:
  `a+32w+n2w (j*ew)*32w = a+n2w (32+j*ems) /\
   k+1w+n2w (j*ew) = k+n2w (1+j*ew)` by
    (qpat_assum `ems = 32*ew` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     strip_tac >> asm_simp_tac bool_ss
       [word_mul_n2w, word_add_n2w, GSYM WORD_ADD_ASSOC, MULT_ASSOC, MULT_COMM]) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
    ((a+32w)+n2w (j*ew)*32w) ((k+1w)+n2w (j*ew)) q tt ew q3 tt3` by
    metis_tac[] >>
  `ctr <> nv /\ lookup_var ctr q3 = SOME (n2w j) /\
   FLOOKUP H3 ctr = NONE /\ op_taint tt3 (Var ctr) = {}` by metis_tac[] >>
  `lookup_block q3.vs_current_bb fn.fn_blocks = SOME bbt /\
   get_instruction bbt q3.vs_inst_idx = SOME (mk_inst it ADD [Var ctr;Lit 1w] [nv]) /\
   get_instruction bbt (SUC q3.vs_inst_idx) = SOME (mk_inst (it+1) ASSIGN [Var nv] [ctr]) /\
   get_instruction bbt (q3.vs_inst_idx+2) = SOME (mk_inst (it+2) JMP [Label cond] [])` by
    (mp_tac (Q.INST [`n` |-> `LENGTH ste.cs_current_insts`, `bb` |-> `bbt`,
       `i0` |-> `mk_inst it ADD [Var ctr;Lit 1w] [nv]`,
       `i1` |-> `mk_inst (it+1) ASSIGN [Var nv] [ctr]`,
       `i2` |-> `mk_inst (it+2) JMP [Label cond] []`] dyn_storage_prefix_three) >>
     (impl_tac >- simp[Excl "isPREFIX"]) >> strip_tac >> fs[]) >>
  `assign_base_store_frame (if tr then LocTransient else LocStorage)
    (a+32w) (k+1w) s tn (j*ew) q tt` by
    (once_rewrite_tac[MULT_COMM] >> first_assum ACCEPT_TAC) >>
  drule_all (Q.INST [`keep` |-> `not_fresh_at stb`]
    (SPEC_ALL dyn_storage_multi_round_keep_counted)) >>
  disch_then (qx_choosel_then [`H4`, `tt4`, `q4`] strip_assume_tac) >>
  `ptr_covers H4 tt4 root q4 capacity /\ lookup_var root q4 = SOME a` by
    (irule assign_base_store_root_transport >> qexistsl_tac [`H`, `q`, `tt`] >>
     simp[] >> fs[ALL_DISTINCT, Excl "isPREFIX"] >> metis_tac[]) >>
  qexistsl_tac [`H4`, `tt4`, `q4`] >> simp[] >>
  simp[] >> fs[ALL_DISTINCT, EVERY_DEF, Excl "isPREFIX"] >>
  Cases_on `dst` >> fs[eval_operand_def, op_taint_def] >> metis_tac[]
QED

Resume dyn_storage_multi_compiled_counted[finish]:
  qpat_x_assum `Inv n G2 tn2 s2` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME bbx /\
   get_instruction bbx s2.vs_inst_idx =
      SOME (mk_inst ix (if tr then TSTORE else SSTORE) [dst;Var lv] []) /\
   eval_operand (Var lv) s2 = SOME (n2w n) /\ ~s2.vs_call_ctx.cc_static` by
    (simp[eval_operand_def] >> conj_tac
     >- (mp_tac (Q.INST [`i` |-> `mk_inst ix (if tr then TSTORE else SSTORE)
            [dst;Var lv] []`, `code` |-> `[]`, `k` |-> `0`, `bb` |-> `bbx`]
            instruction_prefix_cursor) >>
         (impl_tac >- simp[Excl "isPREFIX"]) >> simp[]) >>
     fs[assign_base_store_frame_def]) >>
  drule_all assign_base_storage_write_counted >>
  disch_then (qspecl_then [`G2`, `D`, `PG`] assume_tac) >>
  qexistsl_tac [`G2`, `s2`, `tn2`] >>
  conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
        (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
      disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  simp[] >> conj_tac
  >- (Cases_on `tr` >> gvs[ptr_covers_def, lookup_var_def, op_taint_def,
      sstore_def, tstore_def]) >>
  Cases_on `tr` >> simp[sstore_def, tstore_def, lookup_var_def, op_taint_def] >>
  gvs[lookup_var_def, op_taint_def] >> metis_tac[]
QED

Finalise dyn_storage_multi_compiled_counted
