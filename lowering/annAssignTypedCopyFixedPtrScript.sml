(* Conditional fixed-array normalization with counted pointer execution. *)
Theory annAssignTypedCopyFixedPtr
Ancestors
  annAssignTypedCopyFixedMetadataPtr annAssignTypedCopyFixedControlPtr
  annAssignTypedCopyArrayTraversalPtr annAssignTypedCopyAtomsPtr
  typedMemoryCopy bodyPtrStructLitMonotoneRepresentation typedCopyLoopLayoutPtr
  exprLoweringProps emitHelper venomExecSemantics venomInst
  context compileEnv fragExec fragGasPathPtr valueEncodingDefs valueEncoding
  venomState words arithmetic list bodyPtrDefs

(* The bulk compiler branch is a single memory copy, with its complete
   ambient resource frame.  tv describes the represented whole object. *)
Theorem annassign_sarray_bulk_counted[local]:
  !ce dst dt src st n sa sb fn s b a G tn D ctx PG tv v.
    compile_copy_sarray_typed ce (Var dst) dt (Var src) st n sa = ((),sb) /\
    type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt /\
    n * type_memory_bytes ce dt < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    ptr_covers G tn dst s (n * type_memory_bytes ce dt) /\
    ptr_covers G tn src s (n * type_memory_bytes ce dt) /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n * type_memory_bytes ce dt /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) (n * type_memory_bytes ce dt) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n b) m) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + n * type_memory_bytes ce dt) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_copy_memory (Var dst) (Var src) (n * type_memory_bytes ce dt) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  drule_all annassign_copy_memory_counted_ambient_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[]
QED

(* Resolve compiler layout once, before reasoning about runtime segments. *)
Theorem annassign_sarray_loop_instruction_locations[local]:
  !ce dst dt src st n sa sz fn.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
      ~is_abi_dynamic ce.ce_struct_fields dt) /\
    compile_copy_sarray_typed ce dst dt src st n sa = ((),sz) /\
    fn_has_code sa sz fn ==>
    ?si se entry test body back ctr lt done so doff sp dp cond bodylbl exit.
      compile_store_memory_typed ce (Var dp) dt (Var sp) st si = ((),se) /\
      fn_has_code si se fn /\ cs_extends sa si /\ cs_extends si se /\
      cs_extends se sz /\ si.cs_next_var = sa.cs_next_var+7 /\
      si.cs_current_bb = bodylbl /\ LENGTH si.cs_current_insts = 4 /\
      sz.cs_current_bb = exit /\ sz.cs_current_insts = [] /\
      ctr = "%" ++ toString sa.cs_next_var /\
      lt = "%" ++ toString (sa.cs_next_var+1) /\
      done = "%" ++ toString (sa.cs_next_var+2) /\
      so = "%" ++ toString (sa.cs_next_var+3) /\
      doff = "%" ++ toString (sa.cs_next_var+4) /\
      sp = "%" ++ toString (sa.cs_next_var+5) /\
      dp = "%" ++ toString (sa.cs_next_var+6) /\
      lookup_block sa.cs_current_bb fn.fn_blocks = SOME entry /\
      get_instruction entry (LENGTH sa.cs_current_insts) =
        SOME (mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr]) /\
      get_instruction entry (SUC (LENGTH sa.cs_current_insts)) =
        SOME (mk_inst (sa.cs_next_id+1) JMP [Label cond] []) /\
      lookup_block cond fn.fn_blocks = SOME test /\
      get_instruction test 0 =
        SOME (mk_inst (sa.cs_next_id+2) LT [Var ctr;Lit (n2w n)] [lt]) /\
      get_instruction test 1 =
        SOME (mk_inst (sa.cs_next_id+3) ISZERO [Var lt] [done]) /\
      get_instruction test 2 =
        SOME (mk_inst (sa.cs_next_id+4) JNZ
          [Var done;Label exit;Label bodylbl] []) /\
      lookup_block bodylbl fn.fn_blocks = SOME body /\
      get_instruction body 0 =
        SOME (mk_inst (sa.cs_next_id+5) MUL
          [Var ctr;Lit (n2w (type_memory_bytes ce st))] [so]) /\
      get_instruction body 1 =
        SOME (mk_inst (sa.cs_next_id+6) MUL
          [Var ctr;Lit (n2w (type_memory_bytes ce dt))] [doff]) /\
      get_instruction body 2 =
        SOME (mk_inst (sa.cs_next_id+7) ADD [src;Var so] [sp]) /\
      get_instruction body 3 =
        SOME (mk_inst (sa.cs_next_id+8) ADD [dst;Var doff] [dp]) /\
      lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
      get_instruction back (LENGTH se.cs_current_insts) =
        SOME (mk_inst se.cs_next_id ADD [Var ctr;Lit 1w]
          ["%" ++ toString se.cs_next_var]) /\
      get_instruction back (SUC (LENGTH se.cs_current_insts)) =
        SOME (mk_inst (se.cs_next_id+1) ASSIGN
          [Var ("%" ++ toString se.cs_next_var)] [ctr]) /\
      get_instruction back (LENGTH se.cs_current_insts+2) =
        SOME (mk_inst (se.cs_next_id+2) JMP [Label cond] [])
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
  `cs_extends si se` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`ce`, `Var dp`, `dt`, `Var sp`, `st`, `si`] mp_tac) >>
     pure_asm_rewrite_tac [pairTheory.SND] >>
     rewrite_tac[ci_mono_def] >> metis_tac[]) >>
  `cs_extends sa si /\ cs_extends se sz` by
    simp[cs_extends_def] >>
  qabbrev_tac `entry = HD sc.cs_blocks` >>
  qabbrev_tac `test = HD sb.cs_blocks` >>
  qabbrev_tac `back = HD sz.cs_blocks` >>
  `si.cs_blocks = test::entry::sa.cs_blocks /\
   entry.bb_label = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts entry.bb_instructions /\
   sz.cs_blocks = back::se.cs_blocks /\
   back.bb_label = se.cs_current_bb /\
   isPREFIX se.cs_current_insts back.bb_instructions` by
    simp[Abbr `entry`, Abbr `test`, Abbr `back`] >>
  drule_all typed_copy_loop_slice_locations >> strip_tac >>
  qexistsl_tac [`si`, `se`, `entry`, `test`, `bb`, `back`,
    `ctr`, `lt`, `done`, `so`, `doff`, `sp`, `dp`, `cond`, `body'`, `exit`] >>
  simp[Abbr `entry`, Abbr `test`, Abbr `back`, get_instruction_def, EL_APPEND_EQN] >>
  qpat_x_assum `isPREFIX si.cs_current_insts bb.bb_instructions` mp_tac >>
  simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  gvs[get_instruction_def, EL_APPEND_EQN]
QED

Theorem annassign_sarray_indexed_counted_ptr:
  !ce dt st dtv stv N f dst src sa sb fn s b a G tn D ctx PG.
    compile_copy_sarray_typed ce (Var dst) dt (Var src) st N sa = ((),sb) /\
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\
      ~is_abi_dynamic ce.ce_struct_fields dt) /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    type_memory_bytes ce st = type_memory_size stv /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (N * type_memory_size stv) /\
    ptr_covers G tn dst s (N * type_memory_size dtv) /\
    N < dimword (:256) /\
    w2n a + N * type_memory_size stv < dimword (:256) /\
    w2n b + N * type_memory_size dtv < dimword (:256) /\
    (w2n a + N * type_memory_size stv <= w2n b \/
     w2n b + N * type_memory_size dtv <= w2n a) /\
    (!i m. i < N /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f i) (w2n a + i * type_memory_size stv) m) /\
    (!sc se xr yr u aw bw H tm v.
      compile_store_memory_typed ce (Var yr) dt (Var xr) st sc = ((),se) /\
      fn_has_code sc se fn /\ not_fresh_at sc xr /\ not_fresh_at sc yr /\
      u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
      lookup_var xr u = SOME aw /\ lookup_var yr u = SOME bw /\
      ptr_covers H tm xr u (type_memory_size stv) /\
      ptr_covers H tm yr u (type_memory_size dtv) /\
      w2n aw + type_memory_size stv < dimword (:256) /\
      w2n bw + type_memory_size dtv < dimword (:256) /\
      (w2n aw + type_memory_size stv <= w2n bw \/
       w2n bw + type_memory_size dtv <= w2n aw) /\
      val_wf stv v /\ val_wf dtv v /\
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory stv v (w2n aw) m) ==>
      ?K tk z. gas_path_ptr D 0 ctx fn PG H tm u 0 K tk (OK z) /\
        z.vs_current_bb = se.cs_current_bb /\
        z.vs_inst_idx = LENGTH se.cs_current_insts /\ ~z.vs_halted /\
        typed_copy_state_frame sc (w2n bw) (type_memory_size dtv) u z /\
        (!m. mem_agree_outside tk.t_mem z.vs_memory m ==>
          val_in_memory dtv v (w2n bw) m) /\
        tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
        (!x. not_fresh_at sc x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tk (Var x) = op_taint tm (Var x)) /\
        (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size dtv) ==>
          mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
          (i IN tk.t_mem <=> i IN tm.t_mem))) ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) (N * type_memory_size dtv) s t /\
      (!i m. i < N /\ mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv (f i) (w2n b + i * type_memory_size dtv) m) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + N * type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `!sc se xr yr u aw bw H tm v. _` (mk_asm "child") >>
  drule_all annassign_sarray_loop_instruction_locations >> strip_tac >>
  `sa.cs_next_var + 7 <= si.cs_next_var` by simp[] >>
  drule annassign_generated_register_range >> strip_tac >>
  `!x. not_fresh_at sa x ==> x <> ctr` by metis_tac[ADD_0] >>
  `?H0 tn1 s1.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H0 tn1 (OK s1) /\
    s1.vs_current_bb = cond /\ s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    lookup_var ctr s1 = SOME 0w /\ op_taint tn1 (Var ctr) = {} /\
    typed_copy_state_frame sa (w2n b) (N * type_memory_size dtv) s s1 /\
    s1.vs_memory = s.vs_memory /\ tn1.t_mem = tn.t_mem /\
    tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. x <> ctr ==> lookup_var x s1 = lookup_var x s /\
      FLOOKUP H0 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))` by
    (irule annassign_loop_entry_resources >>
     conj_tac >- metis_tac[] >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexistsl_tac [`entry`, `sa.cs_next_id`] >> simp[]) >>
  qabbrev_tac `Frame = (\H tm t.
    typed_copy_state_frame sa (w2n b) (N * type_memory_size dtv) s t /\
    (!i. ~(w2n b <= i /\ i < w2n b + N * type_memory_size dtv) ==>
      mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
      (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)))` >>
  qabbrev_tac `Rep = (\k tm t.
    (!i. i < N ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory stv (f i) (w2n a + i * type_memory_size stv) m) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      typed_copy_index_prefix f dtv (w2n b) N k m))` >>
  qabbrev_tac `Roots = (\H tm t.
    lookup_var src t = SOME a /\ lookup_var dst t = SOME b /\
    ptr_covers H tm src t (N * type_memory_size stv) /\
    ptr_covers H tm dst t (N * type_memory_size dtv))` >>
  `?H tm t. gas_path_ptr D 0 ctx fn PG H0 tn1 s1 0 H tm (OK t) /\
    t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    Roots H tm t /\ Rep N tm t /\ Frame H tm t` suffices_by
    (strip_tac >> qexistsl_tac [`H`, `tm`, `t`] >>
     conj_tac >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
     gvs[Abbr `Frame`, Abbr `Rep`, typed_copy_index_prefix_def] >> metis_tac[]) >>
  qabbrev_tac `NW = (\(H : string |-> num # num) tm t K tk u.
    typed_copy_state_frame sa (w2n b) (N * type_memory_size dtv) t u /\
    u.vs_memory = t.vs_memory /\ tk.t_mem = tm.t_mem /\
    tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
    (!x. not_fresh_at sa x \/ x = src \/ x = dst ==>
      lookup_var x u = lookup_var x t /\ FLOOKUP K x = FLOOKUP H x /\
      op_taint tk (Var x) = op_taint tm (Var x)))` >>
  qabbrev_tac `Inv = (\k H tm t. k <= N /\ t.vs_current_bb = cond /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
    Roots H tm t /\ Rep k tm t /\ Frame H tm t)` >>
  irule annassign_index_counted_traversal >>
  qexistsl_tac [`G`, `Inv`, `NW`, `bodylbl`, `0`, `cond`, `0`, `ctr`,
    `dp`, `dst`, `w2n b`, `dtv`, `bodylbl`, `4`, `f`, `0`,
    `se.cs_current_bb`, `LENGTH se.cs_current_insts`, `s`, `sa`,
    `sp`, `src`, `w2n a`, `stv`, `tn`] >>
  simp[Abbr `Frame`, Abbr `Rep`, Abbr `Roots`, Abbr `NW`, Abbr `Inv`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `ALL_DISTINCT [ctr;lt;done;so;doff;sp;dp]` by
       (qpat_x_assum `ALL_DISTINCT (GENLIST _ 7)` mp_tac >>
        simp[GENLIST, ALL_DISTINCT]) >>
     `ALL_DISTINCT [so;doff;sp;dp]` by fs[ALL_DISTINCT] >>
     `(!v. MEM v [so;doff;sp;dp] ==> ctr <> v /\ src <> v /\ dst <> v) /\
      (!v. not_fresh_at sa v ==> ~MEM v [so;doff;sp;dp])` by
       (qpat_x_assum `child :- _` kall_tac >>
        fs[MEM, ALL_DISTINCT] >> metis_tac[ADD_COMM]) >>
     `k * type_memory_size stv < N * type_memory_size stv /\
      k * type_memory_size stv + type_memory_size stv <= N * type_memory_size stv /\
      k * type_memory_size dtv < N * type_memory_size dtv /\
      k * type_memory_size dtv + type_memory_size dtv <= N * type_memory_size dtv` by
       simp[abiDecoderArraySliceTheory.abi_decoder_array_cell_capacity] >>
     `w2n a + k * type_memory_size stv < dimword (:256) /\
      w2n b + k * type_memory_size dtv < dimword (:256)` by decide_tac >>
     `?H tm t.
       gas_path_ptr D 0 ctx fn PG G' tn' s'' 0 H tm (OK t) /\
       t.vs_current_bb = s''.vs_current_bb /\ t.vs_inst_idx = s''.vs_inst_idx+4 /\
       ~t.vs_halted /\ lookup_var ctr t = SOME (n2w k) /\
       op_taint tm (Var ctr) = {} /\
       lookup_var sp t = SOME (n2w (w2n a+k*type_memory_size stv)) /\
       lookup_var dp t = SOME (n2w (w2n b+k*type_memory_size dtv)) /\
       ptr_covers H tm sp t (type_memory_size stv) /\
       ptr_covers H tm dp t (type_memory_size dtv) /\
       typed_copy_state_frame sa (w2n b) (N*type_memory_size dtv) s'' t /\
       t.vs_memory = s''.vs_memory /\ tm.t_mem = tn'.t_mem /\
       tm.t_stor = tn'.t_stor /\ tm.t_trans = tn'.t_trans /\ tm.t_imm = tn'.t_imm /\
       (!x. ~MEM x [so;doff;sp;dp] ==> lookup_var x t = lookup_var x s'' /\
         FLOOKUP H x = FLOOKUP G' x /\ op_taint tm (Var x) = op_taint tn' (Var x))` by
       (irule annassign_loop_address_resources >>
        simp[] >> qexistsl_tac [`N*type_memory_size stv`,
          `N*type_memory_size dtv`, `dst`, `sa.cs_next_id+5`, `src`] >>
        simp[ADD_ASSOC]) >>
     qexistsl_tac [`H`,`tm`,`t`] >>
     qpat_x_assum `child :- _` kall_tac >>
     gvs[] >> gen_tac >> disch_tac >>
     qpat_x_assum `!x. _ ==> lookup_var x t = _ /\ _` irule >>
     qpat_x_assum `!v. v = _ \/ _ ==> _` (qspec_then `x` mp_tac) >>
     Cases_on `not_fresh_at sa x` >> gvs[] >> metis_tac[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at si sp /\ not_fresh_at si dp /\ not_fresh_at si ctr` by
       (qpat_assum `!j. j < 7 ==> not_fresh_at si _`
          (qspec_then `5` assume_tac) >>
        qpat_assum `!j. j < 7 ==> not_fresh_at si _`
          (qspec_then `6` assume_tac) >>
        qpat_assum `!j. j < 7 ==> not_fresh_at si _`
          (qspec_then `0` assume_tac) >>
        gvs[ADD_COMM]) >>
     `k*type_memory_size stv + type_memory_size stv <= N*type_memory_size stv /\
      k*type_memory_size dtv + type_memory_size dtv <= N*type_memory_size dtv` by
       simp[abiDecoderArraySliceTheory.abi_decoder_array_cell_capacity] >>
     `w2n a+k*type_memory_size stv < dimword (:256) /\
      w2n b+k*type_memory_size dtv < dimword (:256)` by decide_tac >>
     asm "child" (qspecl_then [`si`,`se`,`sp`,`dp`] mp_tac) >>
     disch_then (qspec_then `s''` mp_tac) >>
     disch_then (qspecl_then [`n2w (w2n a+k*type_memory_size stv)`,
       `n2w (w2n b+k*type_memory_size dtv)`] mp_tac) >>
     disch_then (qspecl_then [`G'`,`tn'`,`f k`] mp_tac) >>
     impl_tac >- (simp[] >> decide_tac) >>
     strip_tac >> qexistsl_tac [`K'`,`tk`,`z`] >>
     qpat_x_assum `child :- _` kall_tac >>
     gvs[] >>
     (conj_tac >-
       (qpat_x_assum `typed_copy_state_frame si _ _ _ _` mp_tac >>
        simp[typed_copy_state_frame_def] >> strip_tac >> simp[] >>
        rpt strip_tac >> first_x_assum irule >> simp[]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     qpat_x_assum `!x. not_fresh_at si x ==> lookup_var x z = _ /\ _` irule >>
     metis_tac[])) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `si.cs_next_var <= se.cs_next_var` by
       (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
        disch_then (qspecl_then [`ce`,`Var dp`,`dt`,`Var sp`,`st`,`si`] mp_tac) >>
        simp[ci_mono_def]) >>
     `(!x. not_fresh_at sa x \/ x = src \/ x = dst ==>
         x <> ctr /\ x <> STRCAT "%" (toString se.cs_next_var)) /\
      ctr <> STRCAT "%" (toString se.cs_next_var)` by
       (qpat_x_assum `child :- _` kall_tac >>
        `sa.cs_next_var <= se.cs_next_var` by decide_tac >>
        `!x. not_fresh_at sa x ==> x <> STRCAT "%" (toString se.cs_next_var)` by
          (gen_tac >> disch_tac >>
           qpat_x_assum `not_fresh_at sa x` mp_tac >>
           simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
           disch_then (qspec_then `se.cs_next_var` mp_tac) >> simp[]) >>
        `not_fresh_at si ctr` by metis_tac[ADD_0, DECIDE ``0 < 7``] >>
        `ctr <> STRCAT "%" (toString se.cs_next_var)` by
          (qpat_x_assum `not_fresh_at si ctr` mp_tac >>
           simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
           disch_then (qspec_then `se.cs_next_var` mp_tac) >> simp[]) >>
        metis_tac[]) >>
     `?H tm t.
       gas_path_ptr D 0 ctx fn PG G' tn' s'' 0 H tm (OK t) /\
       t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       lookup_var ctr t = SOME (n2w (k+1)) /\ op_taint tm (Var ctr) = {} /\
       typed_copy_state_frame sa (w2n b) (N*type_memory_size dtv) s'' t /\
       t.vs_memory = s''.vs_memory /\ tm.t_mem = tn'.t_mem /\
       tm.t_stor = tn'.t_stor /\ tm.t_trans = tn'.t_trans /\ tm.t_imm = tn'.t_imm /\
       (!x. x <> ctr /\ x <> STRCAT "%" (toString se.cs_next_var) ==>
         lookup_var x t = lookup_var x s'' /\ FLOOKUP H x = FLOOKUP G' x /\
         op_taint tm (Var x) = op_taint tn' (Var x))` by
       (irule annassign_loop_backedge_resources >> simp[] >>
        metis_tac[]) >>
     qexistsl_tac [`H`,`tm`,`t`] >>
     qpat_x_assum `child :- _` kall_tac >>
     gvs[ADD1] >> gen_tac >> disch_tac >>
     qpat_x_assum `!x. x <> _ /\ x <> _ ==> lookup_var x t = _ /\ _` irule >>
     metis_tac[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `ALL_DISTINCT [ctr;lt;done]` by
       (qpat_x_assum `ALL_DISTINCT (GENLIST _ 7)` mp_tac >>
        simp[GENLIST, ALL_DISTINCT]) >>
     `!x. not_fresh_at sa x \/ x = src \/ x = dst ==> x <> lt /\ x <> done` by
       (qpat_x_assum `child :- _` kall_tac >> metis_tac[]) >>
     `?H tm t.
       gas_path_ptr D 0 ctx fn PG G' tn' s'' 0 H tm (OK t) /\
       t.vs_current_bb = (if k<N then bodylbl else exit) /\
       t.vs_inst_idx = 0 /\ ~t.vs_halted /\
       lookup_var ctr t = SOME (n2w k) /\ op_taint tm (Var ctr) = {} /\
       typed_copy_state_frame sa (w2n b) (N*type_memory_size dtv) s'' t /\
       t.vs_memory = s''.vs_memory /\ tm.t_mem = tn'.t_mem /\
       tm.t_stor = tn'.t_stor /\ tm.t_trans = tn'.t_trans /\ tm.t_imm = tn'.t_imm /\
       (!x. x <> lt /\ x <> done ==> lookup_var x t = lookup_var x s'' /\
         FLOOKUP H x = FLOOKUP G' x /\ op_taint tm (Var x) = op_taint tn' (Var x))` by
       (irule annassign_loop_test_resources >> simp[] >>
        qexists_tac `sa.cs_next_id+2` >> simp[ADD_ASSOC]) >>
     qexistsl_tac [`H`,`tm`,`t`] >>
     qpat_x_assum `child :- _` kall_tac >>
     gvs[] >> gen_tac >> disch_tac >>
     qpat_x_assum `!x. x <> _ /\ x <> _ ==> lookup_var x t = _ /\ _` irule >>
     metis_tac[]) >>
  qpat_x_assum `child :- _` kall_tac >>
  `src <> ctr /\ dst <> ctr` by metis_tac[] >>
  qpat_assum `!x. x <> ctr ==> _` (qspec_then `src` mp_tac) >>
  qpat_assum `!x. x <> ctr ==> _` (qspec_then `dst` mp_tac) >>
  simp[] >> rpt strip_tac >>
  gvs[] >>
  metis_tac[annAssignPtrBytestringTheory.annassign_ptr_covers_frame_ptr]
QED

Theorem annassign_sarray_counted_ptr:
 !ce tenv dt st dtv stv N kvs dst src sa sb fn s b a G tn D ctx PG.
 compile_copy_sarray_typed ce (Var dst) dt (Var src) st N sa = ((),sb) /\
 type_memory_bytes ce dt = type_memory_size dtv /\
 type_memory_bytes ce st = type_memory_size stv /\
 type_widens_to tenv st dt /\
 evaluate_type tenv (ArrayT st (Fixed N)) = SOME (ArrayTV stv (Fixed N)) /\
 evaluate_type tenv (ArrayT dt (Fixed N)) = SOME (ArrayTV dtv (Fixed N)) /\
 value_has_type (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
 val_wf (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) /\
 val_wf (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
 ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (N * type_memory_size stv) /\
 ptr_covers G tn dst s (N * type_memory_size dtv) /\
 N < dimword (:256) /\
 w2n a + N * type_memory_size stv < dimword (:256) /\
 w2n b + N * type_memory_size dtv < dimword (:256) /\
 (w2n a + N * type_memory_size stv <= w2n b \/
  w2n b + N * type_memory_size dtv <= w2n a) /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n a) m) /\
 (!sc se xr yr u aw bw H tm v.
   compile_store_memory_typed ce (Var yr) dt (Var xr) st sc = ((),se) /\
   fn_has_code sc se fn /\ not_fresh_at sc xr /\ not_fresh_at sc yr /\
   u.vs_current_bb = sc.cs_current_bb /\
   u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
   lookup_var xr u = SOME aw /\ lookup_var yr u = SOME bw /\
   ptr_covers H tm xr u (type_memory_size stv) /\
   ptr_covers H tm yr u (type_memory_size dtv) /\
   w2n aw + type_memory_size stv < dimword (:256) /\
   w2n bw + type_memory_size dtv < dimword (:256) /\
   (w2n aw + type_memory_size stv <= w2n bw \/
    w2n bw + type_memory_size dtv <= w2n aw) /\
   val_wf stv v /\ val_wf dtv v /\
   (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?K tk z. gas_path_ptr D 0 ctx fn PG H tm u 0 K tk (OK z) /\
     z.vs_current_bb = se.cs_current_bb /\
     z.vs_inst_idx = LENGTH se.cs_current_insts /\ ~z.vs_halted /\
     typed_copy_state_frame sc (w2n bw) (type_memory_size dtv) u z /\
     (!m. mem_agree_outside tk.t_mem z.vs_memory m ==>
       val_in_memory dtv v (w2n bw) m) /\
     tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
     (!x. not_fresh_at sc x ==>
       lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
       op_taint tk (Var x) = op_taint tm (Var x)) /\
     (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size dtv) ==>
       mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
       (i IN tk.t_mem <=> i IN tm.t_mem))) ==>
 ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
   t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
   typed_copy_state_frame sa (w2n b) (N * type_memory_size dtv) s t /\
   (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
     val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n b) m) /\
   tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
   (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + N * type_memory_size dtv) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
     (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
 rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
 qpat_x_assum `!sc se xr yr u aw bw H tm v. _` (mk_asm "child") >>
 `evaluate_type tenv st = SOME stv /\ evaluate_type tenv dt = SOME dtv` by
   (imp_res_tac vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv >> gvs[]) >>
 Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\
   ~is_abi_dynamic ce.ce_struct_fields dt`
 >- (`stv = dtv` by metis_tac[typed_copy_static_widening] >>
     qpat_x_assum `child :- _` kall_tac >> gvs[] >>
     ( `N * type_memory_bytes ce dt < dimword (:256)` by (simp[] >> decide_tac) >>
       `val_footprint (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) <=
          N * type_memory_bytes ce dt` by
         simp[loweringPostsTheory.val_footprint_def, type_memory_size_def] >>
       drule annassign_sarray_bulk_counted >>
       disch_then (qspecl_then [`fn`,`s`,`b`,`a`,`G`,`tn`,`D`,`ctx`,`PG`,
         `ArrayTV dtv (Fixed N)`,`ArrayV (SArrayV kvs)`] mp_tac) >>
       simp[] >> metis_tac[])) >>
 `0 < type_memory_size stv /\ 0 < type_memory_size dtv` by
   metis_tac[annassign_evaluated_array_stride_positive] >>
 `val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs))
    (w2n a) s.vs_memory` by
   (qpat_x_assum `child :- _` kall_tac >>
    metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]) >>
 drule_all typed_copy_sarray_representation >> strip_tac >>
 qabbrev_tac `f = (\i. case ALOOKUP kvs i of NONE => default_value stv | SOME v => v)` >>
 `!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)` by
   (simp[Abbr `f`] >> metis_tac[]) >>
 `!i m. i < N /\ mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv (f i) (w2n a + i * type_memory_size stv) m` by
   (rpt strip_tac >> simp[Abbr `f`] >>
    qpat_x_assum `child :- _` kall_tac >>
    `val_in_memory (ArrayTV stv (Fixed N)) (ArrayV (SArrayV kvs)) (w2n a) m`
      by metis_tac[] >>
    drule_all typed_copy_sarray_representation >> metis_tac[]) >>
 asm_x "child" assume_tac >>
 drule_all annassign_sarray_indexed_counted_ptr >>
 strip_tac >>
 qexistsl_tac [`H`,`tm`,`t`] >> simp[] >>
 rpt strip_tac >>
 qpat_x_assum `!mem' dstoff. _` irule >>
 gvs[Abbr `f`] >> metis_tac[]
QED
