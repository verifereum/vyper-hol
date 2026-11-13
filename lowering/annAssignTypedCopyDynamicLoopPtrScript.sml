(* Runtime-bound dynamic payload traversal and its compiler frontier. *)
Theory annAssignTypedCopyDynamicLoopPtr
Ancestors
  typedNormalizeDynarrayLoop annAssignTypedCopyFixedMetadataPtr
  annAssignTypedCopyArrayTraversalPtr typedMemoryCopy fragGasPathPtr
  bodyPtrDefs context compileEnv fragExec exprLoweringProps
  venomState venomInst venomExecSemantics words arithmetic list

Theorem annassign_dynamic_child_frontier:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?si se.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st si = ((),se) /\
    si.cs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    LENGTH si.cs_current_insts = 4 /\ si.cs_next_var = sa.cs_next_var+12 /\
    cs_extends sa si /\ cs_extends si se /\ cs_extends se sb /\
    fn_has_code si se fn /\
    (!j. j < 12 ==> not_fresh_at si ("%" ++ toString (sa.cs_next_var+j))) /\
    (!x j. not_fresh_at sa x ==> x <> "%" ++ toString (sa.cs_next_var+j)) /\
    (!x. not_fresh_at sa x ==> not_fresh_at si x) /\
    ALL_DISTINCT (GENLIST (\j. "%" ++ toString (sa.cs_next_var+j)) 12) /\
    (?body. lookup_block si.cs_current_bb fn.fn_blocks = SOME body /\
      isPREFIX si.cs_current_insts body.bb_instructions) /\
    (?back. lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
      back.bb_instructions = se.cs_current_insts ++
        typed_sa_backedge_insts se.cs_next_id
          ("%" ++ toString (sa.cs_next_var+5)) ("%" ++ toString se.cs_next_var)
          (fresh_label_output "typed_dyn_cond" sa.cs_next_label)) /\
    sb.cs_current_bb = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    sb.cs_current_insts = []
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  `cs_extends sc ec` by gvs[ci_mono_def] >>
  `?body. lookup_block sc.cs_current_bb fn.fn_blocks = SOME body /\
    isPREFIX sc.cs_current_insts body.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `?back. lookup_block ec.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id
        ("%" ++ toString (sa.cs_next_var+5)) ("%" ++ toString ec.cs_next_var)
        (fresh_label_output "typed_dyn_cond" sa.cs_next_label)` by
    (qpat_x_assum `fn_has_code ec sb fn` mp_tac >>
     simp[fn_has_code_def, emitted_blocks_def] >> strip_tac >>
     first_x_assum (qspec_then `HD sb.cs_blocks` mp_tac) >> simp[]) >>
  qexistsl_tac [`sc`,`ec`] >> simp[] >>
  `sa.cs_next_var+12 <= sc.cs_next_var` by simp[] >>
  drule annassign_generated_register_range >> strip_tac >>
  gvs[ci_mono_def]
QED

(* The payload boundary is tied to the generated dynamic-array program.
   Segment hypotheses expose resources, never preservation of a predicate. *)
Theorem annassign_dynamic_payload_loop:
  !D ctx fn PG ce dst_op dt cap src_op st sa sb si se
    bound ctr sr dr sp dp cond body exit f stv dtv src dst L G0 tn0 s0.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst_op dt cap src_op st sa = ((),sb) /\
    fn_has_code sa sb fn /\
    bound = "%" ++ toString sa.cs_next_var /\
    ctr = "%" ++ toString (sa.cs_next_var+5) /\
    sr = "%" ++ toString (sa.cs_next_var+3) /\
    dr = "%" ++ toString (sa.cs_next_var+4) /\
    sp = "%" ++ toString (sa.cs_next_var+10) /\
    dp = "%" ++ toString (sa.cs_next_var+11) /\
    cond = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    body = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    exit = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    compile_store_memory_typed ce (Var dp) dt (Var sp) st si = ((),se) /\
    si.cs_current_bb = body /\ LENGTH si.cs_current_insts = 4 /\
    si.cs_next_var = sa.cs_next_var+12 /\ cs_extends sa si /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    type_memory_bytes ce st = type_memory_size stv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    src + L * type_memory_size stv < dimword(:256) /\
    dst + L * type_memory_size dtv < dimword(:256) /\
    (src + L * type_memory_size stv <= dst \/
     dst + L * type_memory_size dtv <= src) /\ L < dimword(:256) /\
    (!i. i < L ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    s0.vs_current_bb = cond /\ s0.vs_inst_idx = 0 /\ ~s0.vs_halted /\
    lookup_var bound s0 = SOME (n2w L) /\ lookup_var ctr s0 = SOME 0w /\
    op_taint tn0 (Var bound) = {} /\ op_taint tn0 (Var ctr) = {} /\
    FLOOKUP G0 bound = NONE /\ FLOOKUP G0 ctr = NONE /\
    lookup_var sr s0 = SOME (n2w src) /\ lookup_var dr s0 = SOME (n2w dst) /\
    ptr_covers G0 tn0 sr s0 (L * type_memory_size stv) /\
    ptr_covers G0 tn0 dr s0 (L * type_memory_size dtv) /\
    (!i. i < L ==> !m. mem_agree_outside tn0.t_mem s0.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (* Runtime-bound test; both operands are clean scalars. *)
    (!k G tn s. k <= L /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\
      ~s.vs_halted /\ lookup_var ctr s = SOME (n2w k) /\
      lookup_var bound s = SOME (n2w L) /\
      op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
      FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = (if k<L then body else exit) /\
        t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w L) /\
        op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
        FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
        typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
        t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x))) /\
    (* Address generation preserves the scalar resources. *)
    (!k G tn s. k < L /\ s.vs_current_bb = body /\ s.vs_inst_idx = 0 /\
      ~s.vs_halted /\ lookup_var ctr s = SOME (n2w k) /\
      lookup_var bound s = SOME (n2w L) /\
      op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
      FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
      lookup_var sr s = SOME (n2w src) /\ lookup_var dr s = SOME (n2w dst) /\
      ptr_covers G tn sr s (L * type_memory_size stv) /\
      ptr_covers G tn dr s (L * type_memory_size dtv) ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = si.cs_current_bb /\
        t.vs_inst_idx = LENGTH si.cs_current_insts /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w k) /\ lookup_var bound t = SOME (n2w L) /\
        op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
        FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
        lookup_var sp t = SOME (n2w (src + k * type_memory_size stv)) /\
        lookup_var dp t = SOME (n2w (dst + k * type_memory_size dtv)) /\
        ptr_covers H tm sp t (type_memory_size stv) /\
        ptr_covers H tm dp t (type_memory_size dtv) /\
        typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
        t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x))) /\
    (* Recursive child: its ordinary old-register frame retains the scalars. *)
    (!k G tn s. k < L /\ s.vs_current_bb = si.cs_current_bb /\
      s.vs_inst_idx = LENGTH si.cs_current_insts /\ ~s.vs_halted /\
      lookup_var sp s = SOME (n2w (src + k * type_memory_size stv)) /\
      lookup_var dp s = SOME (n2w (dst + k * type_memory_size dtv)) /\
      ptr_covers G tn sp s (type_memory_size stv) /\
      ptr_covers G tn dp s (type_memory_size dtv) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv (f k) (src + k * type_memory_size stv) m) ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = se.cs_current_bb /\
        t.vs_inst_idx = LENGTH se.cs_current_insts /\ ~t.vs_halted /\
        typed_copy_state_frame sa (dst + k * type_memory_size dtv)
          (type_memory_size dtv) s t /\
        (!i. ~(dst + k * type_memory_size dtv <= i /\
               i < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at si x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv (f k) (dst + k * type_memory_size dtv) m)) /\
    (* Increment from the actual recursive-child exit. *)
    (!k G tn s. k < L /\ s.vs_current_bb = se.cs_current_bb /\
      s.vs_inst_idx = LENGTH se.cs_current_insts /\ ~s.vs_halted /\
      lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w L) /\
      op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
      FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE ==>
      ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = cond /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
        lookup_var ctr t = SOME (n2w (SUC k)) /\
        lookup_var bound t = SOME (n2w L) /\
        op_taint tm (Var ctr) = {} /\ op_taint tm (Var bound) = {} /\
        FLOOKUP H ctr = NONE /\ FLOOKUP H bound = NONE /\
        typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
        t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x))) ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 H tm (OK t) /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        typed_copy_index_prefix f dtv dst L L m) /\
      typed_copy_state_frame sa dst (L * type_memory_size dtv) s0 t /\
      (!i. ~(dst <= i /\ i < dst + L * type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
        (i IN tm.t_mem <=> i IN tn0.t_mem)) /\
      tm.t_stor = tn0.t_stor /\ tm.t_trans = tn0.t_trans /\ tm.t_imm = tn0.t_imm /\
      (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
        lookup_var x t = lookup_var x s0 /\ FLOOKUP H x = FLOOKUP G0 x /\
        op_taint tm (Var x) = op_taint tn0 (Var x))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound \/ x = ctr ==>
    not_fresh_at si x` by
    (`sa.cs_next_var+12 <= si.cs_next_var` by simp[] >>
     drule annassign_generated_register_range >> strip_tac >>
     qpat_x_assum `!j. j < 12 ==> _` mp_tac >>
     qpat_x_assum `!x. not_fresh_at sa x ==> not_fresh_at si x` mp_tac >>
     qpat_x_assum `bound = _` mp_tac >> qpat_x_assum `ctr = _` mp_tac >>
     qpat_x_assum `sr = _` mp_tac >> qpat_x_assum `dr = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt disch_tac >>
     map_every (fn j => qpat_assum `!j. j < 12 ==> _`
       (qspec_then j (assume_tac o SRULE []))) [`0`,`3`,`4`,`5`] >>
     metis_tac[ADD_COMM]) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`bound = _`, `ctr = _`, `sr = _`, `dr = _`, `sp = _`, `dp = _`,
     `cond = _`, `body' = _`, `exit = _`, `si.cs_current_bb = _`,
     `LENGTH si.cs_current_insts = _`, `si.cs_next_var = _`] >>
  qabbrev_tac `Frame = (\G tn s.
    typed_copy_state_frame sa dst (L * type_memory_size dtv) s0 s /\
    (!i. ~(dst <= i /\ i < dst + L * type_memory_size dtv) ==>
      mem_bytes_at i 1 s.vs_memory = mem_bytes_at i 1 s0.vs_memory /\
      (i IN tn.t_mem <=> i IN tn0.t_mem)) /\
    tn.t_stor = tn0.t_stor /\ tn.t_trans = tn0.t_trans /\ tn.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)))` >>
  qabbrev_tac `Regs = (\G tn s. !x. x = sr \/ x = dr \/ x = bound ==>
    lookup_var x s = lookup_var x s0 /\ FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x))` >>
  qabbrev_tac `Rep = (\k tn s.
    (!i. i < L ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      typed_copy_index_prefix f dtv dst L k m))` >>
  qabbrev_tac `Roots = (\G tn s.
    lookup_var sr s = SOME (n2w src) /\ lookup_var dr s = SOME (n2w dst) /\
    ptr_covers G tn sr s (L * type_memory_size stv) /\
    ptr_covers G tn dr s (L * type_memory_size dtv))` >>
  qabbrev_tac `NW = (\(G:string |-> num # num) tn s (H:string |-> num # num) tm t.
    typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)))` >>
  `!G tn s H tm t. NW G tn s H tm t ==>
    (Frame G tn s ==> Frame H tm t) /\
    (Regs G tn s ==> Regs H tm t) /\
    (Roots G tn s ==> Roots H tm t) /\
    (!k. Rep k tn s ==> Rep k tm t)` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `NW _ _ _ _ _ _` mp_tac >>
     simp[Abbr `NW`, Abbr `Frame`, Abbr `Regs`, Abbr `Roots`, Abbr `Rep`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[typed_copy_state_frame_trans, ptr_covers_def]) >>
  qabbrev_tac `Inv = (\k G tn s.
    k <= L /\ s.vs_current_bb = cond /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
    lookup_var ctr s = SOME (n2w k) /\ lookup_var bound s = SOME (n2w L) /\
    op_taint tn (Var ctr) = {} /\ op_taint tn (Var bound) = {} /\
    FLOOKUP G ctr = NONE /\ FLOOKUP G bound = NONE /\
    Frame G tn s /\ Regs G tn s /\ Roots G tn s /\ Rep k tn s)` >>
  qabbrev_tac `Q = (\H tm t. t.vs_current_bb = exit /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\ Rep L tm t /\
    Frame H tm t /\ Regs H tm t)` >>
  `!r k G tn s. L-k = r /\ Inv k G tn s ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\ Q H tm t`
    suffices_by
    (disch_then (qspecl_then [`L`,`0`,`G0`,`tn0`,`s0`] mp_tac) >>
     (impl_tac >- simp[Abbr `Inv`, Abbr `Frame`, Abbr `Regs`, Abbr `Roots`,
       Abbr `Rep`, typed_copy_index_prefix_def, typed_copy_state_frame_refl]) >>
     strip_tac >> qexistsl_tac [`H`,`tm`,`t`] >>
     qpat_x_assum `Q _ _ _` mp_tac >>
     simp[Abbr `Q`, Abbr `Rep`, Abbr `Frame`, Abbr `Regs`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  Induct >> map_every qx_gen_tac [`k`,`G`,`tn`,`s`] >> strip_tac >>
  qpat_x_assum `Inv k G tn s` mp_tac >>
  simp_tac std_ss [Abbr `Inv`] >> strip_tac
  >- suspend "zero" >>
  suspend "successor"
QED

Resume annassign_dynamic_payload_loop[zero]:
  `k = L` by decide_tac >>
  qpat_assum `!k G tn s. k <= L /\ _ ==> _`
    (qspecl_then [`k`,`G`,`tn`,`s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm`
    (qx_choose_then `t` strip_assume_tac))) >>
  `NW G tn s H tm t` by
    (simp[Abbr `NW`] >>
     qpat_x_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_x_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[Abbr `Q`] >>
  first_x_assum irule >> qpat_x_assum `Rep k tn s` mp_tac >> simp[]
QED

Resume annassign_dynamic_payload_loop[successor]:
  rename1 `L-k = SUC r` >>
  `k < L /\ L - SUC k = r /\ SUC k <= L` by decide_tac >>
  qpat_assum `!k G tn s. k <= L /\ _ ==> _`
    (qspecl_then [`k`,`G`,`tn`,`s`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G1` (qx_choose_then `tn1`
    (qx_choose_then `s1` strip_assume_tac))) >>
  `NW G tn s G1 tn1 s1` by
    (simp[Abbr `NW`] >>
     qpat_x_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `Frame G1 tn1 s1 /\ Regs G1 tn1 s1 /\ Roots G1 tn1 s1 /\ Rep k tn1 s1` by
    (qpat_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _` drule >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> simp[]) >>
  qpat_assum `!k G tn s. k < L /\ s.vs_current_bb = body' /\ _ ==> _`
    (qspecl_then [`k`,`G1`,`tn1`,`s1`] mp_tac) >>
  (impl_tac >- (simp[] >> qpat_x_assum `Roots G1 tn1 s1` mp_tac >>
    simp[Abbr `Roots`])) >>
  disch_then (qx_choose_then `G2` (qx_choose_then `tn2`
    (qx_choose_then `s2` strip_assume_tac))) >>
  `NW G1 tn1 s1 G2 tn2 s2` by
    (simp[Abbr `NW`] >>
     qpat_x_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `Frame G2 tn2 s2 /\ Regs G2 tn2 s2 /\ Roots G2 tn2 s2 /\ Rep k tn2 s2` by
    (qpat_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _`
      (qspecl_then [`G1`,`tn1`,`s1`,`G2`,`tn2`,`s2`] mp_tac) >>
     simp[] >> strip_tac >> simp[]) >>
  qpat_assum `!k G tn s. k < L /\ s.vs_current_bb = si.cs_current_bb /\ _ ==> _`
    (qspecl_then [`k`,`G2`,`tn2`,`s2`] mp_tac) >>
  (impl_tac >- (simp[] >> qpat_x_assum `Rep k tn2 s2` mp_tac >>
    simp[Abbr `Rep`])) >>
  disch_then (qx_choose_then `G3` (qx_choose_then `tn3`
    (qx_choose_then `s3` strip_assume_tac))) >>
  `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound \/ x = ctr ==>
    lookup_var x s3 = lookup_var x s2 /\ FLOOKUP G3 x = FLOOKUP G2 x /\
    op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (qpat_x_assum `!x. not_fresh_at si x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x \/ _ ==> not_fresh_at si x` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `Rep (SUC k) tn3 s3 /\ Frame G3 tn3 s3` by
    (qpat_x_assum `Frame G2 tn2 s2` mp_tac >>
     qpat_x_assum `Rep k tn2 s2` mp_tac >>
     simp_tac pure_ss [Abbr `Rep`, Abbr `Frame`] >> BETA_TAC >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     rewrite_tac[CONJ_ASSOC] >>
     irule (REWRITE_RULE [CONJ_ASSOC] annassign_robust_index_child_update) >>
     simp[] >> qexistsl_tac [`G2`, `s2`, `tn2`] >> simp[] >>
     rpt strip_tac >> metis_tac[]) >>
  suspend "backedge"
QED

Resume annassign_dynamic_payload_loop[backedge]:
  map_every (fn x => qpat_assum
    `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound \/ x = ctr ==> _`
    (qspec_then x (assume_tac o SRULE []))) [`sr`,`dr`,`bound`,`ctr`] >>
  `Regs G3 tn3 s3 /\ Roots G3 tn3 s3` by
    (qpat_x_assum `Regs G2 tn2 s2` mp_tac >>
     qpat_x_assum `Roots G2 tn2 s2` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound \/ x = ctr ==> _` mp_tac >>
     simp_tac pure_ss [Abbr `Regs`, Abbr `Roots`] >> BETA_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[ptr_covers_def] >> metis_tac[optionTheory.SOME_11]) >>
  qpat_assum `!k G tn s. k < L /\ s.vs_current_bb = se.cs_current_bb /\ _ ==> _`
    (qspecl_then [`k`,`G3`,`tn3`,`s3`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `G4` (qx_choose_then `tn4`
    (qx_choose_then `s4` strip_assume_tac))) >>
  `NW G3 tn3 s3 G4 tn4 s4` by
    (simp[Abbr `NW`] >>
     qpat_x_assum `!x. not_fresh_at sa x \/ x = sr \/ x = dr \/ x = bound ==> _`
       mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `Frame G4 tn4 s4 /\ Regs G4 tn4 s4 /\ Roots G4 tn4 s4 /\
    Rep (SUC k) tn4 s4` by
    (qpat_assum `!G tn s H tm t. NW _ _ _ _ _ _ ==> _`
      (qspecl_then [`G3`,`tn3`,`s3`,`G4`,`tn4`,`s4`] mp_tac) >>
     simp[] >> strip_tac >> simp[]) >>
  qpat_x_assum `!k G tn s. L-k = r /\ Inv k G tn s ==> _`
    (qspecl_then [`SUC k`,`G4`,`tn4`,`s4`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `H` (qx_choose_then `tm`
    (qx_choose_then `t` strip_assume_tac))) >>
  qexistsl_tac [`H`,`tm`,`t`] >> simp[] >>
  ntac 5 (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise annassign_dynamic_payload_loop
