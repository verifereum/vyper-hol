(* Live-length typed-copy iteration over actual header and body locations. *)
Theory typedCopyReturnDynArrayLoopPtr
Ancestors typedCopyReturnControlFramePtr typedCopyReturnIndexBodyPtr
  typedCopyReturnLoopPtr typedCopyReturnArrayLayoutPtr annAssignPtrBytestring
  typedMemoryCopy fragGasPathPtr bodyPtrDefs compileEnv venomState
  venomInst ptrDiscipline words finite_map list arithmetic

Theorem typed_copy_dynarray_loop_counted:
  !ce tenv sty dty stv dtv D ctx PG.
  (!sc sd sp dp fn G tn s a b v.
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty sc = ((),sd) /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    not_fresh_at sc sp /\ not_fresh_at sc dp /\ fn_has_code sc sd fn /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sc.cs_current_bb /\
    s.vs_inst_idx = LENGTH sc.cs_current_insts /\
    lookup_var sp s = SOME a /\ lookup_var dp s = SOME b /\
    w2n a + type_memory_size stv < dimword(:256) /\
    w2n b + type_memory_size dtv < dimword(:256) /\
    regions_disjoint (w2n a) (type_memory_size stv) (w2n b) (type_memory_size dtv) /\
    op_taint tn (Var sp) = {} /\ op_taint tn (Var dp) = {} /\
    (type_memory_size stv <> 0 ==> ptr_covers G tn sp s (type_memory_size stv)) /\
    (type_memory_size dtv <> 0 ==> ptr_covers G tn dp s (type_memory_size dtv)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a) m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sd.cs_current_bb /\
      t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sc (w2n b) (type_memory_size dtv) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n b) m) /\
      (!j. j < w2n b \/ w2n b + type_memory_size dtv <= j ==>
        mem_byte_at t.vs_memory j = mem_byte_at s.vs_memory j /\
        (j IN tm.t_mem <=> j IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!p. not_fresh_at sc p ==> lookup_var p t = lookup_var p s /\
        FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p))) ==>
  !sa sb c1 c2 c3 si se ctr so doff src dst sp dp len lt done nv
    hdr exit hbb ebb hid eid fn G tn s a b f N src_span dst_span.
    emit_op MUL [Var ctr;Lit (n2w (type_memory_size stv))] sb = (Var so,c1) /\
    emit_op MUL [Var ctr;Lit (n2w (type_memory_size dtv))] c1 = (Var doff,c2) /\
    emit_op ADD [Var src;Var so] c2 = (Var sp,c3) /\
    emit_op ADD [Var dst;Var doff] c3 = (Var dp,si) /\
    compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se) /\
    fn_has_code sb c1 fn /\ fn_has_code c1 c2 fn /\
    fn_has_code c2 c3 fn /\ fn_has_code c3 si fn /\ fn_has_code si se fn /\
    lookup_block hdr fn.fn_blocks = SOME hbb /\
    get_instruction hbb 0 = SOME (mk_inst hid LT [Var ctr;Var len] [lt]) /\
    get_instruction hbb 1 = SOME (mk_inst (hid+1) ISZERO [Var lt] [done]) /\
    get_instruction hbb 2 = SOME (mk_inst (hid+2) JNZ [Var done;Label exit;Label sb.cs_current_bb] []) /\
    LENGTH sb.cs_current_insts = 0 /\
    lookup_block se.cs_current_bb fn.fn_blocks = SOME ebb /\
    get_instruction ebb (LENGTH se.cs_current_insts) =
      SOME (mk_inst eid ADD [Var ctr;Lit 1w] [nv]) /\
    get_instruction ebb (SUC (LENGTH se.cs_current_insts)) =
      SOME (mk_inst (eid+1) ASSIGN [Var nv] [ctr]) /\
    get_instruction ebb (LENGTH se.cs_current_insts+2) =
      SOME (mk_inst (eid+2) JMP [Label hdr] []) /\
    acyclic_struct_metadata ce.ce_struct_fields /\
    sfields_tenv_consistent ce.ce_struct_fields tenv /\
    (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
        sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    (!j. j < N ==> value_has_type stv (f j) /\ value_has_type dtv (f j) /\
      val_wf stv (f j) /\ val_wf dtv (f j)) /\
    sa.cs_next_var <= sb.cs_next_var /\
    (!p. not_fresh_at sa p ==> p <> ctr /\ p <> lt /\ p <> done /\ p <> nv) /\
    not_fresh_at sb ctr /\ not_fresh_at sb src /\ not_fresh_at sb dst /\ not_fresh_at sb len /\
    ALL_DISTINCT [ctr;lt;done;nv;len;src;dst] /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
    lookup_var ctr s = SOME 0w /\ lookup_var len s = SOME (n2w N) /\
    op_taint tn (Var ctr) = {} /\ FLOOKUP G ctr = NONE /\
    op_taint tn (Var len) = {} /\ FLOOKUP G len = NONE /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
    (src_span <> 0 ==> ptr_covers G tn src s src_span) /\
    (dst_span <> 0 ==> ptr_covers G tn dst s dst_span) /\
    N < dimword(:256) /\
    N * type_memory_size stv <= src_span /\ N * type_memory_size dtv <= dst_span /\
    w2n a + src_span < dimword(:256) /\ w2n b + dst_span < dimword(:256) /\
    regions_disjoint (w2n a) src_span (w2n b) dst_span /\
    (!j. j < N ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f j) (w2n a + j * type_memory_size stv) m) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      typed_copy_index_prefix f dtv (w2n b) N 0 m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) dst_span s t /\
      (!j. j < N ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory stv (f j) (w2n a + j * type_memory_size stv) m) /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        typed_copy_index_prefix f dtv (w2n b) N N m) /\
      (!j. j < w2n b \/ w2n b + dst_span <= j ==>
        mem_byte_at t.vs_memory j = mem_byte_at s.vs_memory j /\
        (j IN tm.t_mem <=> j IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!p. not_fresh_at sb p /\ p <> ctr /\ p <> lt /\ p <> done /\ p <> nv ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
        op_taint tm (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `Inv = \i H tm t.
    i <= N /\ ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    lookup_var ctr t = SOME (n2w i) /\ op_taint tm (Var ctr) = {} /\ FLOOKUP H ctr = NONE /\
    lookup_var len t = SOME (n2w N) /\ op_taint tm (Var len) = {} /\ FLOOKUP H len = NONE /\
    lookup_var src t = SOME a /\ lookup_var dst t = SOME b /\
    op_taint tm (Var src) = {} /\ op_taint tm (Var dst) = {} /\
    (src_span <> 0 ==> ptr_covers H tm src t src_span) /\
    (dst_span <> 0 ==> ptr_covers H tm dst t dst_span) /\
    typed_copy_state_frame sa (w2n b) dst_span s t /\
    (!j. j < N ==> !m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      val_in_memory stv (f j) (w2n a + j * type_memory_size stv) m) /\
    (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
      typed_copy_index_prefix f dtv (w2n b) N i m) /\
    (!j. j < w2n b \/ w2n b + dst_span <= j ==>
      mem_byte_at t.vs_memory j = mem_byte_at s.vs_memory j /\
      (j IN tm.t_mem <=> j IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!p. not_fresh_at sb p /\ p <> ctr /\ p <> lt /\ p <> done /\ p <> nv ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP H p = FLOOKUP G p /\
      op_taint tm (Var p) = op_taint tn (Var p))` >>
  `Inv 0 G tn s` by simp[Abbr `Inv`] >>
  `!i H tm t. i < N /\ Inv i H tm t ==>
    ?J un u. gas_path_ptr D 0 ctx fn PG H tm t 0 J un (OK u) /\ Inv (SUC i) J un u`
    by suspend "step" >>
  `!H tm t. Inv N H tm t ==> ~t.vs_halted` by simp[Abbr `Inv`] >>
  qpat_assum `!i H tm t. i < N /\ Inv i H tm t ==> _`
    (mp_then Any mp_tac typed_copy_counted_iteration) >>
  disch_then (qspecl_then [`0`,`G`,`tn`,`s`] mp_tac) >> simp[] >>
  (impl_tac >- simp[Abbr `Inv`]) >> strip_tac >>
  suspend "exit"
QED

Resume typed_copy_dynarray_loop_counted[step]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `Inv i H tm t` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `t`, `tn` |-> `tm`, `G` |-> `H`,
    `n` |-> `N`, `bb` |-> `hbb`, `id` |-> `hid`,
    `off` |-> `w2n (b:256 word)`, `span` |-> `dst_span`,
    `bodylbl` |-> `sb.cs_current_bb`,
    `P` |-> `\mt mem. mem = t.vs_memory`]
    (SPEC_ALL typed_copy_runtime_header_frame)) >>
  (impl_tac >- (simp[] >> conj_tac >- gvs[] >> gvs[])) >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tm t 0 H1 tm1 (OK u)` >>
  `lookup_var ctr u = SOME (n2w i) /\
   lookup_var src u = SOME a /\ lookup_var dst u = SOME b /\
   op_taint tm1 (Var ctr) = {} /\ op_taint tm1 (Var src) = {} /\
   op_taint tm1 (Var dst) = {}` by
    (gvs[] >> metis_tac[]) >>
  suspend "body"
QED

Resume typed_copy_dynarray_loop_counted[body]:
  `(src_span <> 0 ==> ptr_covers H1 tm1 src u src_span) /\
   (dst_span <> 0 ==> ptr_covers H1 tm1 dst u dst_span)` by
    (conj_tac >> strip_tac >> irule annassign_ptr_covers_frame_ptr >>
     qexistsl [`H`,`t`,`tm`] >> gvs[] >> metis_tac[]) >>
  qpat_assum `!sc sd sp dp fn G tn s a b v. _`
    (mp_then Any mp_tac typed_copy_index_body_counted) >>
  disch_then (mp_tac o Q.INST [`s''` |-> `u`, `f'` |-> `f`, `G` |-> `H1`, `tn` |-> `tm1`] o SPEC_ALL) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  suspend "backedge"
QED

Resume typed_copy_dynarray_loop_counted[exit]:
  qpat_x_assum `!sc sd sp dp fn G tn s a b v. _` kall_tac >>
  qpat_x_assum `!i H tm t. i < N /\ _ ==> _` kall_tac >>
  qpat_x_assum `Inv N H tm t` mp_tac >> simp[Abbr `Inv`] >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `t`, `tn` |-> `tm`, `G` |-> `H`,
    `i` |-> `N`, `n` |-> `N`, `bb` |-> `hbb`, `id` |-> `hid`,
    `off` |-> `w2n (b:256 word)`, `span` |-> `dst_span`,
    `bodylbl` |-> `sb.cs_current_bb`,
    `P` |-> `\mt mem. mem = t.vs_memory`]
    (SPEC_ALL typed_copy_runtime_header_frame)) >>
  (impl_tac >- (simp[] >> conj_tac >- gvs[] >> gvs[])) >>
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' tm' (OK t')` by
    metis_tac[gas_path_ptr_then,ADD] >>
  `typed_copy_state_frame sa (w2n b) dst_span s t'` by
    (irule typed_copy_state_frame_trans >> metis_tac[]) >>
  qexistsl [`H'`,`tm'`,`t'`] >> simp[] >>
  gvs[] >> rpt strip_tac >>
  qpat_x_assum `!p. not_fresh_at sb p /\ _ ==> _`
    (qspec_then `p` mp_tac) >> simp[]
QED

Resume typed_copy_dynarray_loop_counted[backedge]:
  rename1 `gas_path_ptr D 0 ctx fn PG H1 tm1 u 0 H2 tm2 (OK v)` >>
  `lookup_var ctr v = SOME (n2w i) /\ FLOOKUP H2 ctr = NONE /\
   op_taint tm2 (Var ctr) = {}` by (gvs[] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `v`, `tn` |-> `tm2`, `G` |-> `H2`,
    `bb` |-> `ebb`, `id` |-> `eid`,
    `off` |-> `w2n (b:256 word)`, `span` |-> `dst_span`,
    `P` |-> `\mt mem. mem = v.vs_memory`]
    (SPEC_ALL typed_copy_backedge_frame)) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  suspend "compose"
QED

Resume typed_copy_dynarray_loop_counted[compose]:
  qpat_x_assum `!sc sd sp dp fn G tn s a b v. _` kall_tac >>
  `gas_path_ptr D 0 ctx fn PG H tm t 0 H2 tm2 (OK v)` by
    metis_tac[gas_path_ptr_then,ADD] >>
  `gas_path_ptr D 0 ctx fn PG H tm t 0 H' tm' (OK t')` by
    metis_tac[gas_path_ptr_then,ADD] >>
  `typed_copy_state_frame sa (w2n b) dst_span u v` by
    (gvs[typed_copy_state_frame_def] >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `typed_copy_state_frame sa (w2n b) dst_span s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `v` >> conj_tac
     >- (irule typed_copy_state_frame_trans >> qexists_tac `u` >> conj_tac
         >- (irule typed_copy_state_frame_trans >> metis_tac[]) >> simp[]) >> simp[]) >>
  qexistsl [`H'`,`tm'`,`t'`] >> simp[] >>
  suspend "transport"
QED

Resume typed_copy_dynarray_loop_counted[transport]:
  gvs[] >>
  `!p. not_fresh_at sb p /\ p <> ctr /\ p <> lt /\ p <> done /\ p <> nv ==>
    lookup_var p t' = lookup_var p t /\ FLOOKUP H' p = FLOOKUP H p /\
    op_taint tm' (Var p) = op_taint tm (Var p)` by
    (rpt strip_tac >> metis_tac[]) >>
  suspend "finish"
QED

Resume typed_copy_dynarray_loop_counted[finish]:
  `lookup_var len t' = SOME (n2w N) /\ op_taint tm' (Var len) = {} /\
   FLOOKUP H' len = NONE /\ lookup_var src t' = SOME a /\
   lookup_var dst t' = SOME b /\ op_taint tm' (Var src) = {} /\
   op_taint tm' (Var dst) = {}` by metis_tac[] >>
  `(src_span <> 0 ==> ptr_covers H' tm' src t' src_span) /\
   (dst_span <> 0 ==> ptr_covers H' tm' dst t' dst_span)` by
    (conj_tac >> strip_tac >> irule annassign_ptr_covers_frame_ptr >>
     qexistsl [`H`,`t`,`tm`] >> gvs[] >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise typed_copy_dynarray_loop_counted
