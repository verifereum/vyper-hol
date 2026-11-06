(* Dynamic Concat arm: counted MCOPY and scalar length/offset boundaries. *)
Theory bodyPtrBytestringBuiltinsConcatBytes
Ancestors
  bodyPtrBytestringBuiltinsConcatFixed bodyPtrBytestringBuiltinsAllocation
  typedCopyPtr fragExecPtr abiEncoderReentryLeaves
  fragGasSeqPtr fragGasPathPtr bodyPtrDefs ptrDiscipline ptrSafeRun
  venomInst venomState venomExecSemantics words finite_map
  valueEncodingProps valueEncodingProofs list rich_list byte

Theorem concat_payload_copy_counted_edge:
  !D ctx fn PG G tn s bb id dst src count_op a b n.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst; Var src; count_op] []) /\
    lookup_var dst s = SOME a /\ lookup_var src s = SOME b /\
    eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
    gas_path_ptr_edge D 0 ctx fn PG G tn s 0
      (step_prov PG G (mk_inst id MCOPY [Var dst;Var src;count_op] [])
        (mcopy (w2n a) (w2n b) (w2n n) s))
      (step_taint (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
        (mcopy (w2n a) (w2n b) (w2n n) s) tn)
      (OK ((mcopy (w2n a) (w2n b) (w2n n) s) with
        vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
    OK (mcopy (w2n a) (w2n b) (w2n n) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >>
  simp[GSYM mk_inst_def] >> irule ptr_inst_ok_mcopy_operand >> simp[]
QED

Theorem concat_payload_copy_clean_ghost:
  !PG G tn s id dst src count_op a b n.
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand count_op s = SOME n /\
    (!i. w2n b <= i /\ i < w2n b+w2n n ==> i NOTIN tn.t_mem) ==>
    step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy (w2n a) (w2n b) (w2n n) s) = G /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n a) (w2n b) (w2n n) s) tn).t_var = tn.t_var /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n a) (w2n b) (w2n n) s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n a) (w2n b) (w2n n) s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n a) (w2n b) (w2n n) s) tn).t_mem =
      tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+w2n n}
Proof
  rpt strip_tac >> simp[mcopy_operand_ghost_frame] >>
  `!i. i < w2n n ==> i+w2n b NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem concat_payload_copy_preserves_covers:
  !PG G tn s id dst src count_op a b n p sz.
    eval_operand dst s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand count_op s = SOME n /\ ptr_covers G tn p s sz ==>
    ptr_covers
      (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
        (mcopy (w2n a) (w2n b) (w2n n) s))
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n a) (w2n b) (w2n n) s) tn)
      p ((mcopy (w2n a) (w2n b) (w2n n) s) with
        vs_inst_idx := SUC s.vs_inst_idx) sz
Proof
  rpt strip_tac >> simp[mcopy_operand_ghost_frame] >>
  gvs[ptr_covers_def, op_taint_def, mcopy_operand_ghost_frame,
      mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem concat_bytes_store_prefix:
  !D k src bs ob x s.
    mem_bytes_at src (LENGTH bs) s.vs_memory = bs /\
    (D+(k+LENGTH bs) <= ob \/ ob+32 <= D) ==>
    mem_bytes_at D (k+LENGTH bs)
      (mstore ob x (mcopy (D+k) src (LENGTH bs) s)).vs_memory =
    mem_bytes_at D k s.vs_memory ++ bs
Proof
  rpt gen_tac >> strip_tac >> (
  `mem_bytes_at D (k+LENGTH bs)
     (mstore ob x (mcopy (D+k) src (LENGTH bs) s)).vs_memory =
   mem_bytes_at D (k+LENGTH bs) (mcopy (D+k) src (LENGTH bs) s).vs_memory` by
    (irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  pop_assum SUBST1_TAC >> rewrite_tac[mem_bytes_at_split_padded] >>
  simp[mcopy_mem_bytes_at_same, mcopy_mem_bytes_at_disjoint])
QED

(* Last three edges of the dynamic arm. MCOPY reads the pre-write source,
   including when source and destination overlap or the length is zero. *)
Theorem concat_bytes_copy_counted:
  !D ctx fn PG G tn s bb id dst src off offset len next a b c k n.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MCOPY [Var dst;Var src;Var len] []) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var offset;Var len] [next]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MSTORE [Var off;Var next] []) /\
    lookup_var dst s = SOME a /\ lookup_var src s = SOME b /\
    lookup_var off s = SOME c /\ lookup_var offset s = SOME (n2w k) /\
    lookup_var len s = SOME (n2w n) /\ n < dimword(:256) /\
    ptr_covers G tn dst s n /\ ptr_covers G tn src s n /\
    ptr_covers G tn off s 32 /\
    op_taint tn (Var len) = {} /\ op_taint tn (Var offset) = {} /\
    op_prov G (Var len) = NONE /\ op_prov G (Var offset) = NONE /\
    (!i. w2n b <= i /\ i < w2n b+n ==> i NOTIN tn.t_mem) /\
    off <> next ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      t.vs_memory =
        (mstore (w2n c) (n2w k+n2w n) (mcopy (w2n a) (w2n b) n s)).vs_memory /\
      lookup_var next t = SOME (n2w k+n2w n) /\
      op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
      ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s.vs_allocas /\ t.vs_inst_idx = s.vs_inst_idx+3 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem DIFF
        ({i | w2n a <= i /\ i < w2n a+n} UNION
         {i | w2n c <= i /\ i < w2n c+32}) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. q <> next ==> lookup_var q t = lookup_var q s /\
        FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = mcopy (w2n a) (w2n b) n s` >>
  qabbrev_tac `g1 = step_prov PG G
    (mk_inst id MCOPY [Var dst;Var src;Var len] []) u` >>
  qabbrev_tac `tn1 = step_taint
    (mk_inst id MCOPY [Var dst;Var src;Var len] []) s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var next (n2w k+n2w n) s1` >>
  qabbrev_tac `g2 = step_prov PG g1
    (mk_inst (id+1) ADD [Var offset;Var len] [next]) v` >>
  qabbrev_tac `tn2 = step_taint
    (mk_inst (id+1) ADD [Var offset;Var len] [next]) s1 v tn1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  qabbrev_tac `z = mstore (w2n c) (n2w k+n2w n) s2` >>
  qabbrev_tac `g3 = step_prov PG g2
    (mk_inst (id+2) MSTORE [Var off;Var next] []) z` >>
  qabbrev_tac `tn3 = step_taint
    (mk_inst (id+2) MSTORE [Var off;Var next] []) s2 z tn2` >>
  qabbrev_tac `s3 = z with vs_inst_idx := SUC s2.vs_inst_idx` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)`
    by suspend "copy_edge" >>
  `g1 = G /\ tn1.t_var = tn.t_var /\ tn1.t_stor = tn.t_stor /\
   tn1.t_trans = tn.t_trans /\
   tn1.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+n}`
    by suspend "copy_frame" >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)`
    by suspend "increment" >>
  `ptr_covers g2 tn2 off s2 32` by suspend "covers" >>
  `gas_path_ptr_edge D 0 ctx fn PG g2 tn2 s2 0 g3 tn3 (OK s3)`
    by suspend "last_store" >>
  qexistsl_tac [`g3`, `tn3`, `s3`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_bytes_copy_counted[copy_edge]:
  unabbrev_all_tac >>
  `n = w2n (n2w n : bytes32)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule concat_payload_copy_counted_edge >> simp[eval_operand_def] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_bytes_copy_counted[copy_frame]:
  `eval_operand (Var dst) s = SOME a /\ eval_operand (Var src) s = SOME b /\
   eval_operand (Var len) s = SOME (n2w n)` by simp[eval_operand_def] >>
  map_every qunabbrev_tac [`g1`, `tn1`, `u`] >>
  `n = w2n (n2w n : bytes32)` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule concat_payload_copy_clean_ghost >> simp[]
QED

Resume concat_bytes_copy_counted[increment]:
  simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `v`] >>
  irule pointer_offset_counted_edge >>
  gvs[Abbr `s1`, Abbr `u`, mcopy_def, write_memory_with_expansion_def,
      op_taint_def, lookup_var_def, eval_operand_def, arithmeticTheory.ADD1] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_bytes_copy_counted[covers]:
  `ptr_covers g1 tn1 off s1 32` by
    gvs[ptr_covers_def, op_taint_def, Abbr `s1`, Abbr `u`,
        mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  qunabbrev_tac `g2` >> qunabbrev_tac `tn2` >>
  qunabbrev_tac `s2` >> qunabbrev_tac `v` >>
  irule concat_add_preserves_covers >> simp[]
QED

Resume concat_bytes_copy_counted[last_store]:
  simp[Abbr `g3`, Abbr `tn3`, Abbr `s3`, Abbr `z`] >>
  irule concat_word_store_counted_edge >>
  gvs[Abbr `tn2`, Abbr `v`, copy_len_binop_ghost_frame,
      Abbr `s2`, Abbr `s1`, Abbr `u`, mcopy_def,
      write_memory_with_expansion_def, update_var_def, lookup_var_def,
      eval_operand_def, FLOOKUP_UPDATE, arithmeticTheory.ADD1]
QED

Resume concat_bytes_copy_counted[path]:
  `~s3.vs_halted` by
    simp[Abbr `s3`, Abbr `z`, Abbr `s2`, Abbr `v`,
         Abbr `s1`, Abbr `u`, mstore_def, mcopy_def,
         write_memory_with_expansion_def, update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD]
QED

Resume concat_bytes_copy_counted[endpoint]:
  `lookup_var off s2 = SOME c /\
   eval_operand (Var next) s2 = SOME (n2w k+n2w n)` by
    (simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, mcopy_def,
          write_memory_with_expansion_def, lookup_var_def, update_var_def,
          FLOOKUP_UPDATE, eval_operand_def] >>
     qpat_x_assum `lookup_var off s = _` mp_tac >> simp[lookup_var_def]) >>
  `op_prov g2 (Var next) = NONE /\ op_taint tn2 (Var next) = {} /\
   tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
   tn2.t_trans = tn1.t_trans` by
    (simp[Abbr `g2`, Abbr `tn2`, Abbr `v`, copy_len_binop_ghost_frame] >>
     irule step_prov_out_none >> simp[mk_inst_def] >>
     irule out_prov_arith_none >> simp[mk_inst_def, op_prov_def] >>
     gvs[op_prov_def]) >>
  `g3 = g2 /\ tn3.t_var = tn2.t_var /\ tn3.t_stor = tn2.t_stor /\
   tn3.t_trans = tn2.t_trans /\
   tn3.t_mem = tn2.t_mem DIFF {i | w2n c <= i /\ i < w2n c+32}` by
    simp[Abbr `g3`, Abbr `tn3`, Abbr `z`, mstore_ghost_frame,
         step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV] >>
  `ptr_covers g3 tn3 off s3 32` by
    gvs[ptr_covers_def, op_taint_def, Abbr `s3`, Abbr `z`,
        mstore_def, lookup_var_def] >>
  conj_tac >-
    simp[NoAsms, Abbr `s3`, Abbr `z`, Abbr `s2`, Abbr `v`, Abbr `s1`,
         mstore_def, update_var_def] >>
  `op_taint tn3 (Var next) = {}` by
    (simp[op_taint_def] >>
     qpat_x_assum `op_taint tn2 (Var next) = _` mp_tac >> simp[op_taint_def]) >>
  simp[Abbr `s3`, Abbr `z`, mstore_def, lookup_var_def,
       pred_setTheory.DIFF_UNION] >>
  simp[Abbr `s2`, Abbr `v`, update_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `s1`, Abbr `u`, mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >>
  simp[Abbr `g2`, Abbr `tn2`, copy_len_binop_ghost_frame,
       op_taint_def, lookup_var_def, update_var_def] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Finalise concat_bytes_copy_counted

(* Source header and payload address: the two edges before the offset load. *)
Theorem concat_bytes_source_counted:
  !D ctx fn PG G tn s bb id root len src a n cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var root] [len]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) ADD [Var root; Lit 32w] [src]) /\
    lookup_var root s = SOME a /\ ptr_covers G tn root s cap /\
    ptr_covers G tn root s 32 /\ mload (w2n a) s = n2w n /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
    32+n <= cap /\ w2n a+32 < dimword(:256) /\
    root <> len /\ len <> src ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      lookup_var src t = SOME (a+32w) /\
      lookup_var len t = SOME (n2w n) /\
      op_prov Gf (Var len) = NONE /\ op_taint tnf (Var len) = {} /\
      ptr_covers Gf tnf src t n /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_labels = s.vs_labels /\ t.vs_inst_idx = s.vs_inst_idx+2 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. q <> len /\ q <> src ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `u = update_var len (n2w n) s` >>
  qabbrev_tac `g1 = step_prov PG G (mk_inst id MLOAD [Var root] [len]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst id MLOAD [Var root] [len]) s u tn` >>
  qabbrev_tac `s1 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `v = update_var src (a+32w) s1` >>
  qabbrev_tac `g2 = step_prov PG g1
    (mk_inst (id+1) ADD [Var root; Lit 32w] [src]) v` >>
  qabbrev_tac `tn2 = step_taint
    (mk_inst (id+1) ADD [Var root; Lit 32w] [src]) s1 v tn1` >>
  qabbrev_tac `s2 = v with vs_inst_idx := SUC s1.vs_inst_idx` >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 g1 tn1 (OK s1)` by
    (unabbrev_all_tac >> drule_all concat_offset_load_counted_edge >> simp[]) >>
  `op_prov g1 (Var len) = NONE /\ op_taint tn1 (Var len) = {} /\
   tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans`
    by suspend "load_ghost" >>
  `ptr_covers g1 tn1 root s1 cap /\ lookup_var root s1 = SOME a`
    by suspend "root" >>
  `gas_path_ptr_edge D 0 ctx fn PG g1 tn1 s1 0 g2 tn2 (OK s2)`
    by suspend "add_edge" >>
  qexistsl_tac [`g2`, `tn2`, `s2`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_bytes_source_counted[load_ghost]:
  `eval_operand (Var root) s = SOME a` by simp[eval_operand_def] >>
  drule_all concat_offset_load_ghost >>
  disch_then (qspecl_then [`PG`, `G`, `id`, `len`] mp_tac) >>
  simp[Abbr `g1`, Abbr `tn1`, Abbr `u`]
QED

Resume concat_bytes_source_counted[root]:
  conj_tac
  >- (simp[Abbr `s1`, Abbr `g1`, Abbr `tn1`, Abbr `u`] >>
      qpat_assum `mload _ _ = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      irule mload_preserves_ptr_covers >> simp[]) >>
  simp[Abbr `s1`, Abbr `u`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  gvs[lookup_var_def]
QED

Resume concat_bytes_source_counted[add_edge]:
  simp[Abbr `g2`, Abbr `tn2`, Abbr `s2`, Abbr `v`] >>
  irule pointer_offset_counted_edge >>
  gvs[Abbr `s1`, Abbr `u`, ptr_covers_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  qexists_tac `bb` >> simp[]
QED

Resume concat_bytes_source_counted[path]:
  `~s2.vs_halted` by
    simp[Abbr `s2`, Abbr `v`, Abbr `s1`, Abbr `u`, update_var_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD]
QED

Resume concat_bytes_source_counted[endpoint]:
  `ptr_covers g2 tn2 src s2 n` by
    (qunabbrev_tac `g2` >> qunabbrev_tac `tn2` >>
     qunabbrev_tac `s2` >> qunabbrev_tac `v` >>
     irule pointer_offset_covers >> simp[eval_operand_def, op_taint_def] >>
     qexists_tac `cap` >> simp[]) >>
  simp[Abbr `s2`, Abbr `v`, Abbr `tn2`, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `s1`, Abbr `u`] >>
  conj_tac
  >- (simp[Abbr `g2`, op_prov_def, copy_len_binop_ghost_frame] >>
      gvs[op_prov_def]) >>
  rpt strip_tac >>
  simp[Abbr `g2`, copy_len_binop_ghost_frame, Abbr `g1`,
       step_prov_def, set_prov_def, out_prov_def, mk_inst_def,
       FLOOKUP_DRESTRICT] >>
  simp[Abbr `tn1`, step_taint_def, set_var_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE]
QED

Finalise concat_bytes_source_counted

Theorem concat_bytes_addresses_counted:
  !D ctx fn PG G tn s bb id root off input len src offset dst
    a b c k n source_cap cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var input] [len]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var input; Lit 32w] [src]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MLOAD [Var off] [offset]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var root; Var offset] [dst]) /\
    lookup_var input s = SOME b /\ lookup_var root s = SOME a /\
    lookup_var off s = SOME c /\
    ptr_covers G tn input s source_cap /\ ptr_covers G tn input s 32 /\
    ptr_covers G tn root s cap /\ ptr_covers G tn off s 32 /\
    mload (w2n b) s = n2w n /\ mload (w2n c) s = n2w k /\
    (!i. (w2n b <= i /\ i < w2n b+32) \/
         (w2n c <= i /\ i < w2n c+32) ==> i NOTIN tn.t_mem) /\
    32+n <= source_cap /\ w2n b+32 < dimword(:256) /\
    k+n <= cap /\ w2n a+k < dimword(:256) /\
    ALL_DISTINCT [len; src; offset; dst] /\
    (~MEM root [len;src;offset;dst]) /\ (~MEM off [len;src;offset;dst]) /\
    input <> len ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      lookup_var dst t = SOME (a+n2w k) /\
      lookup_var src t = SOME (b+32w) /\ lookup_var len t = SOME (n2w n) /\
      lookup_var offset t = SOME (n2w k) /\ lookup_var off t = SOME c /\
      op_prov Gf (Var len) = NONE /\ op_taint tnf (Var len) = {} /\
      op_prov Gf (Var offset) = NONE /\ op_taint tnf (Var offset) = {} /\
      ptr_covers Gf tnf dst t n /\ ptr_covers Gf tnf src t n /\
      ptr_covers Gf tnf off t 32 /\ ptr_covers Gf tnf root t cap /\
      t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
      t.vs_labels = s.vs_labels /\ t.vs_inst_idx = s.vs_inst_idx+4 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!q. ~MEM q [len;src;offset;dst] ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  `?G1 tn1 s1.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1) /\
    lookup_var src s1 = SOME (b+32w) /\ lookup_var len s1 = SOME (n2w n) /\
    op_prov G1 (Var len) = NONE /\ op_taint tn1 (Var len) = {} /\
    ptr_covers G1 tn1 src s1 n /\
    s1.vs_memory = s.vs_memory /\ s1.vs_allocas = s.vs_allocas /\
    s1.vs_labels = s.vs_labels /\ s1.vs_inst_idx = s.vs_inst_idx+2 /\
    s1.vs_current_bb = s.vs_current_bb /\ ~s1.vs_halted /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
    (!q. q <> len /\ q <> src ==>
      lookup_var q s1 = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
      op_taint tn1 (Var q) = op_taint tn (Var q))`
    by suspend "source" >>
  `lookup_var off s1 = SOME c /\ lookup_var root s1 = SOME a /\
   ptr_covers G1 tn1 off s1 32 /\ ptr_covers G1 tn1 root s1 cap`
    by suspend "scratch" >>
  `mload (w2n c) s1 = n2w k` by
    gvs[mload_def] >>
  `?G2 tn2 s2.
    gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2) /\
    lookup_var dst s2 = SOME (a+n2w k) /\
    lookup_var offset s2 = SOME (n2w k) /\
    op_prov G2 (Var offset) = NONE /\ op_taint tn2 (Var offset) = {} /\
    ptr_covers G2 tn2 dst s2 n /\
    s2.vs_memory = s1.vs_memory /\ s2.vs_allocas = s1.vs_allocas /\
    s2.vs_labels = s1.vs_labels /\ s2.vs_inst_idx = s1.vs_inst_idx+2 /\
    s2.vs_current_bb = s1.vs_current_bb /\ ~s2.vs_halted /\
    tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
    tn2.t_trans = tn1.t_trans /\
    (!q. q <> offset /\ q <> dst ==>
      lookup_var q s2 = lookup_var q s1 /\ FLOOKUP G2 q = FLOOKUP G1 q /\
      op_taint tn2 (Var q) = op_taint tn1 (Var q))`
    by suspend "destination" >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_bytes_addresses_counted[source]:
  gvs[ALL_DISTINCT, MEM] >>
  irule concat_bytes_source_counted >>
  simp[arithmeticTheory.ADD1] >>
  qexistsl_tac [`source_cap`, `id`, `input`] >> simp[]
QED

Resume concat_bytes_addresses_counted[scratch]:
  gvs[MEM] >>
  `lookup_var off s1 = lookup_var off s /\ FLOOKUP G1 off = FLOOKUP G off /\
   op_taint tn1 (Var off) = op_taint tn (Var off)` by metis_tac[] >>
  `lookup_var root s1 = lookup_var root s /\ FLOOKUP G1 root = FLOOKUP G root /\
   op_taint tn1 (Var root) = op_taint tn (Var root)` by metis_tac[] >>
  gvs[ptr_covers_def]
QED

Resume concat_bytes_addresses_counted[destination]:
  irule concat_fixed_address_counted >> fs[MEM, ALL_DISTINCT] >>
  qexistsl_tac [`c`, `cap`, `id+2`, `off`, `root`] >>
  simp[arithmeticTheory.ADD1] >> metis_tac[]
QED

Resume concat_bytes_addresses_counted[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED

Resume concat_bytes_addresses_counted[endpoint]:
  gvs[MEM, ALL_DISTINCT] >>
  `FLOOKUP G2 len = FLOOKUP G1 len` by metis_tac[] >>
  `FLOOKUP G2 src = FLOOKUP G1 src` by metis_tac[] >>
  `FLOOKUP G2 off = FLOOKUP G1 off` by metis_tac[] >>
  `FLOOKUP G2 root = FLOOKUP G1 root` by metis_tac[] >>
  gvs[op_prov_def, ptr_covers_def]
QED

Finalise concat_bytes_addresses_counted

Theorem concat_bytes_arm_counted:
  !D ctx fn PG G tn s bb id root off input len src offset dst next
    a b c k n source_cap cap.
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id MLOAD [Var input] [len]) /\
    get_instruction bb (s.vs_inst_idx+1) =
      SOME (mk_inst (id+1) ADD [Var input; Lit 32w] [src]) /\
    get_instruction bb (s.vs_inst_idx+2) =
      SOME (mk_inst (id+2) MLOAD [Var off] [offset]) /\
    get_instruction bb (s.vs_inst_idx+3) =
      SOME (mk_inst (id+3) ADD [Var root; Var offset] [dst]) /\
    get_instruction bb (s.vs_inst_idx+4) =
      SOME (mk_inst (id+4) MCOPY [Var dst;Var src;Var len] []) /\
    get_instruction bb (s.vs_inst_idx+5) =
      SOME (mk_inst (id+5) ADD [Var offset;Var len] [next]) /\
    get_instruction bb (s.vs_inst_idx+6) =
      SOME (mk_inst (id+6) MSTORE [Var off;Var next] []) /\
    lookup_var input s = SOME b /\ lookup_var root s = SOME a /\
    lookup_var off s = SOME c /\
    ptr_covers G tn input s source_cap /\ ptr_covers G tn input s 32 /\
    ptr_covers G tn root s cap /\ ptr_covers G tn off s 32 /\
    mload (w2n b) s = n2w n /\ mload (w2n c) s = n2w k /\
    (!i. (w2n b <= i /\ i < w2n b+32+n) \/
         (w2n c <= i /\ i < w2n c+32) ==> i NOTIN tn.t_mem) /\
    32+n <= source_cap /\ w2n b+32 < dimword(:256) /\
    k+n <= cap /\ w2n a+k < dimword(:256) /\ n < dimword(:256) /\
    ALL_DISTINCT [len;src;offset;dst;next] /\
    (~MEM root [len;src;offset;dst;next]) /\
    (~MEM off [len;src;offset;dst;next]) /\ input <> len ==>
    ?Gf tnf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
      t.vs_memory = (mstore (w2n c) (n2w k+n2w n)
        (mcopy (w2n (a+n2w k)) (w2n (b+32w)) n s)).vs_memory /\
      lookup_var next t = SOME (n2w k+n2w n) /\
      op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
      ptr_covers Gf tnf off t 32 /\
      t.vs_allocas = s.vs_allocas /\ t.vs_inst_idx = s.vs_inst_idx+7 /\
      t.vs_current_bb = s.vs_current_bb /\ ~t.vs_halted /\
      tnf.t_mem = tn.t_mem DIFF
        ({i | w2n (a+n2w k) <= i /\ i < w2n (a+n2w k)+n} UNION
         {i | w2n c <= i /\ i < w2n c+32}) /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      (!q. ~MEM q [len;src;offset;dst;next] ==>
        lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
        op_taint tnf (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT [len;src;offset;dst] /\ ~MEM root [len;src;offset;dst] /\
   ~MEM off [len;src;offset;dst]` by gvs[ALL_DISTINCT, MEM] >>
  `!i. (w2n b <= i /\ i < w2n b+32) \/
       (w2n c <= i /\ i < w2n c+32) ==> i NOTIN tn.t_mem` by
    (rpt gen_tac >> disch_tac >>
     qpat_x_assum `!i. _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  drule_all concat_bytes_addresses_counted >>
  disch_then (qspecl_then [`D`, `PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1`
      (qx_choose_then `s1` strip_assume_tac)))) >>
  `?Gf tnf t.
    gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 Gf tnf (OK t) /\
    t.vs_memory = (mstore (w2n c) (n2w k+n2w n)
      (mcopy (w2n (a+n2w k)) (w2n (b+32w)) n s1)).vs_memory /\
    lookup_var next t = SOME (n2w k+n2w n) /\
    op_prov Gf (Var next) = NONE /\ op_taint tnf (Var next) = {} /\
    ptr_covers Gf tnf off t 32 /\
    t.vs_allocas = s1.vs_allocas /\ t.vs_inst_idx = s1.vs_inst_idx+3 /\
    t.vs_current_bb = s1.vs_current_bb /\ ~t.vs_halted /\
    tnf.t_mem = tn1.t_mem DIFF
      ({i | w2n (a+n2w k) <= i /\ i < w2n (a+n2w k)+n} UNION
       {i | w2n c <= i /\ i < w2n c+32}) /\
    tnf.t_stor = tn1.t_stor /\ tnf.t_trans = tn1.t_trans /\
    (!q. q <> next ==> lookup_var q t = lookup_var q s1 /\
      FLOOKUP Gf q = FLOOKUP G1 q /\
      op_taint tnf (Var q) = op_taint tn1 (Var q))`
    by suspend "suffix" >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >>
  conj_tac >- suspend "path" >> suspend "endpoint"
QED

Resume concat_bytes_arm_counted[suffix]:
  irule concat_bytes_copy_counted >>
  fs[ALL_DISTINCT, MEM] >>
  conj_tac
  >- (simp[w2n_add_2] >> rpt gen_tac >> disch_tac >>
      qpat_x_assum `!i. _ \/ _ ==> i NOTIN tn.t_mem` irule >> decide_tac) >>
  qexistsl_tac [`dst`, `id+4`, `len`, `offset`, `src`] >> simp[]
QED

Resume concat_bytes_arm_counted[path]:
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD]
QED

Resume concat_bytes_arm_counted[endpoint]:
  conj_tac
  >- (asm_rewrite_tac[] >> irule abi_encoder_store_memory >>
      simp[mcopy_def, write_memory_with_expansion_def]) >>
  gvs[MEM] >> metis_tac[]
QED

Finalise concat_bytes_arm_counted
