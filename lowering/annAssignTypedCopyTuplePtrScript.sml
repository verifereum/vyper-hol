(* Tuple normalization: concrete offsets, recursive children, robust fields. *)
Theory annAssignTypedCopyTuplePtr
Ancestors
  annAssignTypedCopyInterfacePtr annAssignTypedCopyAtomsPtr
  assignBasePtrFieldOffsets bodyPtrPopNestedLiveAddressFrame
  context compileEnv typedMemoryCopy fragGasPathPtr venomState words
  valueEncodingDefs valueEncoding ptrDiscipline finite_map bodyPtrDefs
  placeMemoryFieldsForward contextCodegenRelProps fragExec exprLoweringProps
  typedCopyRobustTransportPtr

(* Unlike the older strict-offset adapter this also covers a zero-sized
   trailing field.  The immutable-taint frame is needed by declaration. *)
Theorem annassign_typed_field_offset_ambient_ptr:
  !root off sa op sb G tn s a total n fn ctx D PG.
    compile_with_byte_offset (Var root) off sa = (op,sb) /\
    not_fresh_at sa root /\ lookup_var root s = SOME a /\
    ptr_covers G tn root s total /\ off+n <= total /\
    w2n a + off < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?p Gf tf u.
      op = Var p /\ not_fresh_at sb p /\
      lookup_var p u = SOME (n2w (w2n a+off)) /\
      ptr_covers Gf tf p u n /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_base_offset_extends >> strip_tac >> simp[] >>
  Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules] >>
      gvs[ptr_covers_def, venom_state_component_equality] >> decide_tac) >>
  `emit_op ADD [Var root; Lit (n2w off)] sa = (op,sb)` by
    gvs[compile_with_byte_offset_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off) /\
   op_taint tn (Lit (n2w off)) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all pop_emit_offset_endpoint_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`out`, `H`, `tf`, `t`] >> simp[] >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
  simp[venom_state_component_equality]
QED

Theorem indexed_four_cons[local]:
  !P x xs y ys z zs w ws.
    (!k. k < SUC (LENGTH xs) ==>
      P (EL k (x::xs)) (EL k (y::ys)) (EL k (z::zs)) (EL k (w::ws))) ==>
    P x y z w /\
    (!k. k < LENGTH xs ==> P (EL k xs) (EL k ys) (EL k zs) (EL k ws))
Proof
  rpt gen_tac >> disch_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED

Theorem annassign_typed_copy_head_ambient_ptr[local]:
  !ce D ctx PG R.
    (!dt st dtv stv dp sp sa sb fn G tn s b a v.
      R dt st dtv stv /\
      compile_store_memory_typed ce (Var dp) dt (Var sp) st sa = ((),sb) /\
      fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dp /\ not_fresh_at sa sp /\
      lookup_var dp s = SOME b /\ lookup_var sp s = SOME a /\
      ptr_covers G tn dp s (type_memory_bytes ce dt) /\
      ptr_covers G tn sp s (type_memory_bytes ce st) /\
      type_memory_bytes ce dt = type_memory_size dtv /\
      type_memory_bytes ce st = type_memory_size stv /\
      w2n b + type_memory_size dtv < dimword (:256) /\
      w2n a + type_memory_size stv < dimword (:256) /\
      (w2n b + type_memory_size dtv <= w2n a \/
       w2n a + type_memory_size stv <= w2n b) /\
      val_wf dtv v /\ val_wf stv v /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
           val_in_memory stv v (w2n a) m) ==>
      cs_extends sa sb /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b <= i /\ i < w2n b + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n b) m)) ==>
    !dt st dtv stv dst src doff soff sa sb sc sd dp sp fn G tn s b a nd ns v.
      R dt st dtv stv /\
      compile_with_byte_offset (Var dst) doff sa = (dp,sb) /\
      compile_with_byte_offset (Var src) soff sb = (sp,sc) /\
      compile_store_memory_typed ce dp dt sp st sc = ((),sd) /\
      fn_has_code sa sd fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
      lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
      ptr_covers G tn dst s nd /\ ptr_covers G tn src s ns /\
      type_memory_bytes ce dt = type_memory_size dtv /\
      type_memory_bytes ce st = type_memory_size stv /\
      doff + type_memory_size dtv <= nd /\ soff + type_memory_size stv <= ns /\
      w2n b + nd < dimword (:256) /\ w2n a + ns < dimword (:256) /\
      (w2n a + ns <= w2n b \/ w2n b + nd <= w2n a) /\
      val_wf dtv v /\ val_wf stv v /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (w2n a + soff) m) ==>
      cs_extends sa sd /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sd.cs_current_bb /\
        t.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b + doff) (type_memory_size dtv) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        not_fresh_at sd dst /\ not_fresh_at sd src /\
        lookup_var dst t = SOME b /\ lookup_var src t = SOME a /\
        ptr_covers H tm dst t nd /\ ptr_covers H tm src t ns /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n b + doff) m)
Proof
  rpt gen_tac >> disch_then (mk_asm "child") >> rpt gen_tac >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  qpat_assum `compile_with_byte_offset (Var dst) doff sa = _`
    (mp_then Any strip_assume_tac assign_base_offset_extends) >>
  qpat_assum `compile_with_byte_offset (Var src) soff sb = _`
    (mp_then Any strip_assume_tac assign_base_offset_extends) >>
  `ci_mono sc sd` by
    (asm_x "child" kall_tac >>
     metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND]) >>
  `cs_extends sc sd` by gvs[ci_mono_def] >>
  `cs_extends sa sc /\ cs_extends sa sd /\ cs_extends sb sd` by
    (asm_x "child" kall_tac >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn` by
    (asm_x "child" kall_tac >> metis_tac[fn_has_code_split]) >>
  `doff + type_memory_bytes ce dt <= nd /\
   w2n b + doff < dimword (:256) /\
   soff + type_memory_bytes ce st <= ns /\
   w2n a + soff < dimword (:256)` by
    (asm_x "child" kall_tac >> gvs[] >> decide_tac) >>
  qpat_assum `compile_with_byte_offset (Var dst) doff sa = (dp,sb)`
    (mp_then Any mp_tac annassign_typed_field_offset_ambient_ptr) >>
  disch_then (qspecl_then [`G`, `tn`, `s`, `b`, `nd`,
    `type_memory_bytes ce dt`, `fn`, `ctx`, `D`, `PG`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` >>
  rename1 `dp = Var dpv` >>
  `not_fresh_at sb src /\ lookup_var src s1 = SOME a /\
   ptr_covers G1 tn1 src s1 ns` by
    (asm_x "child" kall_tac >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `lookup_var src s1 = lookup_var src s /\
      FLOOKUP G1 src = FLOOKUP G src /\
      op_taint tn1 (Var src) = op_taint tn (Var src)` by metis_tac[] >>
     gvs[ptr_covers_def]) >>
  qpat_assum `compile_with_byte_offset (Var src) soff sb = (sp,sc)`
    (mp_then Any mp_tac annassign_typed_field_offset_ambient_ptr) >>
  disch_then (qspecl_then [`G1`, `tn1`, `s1`, `a`, `ns`,
    `type_memory_bytes ce st`, `fn`, `ctx`, `D`, `PG`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2 (OK s2)` >>
  rename1 `sp = Var spv` >>
  `not_fresh_at sc dpv /\
   lookup_var dpv s2 = SOME (n2w (w2n b + doff)) /\
   ptr_covers G2 tn2 dpv s2 (type_memory_bytes ce dt)` by
    (asm_x "child" kall_tac >>
     conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     `lookup_var dpv s2 = lookup_var dpv s1 /\
      FLOOKUP G2 dpv = FLOOKUP G1 dpv /\
      op_taint tn2 (Var dpv) = op_taint tn1 (Var dpv)` by metis_tac[] >>
     gvs[ptr_covers_def]) >>
  `s2.vs_memory = s.vs_memory` by
    (asm_x "child" kall_tac >> gvs[venom_state_component_equality]) >>
  `w2n (n2w (w2n b + doff):256 word) = w2n b + doff /\
   w2n (n2w (w2n a + soff):256 word) = w2n a + soff` by
    simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  `!m. mem_agree_outside tn2.t_mem s2.vs_memory m ==>
       val_in_memory stv v (w2n (n2w (w2n a + soff):256 word)) m` by
    (asm_x "child" kall_tac >> gvs[]) >>
  `w2n b + doff + type_memory_size dtv < dimword (:256) /\
   w2n a + soff + type_memory_size stv < dimword (:256)` by
    (asm_x "child" kall_tac >> decide_tac) >>
  SUBGOAL_THEN
    ``w2n (b:256 word) + doff + type_memory_size dtv <= w2n (a:256 word) + soff \/
      w2n (a:256 word) + soff + type_memory_size stv <= w2n (b:256 word) + doff`` assume_tac
  >- (asm_x "child" kall_tac >> decide_tac) >>
  `compile_store_memory_typed ce (Var dpv) dt (Var spv) st sc = ((),sd)` by
    (qpat_x_assum `compile_store_memory_typed ce dp dt sp st sc = _` mp_tac >> simp[]) >>
  asm "child" (drule_at (Pos (el 2))) >>
  disch_then (qspecl_then [`dtv`, `stv`] mp_tac) >>
  disch_then (qspecl_then [`fn`, `G2`, `tn2`, `s2`] mp_tac) >>
  simp[] >> disch_then (qspec_then `v` mp_tac) >>
  impl_tac >- (asm_x "child" kall_tac >> gvs[]) >> strip_tac >>
  rename1 `gas_path_ptr _ _ _ _ _ _ _ _ _ childG childT (OK childS)` >>
  asm_x "child" kall_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x /\ not_fresh_at sc x /\ not_fresh_at sd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, ci_mono_def] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x childS = lookup_var x s /\ FLOOKUP childG x = FLOOKUP G x /\
     op_taint childT (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `typed_copy_state_frame sa (w2n b + doff) (type_memory_size dtv) s childS` by
    (gvs[typed_copy_state_frame_def, venom_state_component_equality,
         arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK s2)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 childG childT (OK childS)` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD] >>
  `childS.vs_prev_bb = s.vs_prev_bb` by gvs[venom_state_component_equality] >>
  `ptr_covers childG childT dst childS nd /\ ptr_covers childG childT src childS ns` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[] >> qexistsl_tac [`childG`, `childT`, `childS`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM] >>
  gvs[]
QED

Theorem annassign_typed_copy_fields_counted_ambient_ptr:
  !ce D ctx PG R.
    (!dt st dtv stv dp sp sa sb fn G tn s b a v.
      R dt st dtv stv /\
      compile_store_memory_typed ce (Var dp) dt (Var sp) st sa = ((),sb) /\
      fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dp /\ not_fresh_at sa sp /\
      lookup_var dp s = SOME b /\ lookup_var sp s = SOME a /\
      ptr_covers G tn dp s (type_memory_bytes ce dt) /\
      ptr_covers G tn sp s (type_memory_bytes ce st) /\
      type_memory_bytes ce dt = type_memory_size dtv /\
      type_memory_bytes ce st = type_memory_size stv /\
      w2n b + type_memory_size dtv < dimword (:256) /\
      w2n a + type_memory_size stv < dimword (:256) /\
      (w2n b + type_memory_size dtv <= w2n a \/
       w2n a + type_memory_size stv <= w2n b) /\
      val_wf dtv v /\ val_wf stv v /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
           val_in_memory stv v (w2n a) m) ==>
      cs_extends sa sb /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b <= i /\ i < w2n b + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n b) m)) ==>
    !dts sts dtvs stvs vs dst src doff soff sa sz fn G tn s b a nd ns.
      LENGTH sts = LENGTH dts /\ LENGTH dtvs = LENGTH dts /\
      LENGTH stvs = LENGTH dts /\ LENGTH vs = LENGTH dts /\
      (!k. k < LENGTH dts ==>
        R (EL k dts) (EL k sts) (EL k dtvs) (EL k stvs) /\
        type_memory_bytes ce (EL k dts) = type_memory_size (EL k dtvs) /\
        type_memory_bytes ce (EL k sts) = type_memory_size (EL k stvs)) /\
      val_wf (TupleTV dtvs) (ArrayV (TupleV vs)) /\
      val_wf (TupleTV stvs) (ArrayV (TupleV vs)) /\
      compile_typed_copy_fields ce (Var dst) (Var src) dts sts
        doff soff sa = ((),sz) /\
      fn_has_code sa sz fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
      lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
      ptr_covers G tn dst s nd /\ ptr_covers G tn src s ns /\
      doff + type_memory_size_list dtvs <= nd /\
      soff + type_memory_size_list stvs <= ns /\
      w2n b + nd < dimword (:256) /\ w2n a + ns < dimword (:256) /\
      (w2n a + ns <= w2n b \/ w2n b + nd <= w2n a) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        tuple_in_memory vs stvs (w2n a + soff) m) ==>
      cs_extends sa sz /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sz.cs_current_bb /\
        t.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b + doff) (type_memory_size_list dtvs) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b + doff <= i /\
               i < w2n b + doff + type_memory_size_list dtvs) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          tuple_in_memory vs dtvs (w2n b + doff) m)
Proof
  rpt gen_tac >> disch_then (mk_asm "child") >> Induct_on `dts`
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once compile_store_memory_typed_def, comp_return_def] >>
      simp[cs_extends_refl] >> qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules, val_in_memory_def]) >>
  pop_assum (mk_asm "tail") >> rpt gen_tac >>
  namedCases_on `sts` ["", "st sts0"] >> simp[] >>
  namedCases_on `dtvs` ["", "dtv dtvs0"] >> simp[] >>
  namedCases_on `stvs` ["", "stv stvs0"] >> simp[] >>
  namedCases_on `vs` ["", "v vs0"] >> simp[] >>
  disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  rename1 `compile_typed_copy_fields ce _ _ (dt::dts) _ _ _ _ = _` >>
  qspec_then `\dt st dtv stv.
    R dt st dtv stv /\ type_memory_bytes ce dt = type_memory_size dtv /\
    type_memory_bytes ce st = type_memory_size stv`
    (fn th => drule (BETA_RULE th)) indexed_four_cons >> strip_tac >>
  `val_wf dtv v /\ val_wf stv v /\
   val_wf (TupleTV dtvs0) (ArrayV (TupleV vs0)) /\
   val_wf (TupleTV stvs0) (ArrayV (TupleV vs0))` by
    (gvs[val_wf_def, listTheory.LIST_REL_CONS1]) >>
  drule typed_memory_fields_cons_compile >> strip_tac >>
  rename1 `compile_with_byte_offset (Var dst) doff sa = (dp,sb)` >>
  rename1 `compile_with_byte_offset (Var src) soff sb = (sp,sc)` >>
  rename1 `compile_store_memory_typed ce dp dt sp st sc = ((),sd)` >>
  `cs_extends sa sc /\ cs_extends sc sz /\ cs_extends sb sz /\
   cs_extends sa sz` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
   fn_has_code sc sd fn /\ fn_has_code sd sz fn` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     metis_tac[fn_has_code_split]) >>
  simp[] >> suspend "offsets"
QED

Resume annassign_typed_copy_fields_counted_ambient_ptr[offsets]:
  `cs_extends sa sd` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sd fn` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     metis_tac[fn_has_code_split]) >>
  `doff + type_memory_size dtv <= nd /\
   soff + type_memory_size stv <= ns` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     gvs[type_memory_size_def] >> decide_tac) >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory stv v (w2n a + soff) m` by
    (asm_x "child" kall_tac >> asm_x "tail" kall_tac >>
     rpt strip_tac >> first_x_assum drule >>
     simp[val_in_memory_def, arithmeticTheory.ADD_COMM]) >>
  asm "child" (mp_then Any mp_tac annassign_typed_copy_head_ambient_ptr) >>
  disch_then (fn th =>
    qpat_assum `compile_with_byte_offset (Var dst) doff sa = (dp,sb)`
      (mp_then (Pos (el 2)) mp_tac th)) >>
  disch_then (qspecl_then [`dt`, `st`, `dtv`, `stv`] mp_tac) >>
  disch_then (fn th =>
    qpat_assum `compile_with_byte_offset (Var src) soff sb = (sp,sc)`
      (mp_then (Pos (el 2)) mp_tac th)) >>
  disch_then (fn th =>
    qpat_assum `compile_store_memory_typed ce dp dt sp st sc = ((),sd)`
      (mp_then (Pos (el 2)) mp_tac th)) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `G` mp_tac) >>
  disch_then (qspec_then `tn` mp_tac) >>
  disch_then (qspec_then `s` mp_tac) >>
  disch_then (qspecl_then [`b`, `a`, `nd`, `ns`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t)` >>
  asm_x "child" kall_tac >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (TupleTV stvs0) (ArrayV (TupleV vs0))
      (w2n a + soff + type_memory_size stv) m` by
    (asm_x "tail" kall_tac >> rpt strip_tac >>
     qpat_x_assum `!m. _ ==> tuple_in_memory _ _ _ _` drule >>
     simp[NoAsms, val_in_memory_def] >>
     metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  `!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
    val_in_memory (TupleTV stvs0) (ArrayV (TupleV vs0))
      (w2n a + soff + type_memory_size stv) m` by
    (asm_x "tail" kall_tac >> rpt strip_tac >>
     irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexists_tac `doff + w2n b` >>
     qexists_tac `s.vs_memory` >> qexists_tac `t.vs_memory` >>
     qexists_tac `type_memory_size dtv` >>
     qexists_tac `tn.t_mem` >> qexists_tac `tm.t_mem` >>
     simp[] >> conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     gvs[type_memory_size_def] >> decide_tac ) >>
  asm_x "tail" (fn th =>
    qpat_assum `compile_typed_copy_fields ce (Var dst) (Var src) dts sts0 _ _ sd = ((),sz)`
      (mp_then (Pos (el 8)) mp_tac th)) >>
  disch_then (qspecl_then [`dtvs0`, `stvs0`, `vs0`] mp_tac) >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `H` mp_tac) >>
  disch_then (qspec_then `tm` mp_tac) >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (qspecl_then [`b`, `a`, `nd`, `ns`] mp_tac) >>
  simp[] >> impl_tac
  >- (conj_tac
      >- (gvs[type_memory_size_def] >> decide_tac) >>
      conj_tac
      >- (gvs[type_memory_size_def] >> decide_tac) >>
      qpat_x_assum `!m. mem_agree_outside tm.t_mem t.vs_memory m ==> val_in_memory (TupleTV stvs0) _ _ m` mp_tac >>
      simp[NoAsms, val_in_memory_def] >>
      metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  strip_tac >>
  qpat_assum `compile_with_byte_offset (Var dst) doff sa = _`
    (mp_then Any strip_assume_tac assign_base_offset_extends) >>
  qpat_assum `compile_with_byte_offset (Var src) soff sb = _`
    (mp_then Any strip_assume_tac assign_base_offset_extends) >>
  `ci_mono sc sd` by
    metis_tac[cj 1 ci_mono_typed_memory_family, pairTheory.SND] >>
  `sa.cs_next_var <= sd.cs_next_var` by
    (gnvs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!m. mem_agree_outside tm'.t_mem t'.vs_memory m ==>
       val_in_memory dtv v (doff + w2n b) m` by
    (rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexists_tac `doff + (type_memory_size dtv + w2n b)` >>
     qexists_tac `t.vs_memory` >> qexists_tac `t'.vs_memory` >>
     qexists_tac `type_memory_size_list dtvs0` >>
     qexists_tac `tm.t_mem` >> qexists_tac `tm'.t_mem` >>
     simp[] >> conj_tac >- metis_tac[] >>
     metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 H' tm' (OK t')` by
    metis_tac[gas_path_ptr_then, arithmeticTheory.ADD] >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t' = lookup_var x s /\ FLOOKUP H' x = FLOOKUP G x /\
     op_taint tm' (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `typed_copy_state_frame sa (w2n b + doff + type_memory_size dtv)
     (type_memory_size_list dtvs0) t t'` by
    (gvs[typed_copy_state_frame_def] >> metis_tac[]) >>
  `typed_copy_state_frame sa (w2n b + doff)
     (type_memory_size_list (dtv::dtvs0)) s t` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n b + doff`, `type_memory_size dtv`] >>
     simp[type_memory_size_def]) >>
  `typed_copy_state_frame sa (w2n b + doff)
     (type_memory_size_list (dtv::dtvs0)) t t'` by
    (irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n b + doff + type_memory_size dtv`,
                  `type_memory_size_list dtvs0`] >>
     pure_rewrite_tac[cj 11 type_memory_size_def] >>
     conj_tac >- decide_tac >>
     conj_tac >- (POP_ASSUM_LIST (K all_tac) >>
       pure_once_rewrite_tac[type_memory_size_def] >> decide_tac) >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  `typed_copy_state_frame sa (w2n b + doff)
     (type_memory_size_list (dtv::dtvs0)) s t'` by
    metis_tac[typed_copy_state_frame_trans] >>
  qexistsl_tac [`H'`, `tm'`, `t'`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      `~(doff + w2n b <= i /\ i < doff + w2n b + type_memory_size dtv) /\
       ~(doff + w2n b + type_memory_size dtv <= i /\
         i < doff + w2n b + type_memory_size dtv + type_memory_size_list dtvs0)` by
        (qpat_x_assum `~(_ <= i) \/ ~_` mp_tac >>
         pure_once_rewrite_tac[type_memory_size_def] >> decide_tac) >>
      qpat_assum `!j. _ ==> mem_bytes_at j 1 t'.vs_memory = _ /\ _`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> strip_tac >>
      qpat_assum `!j. _ ==> mem_bytes_at j 1 t.vs_memory = _ /\ _`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> metis_tac[]) >>
  rpt strip_tac >>
  pure_once_rewrite_tac[val_in_memory_def] >>
  simp[]
QED

Finalise annassign_typed_copy_fields_counted_ambient_ptr
