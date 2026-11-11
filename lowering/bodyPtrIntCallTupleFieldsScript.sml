(* Concrete field-store preparation.  Unlike the older paired-offset boundary,
   endpoint zero-size fields are allowed and immutable taint is preserved. *)
Theory bodyPtrIntCallTupleFields
Ancestors bodyPtrIntCallFieldOffset bodyPtrIntCallStoreFields
  assignBasePtrFieldOffsets appendStorageGhostPtr stmtFragPtr
  typedCopyLayoutPtr typedCopyTuplePtr exprSimPtrTopLevelStorageFrame
  context compileEnv fragExec fragGasPathPtr venomState words finite_map arithmetic
  bodyPtrSubscriptMemoryRebuild vyperTypeDefaults

Theorem intcall_field_offsets_counted:
  !dst src doff soff sa dop sm sop sb G tn s d a dtot stot dn sn fn ctx D PG.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sb) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME d /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtot /\ ptr_covers G tn src s stot /\
    doff+dn <= dtot /\ soff+sn <= stot /\
    w2n d+doff < dimword (:256) /\ w2n a+soff < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    ?dp sp Gf tf u.
      dop = Var dp /\ sop = Var sp /\
      not_fresh_at sb dp /\ not_fresh_at sb sp /\
      lookup_var dp u = SOME (n2w (w2n d+doff)) /\
      lookup_var sp u = SOME (n2w (w2n a+soff)) /\
      ptr_covers Gf tf dp u dn /\ ptr_covers Gf tf sp u sn /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
      tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[assign_base_offset_extends] >>
  `cs_extends sm sb /\ sm.cs_next_var <= sb.cs_next_var` by
    (drule_all assign_base_offset_extends >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var` by
    metis_tac[cs_extends_trans, LESS_EQ_TRANS] >> simp[] >>
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gm tm (OK v)` >>
  rename1 `dop = Var dp` >>
  `not_fresh_at sm src` by metis_tac[not_fresh_at_mono] >>
  `lookup_var src v = SOME a` by metis_tac[] >>
  `ptr_covers Gm tm src v stot` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`G`, `s`, `sa`, `tn`] >> metis_tac[]) >>
  drule_all intcall_field_offset_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gm tm v 0 Gf tf (OK u)` >>
  rename1 `sop = Var sp` >>
  qexistsl_tac [`dp`, `sp`, `Gf`, `tf`, `u`] >>
  `not_fresh_at sb dp` by metis_tac[not_fresh_at_mono] >>
  `lookup_var dp u = lookup_var dp v` by metis_tac[] >>
  `ptr_covers Gf tf dp u dn` by
    (irule ptr_covers_old_transport >>
     qexistsl_tac [`Gm`, `v`, `sm`, `tm`] >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn s _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule >> simp[]) >>
  simp[ADD_COMM] >> conj_tac
  >- fs[venom_state_component_equality] >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

(* One concrete head: prepare the two addresses, then consume the recursive
   store contract.  The recursive premise is at the emitted child cursor;
   numeric resources are independent of provenance coverage. *)
Theorem intcall_field_store_counted:
  !D ctx fn PG dst src doff soff sa sm sc dop sop G tn s b a
    dtotal stotal stv dtv v sd.
    compile_with_byte_offset (Var dst) doff sa = (dop,sm) /\
    compile_with_byte_offset (Var src) soff sm = (sop,sc) /\
    not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s dtotal /\ ptr_covers G tn src s stotal /\
    doff + type_memory_size dtv <= dtotal /\
    soff + type_memory_size stv <= stotal /\
    w2n b + doff + type_memory_size dtv < dimword (:256) /\
    w2n a + soff + val_footprint stv v < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n a + soff) m) /\
    fn_has_code sa sc fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    (!dp sp H t u.
      dop = Var dp /\ sop = Var sp /\
      not_fresh_at sc dp /\ not_fresh_at sc sp /\
      lookup_var dp u = SOME (n2w (w2n b + doff)) /\
      lookup_var sp u = SOME (n2w (w2n a + soff)) /\
      ptr_covers H t dp u (type_memory_size dtv) /\
      ptr_covers H t sp u (type_memory_size stv) /\
      w2n (n2w (w2n b + doff):256 word) + type_memory_size dtv < dimword (:256) /\
      w2n (n2w (w2n a + soff):256 word) + val_footprint stv v < dimword (:256) /\
      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
        val_in_memory stv v (w2n (n2w (w2n a + soff):256 word)) m) /\
      u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted ==>
      ?K tf z.
        gas_path_ptr D 0 ctx fn PG H t u 0 K tf (OK z) /\
        z.vs_current_bb = sd.cs_current_bb /\
        z.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~z.vs_halted /\
        (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
          val_in_memory dtv v (w2n b + doff) m) /\
        tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\ tf.t_imm = t.t_imm /\
        z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
        z.vs_fmp = u.vs_fmp /\ z.vs_accounts = u.vs_accounts /\
        z.vs_transient = u.vs_transient /\ z.vs_call_ctx = u.vs_call_ctx /\
        (!x. not_fresh_at sc x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tf (Var x) = op_taint t (Var x)) /\
        (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size dtv) ==>
          mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
          (i IN tf.t_mem <=> i IN t.t_mem))) ==>
    ?K tf z.
      gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK z) /\
      z.vs_current_bb = sd.cs_current_bb /\
      z.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        val_in_memory dtv v (w2n b + doff) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size dtv) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `w2n b + doff < dimword (:256) /\ w2n a + soff < dimword (:256)`
    by decide_tac >>
  drule_all intcall_field_offsets_counted >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 H t (OK u)` >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
   u.vs_alloca_next = s.vs_alloca_next /\ u.vs_fmp = s.vs_fmp /\
   u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
   u.vs_call_ctx = s.vs_call_ctx` by
    fs[venom_state_component_equality] >>
  `w2n (n2w (w2n b + doff):256 word) = w2n b + doff /\
   w2n (n2w (w2n a + soff):256 word) = w2n a + soff` by simp[] >>
  fs[] >>
  qpat_x_assum `!H t u. _` (qspecl_then [`H`, `t`, `u`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H t u 0 Hf tf (OK z)` >>
  qexistsl_tac [`Hf`, `tf`, `z`] >> simp[] >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

(* Semantic part of advancing the destination prefix.  Fields need not have
   equal strides; empty fields are included in the prefix like every other. *)
Theorem intcall_tuple_prefix_advance:
  !tvs vs k b ms mem ms' mem'.
    values_have_types tvs vs /\ k < LENGTH tvs /\
    (!j. j < k ==> !m. mem_agree_outside ms mem m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (b + SUM (MAP type_memory_size (TAKE j tvs))) m) /\
    (!i. ~(b + SUM (MAP type_memory_size (TAKE k tvs)) <= i /\
            i < b + SUM (MAP type_memory_size (TAKE k tvs)) +
                    type_memory_size (EL k tvs)) ==>
      mem_bytes_at i 1 mem' = mem_bytes_at i 1 mem /\
      (i IN ms' <=> i IN ms)) /\
    (!m. mem_agree_outside ms' mem' m ==>
      val_in_memory (EL k tvs) (EL k vs)
        (b + SUM (MAP type_memory_size (TAKE k tvs))) m) ==>
    !j. j < SUC k ==> !m. mem_agree_outside ms' mem' m ==>
      val_in_memory (EL j tvs) (EL j vs)
        (b + SUM (MAP type_memory_size (TAKE j tvs))) m
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `j` >> strip_tac >>
  Cases_on `j = k` >- gvs[] >>
  `j < k /\ k <= LENGTH tvs /\ j < LENGTH tvs` by decide_tac >>
  `value_has_type (EL j tvs) (EL j vs)` by
    (fs[values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN]) >>
  `val_wf (EL j tvs) (EL j vs)` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  drule_all sum_take_element_before >>
  disch_then (qspec_then `type_memory_size` assume_tac) >>
  `SUM (MAP type_memory_size (TAKE j tvs)) +
     val_footprint (EL j tvs) (EL j vs) <=
     SUM (MAP type_memory_size (TAKE k tvs))` by
    (drule_all tupleMemoryLayoutTheory.tuple_element_footprint >> decide_tac) >>
  rpt strip_tac >> irule toplevel_robust_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`mem`, `mem'`, `ms`, `ms'`,
    `{i | b + SUM (MAP type_memory_size (TAKE k tvs)) <= i /\
           i < b + SUM (MAP type_memory_size (TAKE k tvs)) +
               type_memory_size (EL k tvs)}`] >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem intcall_tuple_fields_conditional:
  !D ctx fn PG ce dst src dts sts dtvs stvs vs sa sz G tn s b a.
    LENGTH dts = LENGTH vs /\ LENGTH sts = LENGTH vs /\
    LENGTH dtvs = LENGTH vs /\ LENGTH stvs = LENGTH vs /\
    values_have_types dtvs vs /\ values_have_types stvs vs /\
    (!i. i < LENGTH vs ==>
      type_memory_bytes ce (EL i dts) = type_memory_size (EL i dtvs) /\
      type_memory_bytes ce (EL i sts) = type_memory_size (EL i stvs)) /\
    compile_typed_copy_fields ce (Var dst) (Var src) dts sts 0 0 sa = ((),sz) /\
    fn_has_code sa sz fn /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    ptr_covers G tn dst s (SUM (MAP type_memory_size dtvs)) /\
    ptr_covers G tn src s (SUM (MAP type_memory_size stvs)) /\
    w2n b + SUM (MAP type_memory_size dtvs) < dimword (:256) /\
    w2n a + SUM (MAP type_memory_size stvs) < dimword (:256) /\
    (w2n b + SUM (MAP type_memory_size dtvs) <= w2n a \/
     w2n a + SUM (MAP type_memory_size stvs) <= w2n b) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      tuple_in_memory vs stvs (w2n a) m) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    (!i c d dp sp bv av H t u.
      i < LENGTH vs /\
      compile_store_memory_typed ce (Var dp) (EL i dts)
        (Var sp) (EL i sts) c = ((),d) /\ fn_has_code c d fn /\
      not_fresh_at c dp /\ not_fresh_at c sp /\
      lookup_var dp u = SOME bv /\ lookup_var sp u = SOME av /\
      ptr_covers H t dp u (type_memory_size (EL i dtvs)) /\
      ptr_covers H t sp u (type_memory_size (EL i stvs)) /\
      w2n bv + type_memory_size (EL i dtvs) < dimword (:256) /\
      w2n av + val_footprint (EL i stvs) (EL i vs) < dimword (:256) /\
      (w2n bv + type_memory_size (EL i dtvs) <= w2n av \/
       w2n av + type_memory_size (EL i stvs) <= w2n bv) /\
      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
        val_in_memory (EL i stvs) (EL i vs) (w2n av) m) /\
      u.vs_current_bb = c.cs_current_bb /\
      u.vs_inst_idx = LENGTH c.cs_current_insts /\ ~u.vs_halted ==>
      ?K tf z. gas_path_ptr D 0 ctx fn PG H t u 0 K tf (OK z) /\
        z.vs_current_bb = d.cs_current_bb /\
        z.vs_inst_idx = LENGTH d.cs_current_insts /\ ~z.vs_halted /\
        (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
          val_in_memory (EL i dtvs) (EL i vs) (w2n bv) m) /\
        tf.t_stor = t.t_stor /\ tf.t_trans = t.t_trans /\ tf.t_imm = t.t_imm /\
        z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next /\
        z.vs_fmp = u.vs_fmp /\ z.vs_accounts = u.vs_accounts /\
        z.vs_transient = u.vs_transient /\ z.vs_call_ctx = u.vs_call_ctx /\
        (!x. not_fresh_at c x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tf (Var x) = op_taint t (Var x)) /\
        (!j. ~(w2n bv <= j /\ j < w2n bv + type_memory_size (EL i dtvs)) ==>
          mem_bytes_at j 1 z.vs_memory = mem_bytes_at j 1 u.vs_memory /\
          (j IN tf.t_mem <=> j IN t.t_mem))) ==>
    ?K tf z. gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK z) /\
      z.vs_current_bb = sz.cs_current_bb /\
      z.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~z.vs_halted /\
      (!m. mem_agree_outside tf.t_mem z.vs_memory m ==>
        tuple_in_memory vs dtvs (w2n b) m) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      z.vs_allocas = s.vs_allocas /\ z.vs_alloca_next = s.vs_alloca_next /\
      z.vs_fmp = s.vs_fmp /\ z.vs_accounts = s.vs_accounts /\
      z.vs_transient = s.vs_transient /\ z.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x z = lookup_var x s /\ FLOOKUP K x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + SUM (MAP type_memory_size dtvs)) ==>
        mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `tupInv = \ds ss doff soff c H t u.
    ?k. k <= LENGTH vs /\ ds = DROP k dts /\ ss = DROP k sts /\
      doff = SUM (MAP type_memory_size (TAKE k dtvs)) /\
      soff = SUM (MAP type_memory_size (TAKE k stvs)) /\
      compile_typed_copy_fields ce (Var dst) (Var src) ds ss doff soff c = ((),sz) /\
      cs_extends sa c /\ sa.cs_next_var <= c.cs_next_var /\ fn_has_code c sz fn /\
      u.vs_current_bb = c.cs_current_bb /\
      u.vs_inst_idx = LENGTH c.cs_current_insts /\ ~u.vs_halted /\
      lookup_var dst u = SOME b /\ lookup_var src u = SOME a /\
      ptr_covers H t dst u (SUM (MAP type_memory_size dtvs)) /\
      ptr_covers H t src u (SUM (MAP type_memory_size stvs)) /\
      (!m. mem_agree_outside t.t_mem u.vs_memory m ==>
        tuple_in_memory vs stvs (w2n a) m) /\
      (!j. j < k ==> !m. mem_agree_outside t.t_mem u.vs_memory m ==>
        val_in_memory (EL j dtvs) (EL j vs)
          (w2n b + SUM (MAP type_memory_size (TAKE j dtvs))) m) /\
      t.t_stor = tn.t_stor /\ t.t_trans = tn.t_trans /\ t.t_imm = tn.t_imm /\
      u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
      u.vs_fmp = s.vs_fmp /\ u.vs_accounts = s.vs_accounts /\
      u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint t (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + doff) ==>
        mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN t.t_mem <=> i IN tn.t_mem))` >>
  `tupInv dts sts 0 0 sa G tn s` by
    (simp[Abbr `tupInv`] >> qexists_tac `0` >> simp[cs_extends_def]) >>
  qspecl_then [`D`, `ctx`, `fn`, `PG`, `ce`, `Var dst`, `Var src`, `tupInv`]
    mp_tac intcall_typed_fields_counted_traversal >>
  (impl_tac
   >- (rpt gen_tac >> strip_tac >> conj_tac
       >- (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
           disch_then (qspecl_then [`ce`, `dp`, `dt`, `sp`, `st`, `c`] mp_tac) >>
           simp[] >> simp[exprLoweringPropsTheory.ci_mono_def] >>
           metis_tac[assign_base_offset_extends, cs_extends_trans]) >>
       rpt gen_tac >> strip_tac >>
       qpat_x_assum `tupInv (dt::ds) (st::ss) _ _ _ _ _ _` mp_tac >>
       simp_tac (srw_ss()) [Abbr `tupInv`] >> strip_tac >>
       qpat_x_assum `doff = _` SUBST_ALL_TAC >>
       qpat_x_assum `soff = _` SUBST_ALL_TAC >>
       qpat_assum `compile_typed_copy_fields _ _ _ (_::_) (_::_) _ _ _ = _`
         mp_tac >>
       pure_rewrite_tac[Once compile_store_memory_typed_def] >>
       asm_simp_tac (srw_ss()) [LET_THM, pairTheory.UNCURRY_DEF,
         comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
       strip_tac >>
       `k < LENGTH vs` by
         (metis_tac[listTheory.LENGTH_DROP, listTheory.LENGTH, arithmeticTheory.SUB_EQ_0,
                    arithmeticTheory.NOT_LESS_EQUAL, numTheory.NOT_SUC]) >>
       `dt = EL k dts /\ st = EL k sts` by
         (metis_tac[listTheory.HD_DROP, listTheory.HD]) >>
       `cs_extends a' b' /\ cs_extends b' c` by
         metis_tac[assign_base_offset_extends] >>
       `cs_extends c d` by
         (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
          disch_then (qspecl_then [`ce`, `dp`, `dt`, `sp`, `st`, `c`] mp_tac) >>
          simp[] >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
       `cs_extends d sz` by
         (mp_tac (cj 2 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
          disch_then (qspecl_then [`ce`, `Var dst`, `Var src`, `ds`, `ss`,
            `SUM (MAP type_memory_size (TAKE k dtvs)) + type_memory_bytes ce dt`,
            `SUM (MAP type_memory_size (TAKE k stvs)) + type_memory_bytes ce st`, `d`] mp_tac) >>
          simp[] >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
       `cs_extends a' c /\ cs_extends c sz /\ cs_extends sa d` by
         metis_tac[cs_extends_trans] >>
       `fn_has_code a' c fn /\ fn_has_code c d fn /\ fn_has_code d sz fn` by
         metis_tac[fn_has_code_split] >>
       `SUM (MAP type_memory_size (TAKE k dtvs)) + type_memory_size (EL k dtvs)
          <= SUM (MAP type_memory_size dtvs) /\
        SUM (MAP type_memory_size (TAKE k stvs)) + type_memory_size (EL k stvs)
          <= SUM (MAP type_memory_size stvs)` by
         (conj_tac
          >- (qspecl_then [`dtvs`, `type_memory_size`, `k`, `LENGTH dtvs`]
                mp_tac sum_take_element_before >> simp[]) >>
          qspecl_then [`stvs`, `type_memory_size`, `k`, `LENGTH stvs`]
            mp_tac sum_take_element_before >> simp[]) >>
       `SUM (MAP type_memory_size (TAKE k stvs)) + val_footprint (EL k stvs) (EL k vs)
          <= SUM (MAP type_memory_size stvs)` by
         metis_tac[tuple_child_footprint_contained] >>
       `!m. mem_agree_outside tn'.t_mem s'.vs_memory m ==>
          val_in_memory (EL k stvs) (EL k vs)
            (w2n a + SUM (MAP type_memory_size (TAKE k stvs))) m` by
         metis_tac[tupleMemoryLayoutTheory.tuple_in_memory_element] >>
       `not_fresh_at a' dst /\ not_fresh_at a' src` by
         (conj_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >>
          simp[]) >>
       qpat_assum `compile_with_byte_offset (Var dst) _ a' = _`
         (mp_then Any mp_tac intcall_field_store_counted) >>
       disch_then drule >>
       disch_then (drule_at (Pat `!m. mem_agree_outside _ _ m ==> val_in_memory _ _ _ m`)) >>
       disch_then (drule_at (Pat `lookup_var dst _ = _`)) >>
       disch_then (drule_at (Pat `ptr_covers _ _ dst _ _`)) >>
       disch_then (drule_at (Pat `ptr_covers _ _ src _ _`)) >>
       disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
       disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
       disch_then (drule_at (Pat `~ctx_has_dalloca _`)) >>
       disch_then (qspecl_then [`D`, `PG`, `EL k dtvs`, `d`] mp_tac) >>
       simp[] >>
       (impl_tac
        >- (rpt gen_tac >> strip_tac >>
            qpat_x_assum `dp = Var _` SUBST_ALL_TAC >>
            qpat_x_assum `sp = Var _` SUBST_ALL_TAC >>
            qpat_x_assum `dt = EL k dts` SUBST_ALL_TAC >>
            qpat_x_assum `st = EL k sts` SUBST_ALL_TAC >>
            qpat_assum `!i c d dp sp bv av H t u. _`
              (qspec_then `k` mp_tac) >>
            simp[] >>
            disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
            disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
            disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
            simp[])) >>
       strip_tac >>
       `!j. j < SUC k ==> !m. mem_agree_outside tf.t_mem z.vs_memory m ==>
          val_in_memory (EL j dtvs) (EL j vs)
            (w2n b + SUM (MAP type_memory_size (TAKE j dtvs))) m` by
         (match_mp_tac intcall_tuple_prefix_advance >>
          qexistsl_tac [`tn'.t_mem`, `s'.vs_memory`] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- simp[] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac
          >- (qx_gen_tac `i` >> strip_tac >>
              qpat_x_assum `!i. _ ==> mem_bytes_at i 1 z.vs_memory = _ /\ _`
                (qspec_then `i` mp_tac) >>
              impl_tac >- decide_tac >> simp[]) >>
          simp_tac (srw_ss()) [ADD_COMM] >> simp[]) >>
       `sa.cs_next_var <= d.cs_next_var` by
         (mp_tac (cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family) >>
          disch_then (qspecl_then [`ce`, `dp`, `dt`, `sp`, `st`, `c`] mp_tac) >>
          simp[] >> simp[exprLoweringPropsTheory.ci_mono_def] >> strip_tac >>
          `a'.cs_next_var <= b'.cs_next_var /\ b'.cs_next_var <= c.cs_next_var` by
            metis_tac[assign_base_offset_extends] >> decide_tac) >>
       qexistsl_tac [`K'`, `tf`, `z`] >> simp[] >>
       qexists_tac `SUC k` >>
       `ds = DROP (SUC k) dts /\ ss = DROP (SUC k) sts` by
         (rewrite_tac[rich_listTheory.DROP_SUC] >>
          conj_tac
          >- (qpat_x_assum `dt::ds = DROP k dts` (SUBST1_TAC o SYM) >> simp[]) >>
          qpat_x_assum `st::ss = DROP k sts` (SUBST1_TAC o SYM) >> simp[]) >>
       simp[rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.MAP_SNOC,
            rich_listTheory.SUM_SNOC] >>
       conj_tac
       >- (irule ptr_covers_old_transport >>
           qexistsl_tac [`G'`, `s'`, `a'`, `tn'`] >>
           conj_tac >- simp[] >>
           conj_tac >- simp[] >>
           qpat_assum `!x. not_fresh_at a' x ==> _` mp_tac >>
           metis_tac[]) >>
       conj_tac
       >- (irule ptr_covers_old_transport >>
           qexistsl_tac [`G'`, `s'`, `a'`, `tn'`] >>
           conj_tac >- simp[] >>
           conj_tac >- simp[] >>
           qpat_assum `!x. not_fresh_at a' x ==> _` mp_tac >>
           metis_tac[]) >>
       conj_tac
       >- (rewrite_tac[GSYM valueEncodingPropsTheory.val_in_memory_tuple] >>
           rpt strip_tac >> irule toplevel_robust_exterior_frame >>
           conj_tac
           >- (irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >>
               simp[vyperTypingTheory.value_has_type_def]) >>
           qexistsl_tac [`s'.vs_memory`, `z.vs_memory`, `tn'.t_mem`, `tf.t_mem`,
             `{i | SUM (MAP type_memory_size (TAKE k dtvs)) + w2n b <= i /\
                   i < SUM (MAP type_memory_size (TAKE k dtvs)) +
                       (type_memory_size (EL k dtvs) + w2n b)}`] >>
           simp[valueEncodingPropsTheory.val_in_memory_tuple,
                loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def,
                valueEncodingProofsTheory.type_memory_size_list_sum] >>
           conj_tac
           >- (rpt strip_tac >>
               qpat_x_assum `!i. _ ==> mem_bytes_at i 1 z.vs_memory = _ /\ _`
                 (qspec_then `i` mp_tac) >> simp[]) >>
           rpt strip_tac >>
           qpat_x_assum `!i. _ ==> mem_bytes_at i 1 z.vs_memory = _ /\ _`
             (qspec_then `i` mp_tac) >> simp[]) >>
       conj_tac
       >- (simp_tac (srw_ss()) [ADD_COMM] >> first_assum ACCEPT_TAC) >>
       conj_tac
       >- (qx_gen_tac `x` >> strip_tac >>
           `not_fresh_at a' x` by
             (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
           qpat_x_assum `!x. not_fresh_at a' x ==> _` (qspec_then `x` mp_tac) >>
           qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >>
           simp[]) >>
       qx_gen_tac `i` >> strip_tac >>
       qpat_x_assum `!i. _ ==> mem_bytes_at i 1 z.vs_memory = _ /\ _`
         (qspec_then `i` mp_tac) >>
       qpat_x_assum `!i. _ ==> mem_bytes_at i 1 s'.vs_memory = _ /\ _`
         (qspec_then `i` mp_tac) >>
       simp[] >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM,
                          arithmeticTheory.LESS_EQ_ADD])) >>
  disch_then (qspecl_then [`dts`, `sts`, `0`, `0`, `sa`, `sz`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`G`, `tn`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  fs[Abbr `tupInv`] >>
  `k' = LENGTH vs` by simp[] >>
  gvs[] >>
  `TAKE (LENGTH vs) dtvs = dtvs` by simp[listTheory.TAKE_LENGTH_ID_rwt2] >>
  gvs[] >>
  `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
       tuple_in_memory vs dtvs (w2n b) m` by
    (rpt strip_tac >> irule tuple_in_memory_from_elements >>
     simp[] >>
     qpat_x_assum `!j. j < LENGTH vs ==> _` mp_tac >>
     simp_tac (srw_ss()) [ADD_COMM] >> metis_tac[]) >>
  qexistsl_tac [`H`, `tf`, `u`] >> simp[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` mp_tac >> simp[] >>
  qpat_x_assum `!i. _ ==> mem_bytes_at i 1 u.vs_memory = _ /\ _` mp_tac >>
  disch_tac >> disch_tac >> first_assum ACCEPT_TAC
QED
