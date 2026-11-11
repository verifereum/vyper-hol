(* Robust representation interfaces for recursive field copying. *)
Theory widenedAssignPtrCopyFieldList
Ancestors assignBasePtrFieldsCompose typedCopyRobustTransportPtr typedMemoryCopy
  typedCopyAgreement valueEncodingDefs valueEncodingProps valueEncoding
  fragGasPathPtr fragExec context compileEnv venomState words list arithmetic
  emitHelper contextCodegenRelProps ptrDiscipline finite_map pred_set
  placeMemoryFieldsForward exprLoweringProps

Theorem widened_assign_robust_tuple_frame:
  !vs tvs p dst n tn tn' mem mem'.
    tuple_val_wf vs tvs /\
    (p + type_memory_size_list tvs <= dst \/ dst+n <= p) /\
    (!m. mem_agree_outside tn mem m ==> tuple_in_memory vs tvs p m) /\
    typed_copy_frame dst n mem mem' /\
    (!i. ~(dst <= i /\ i < dst+n) ==> (i IN tn' <=> i IN tn)) ==>
    !m. mem_agree_outside tn' mem' m ==> tuple_in_memory vs tvs p m
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn' mem' m ==>
    val_in_memory (TupleTV tvs) (ArrayV (TupleV vs)) p m` suffices_by
      simp[val_in_memory_def] >>
  rpt strip_tac >> irule robust_representation_exterior_frame >>
  conj_tac >- gvs[val_wf_def] >>
  qexistsl_tac [`dst`, `mem`, `mem'`, `n`, `tn`, `tn'`] >>
  gvs[typed_copy_frame_def, val_in_memory_def, val_wf_def, type_memory_size_def] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem widened_assign_robust_tuple_cons:
  !tv v tvs vs p tn tn' s t.
    val_wf tv v /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v p m) /\
    typed_copy_frame (p + type_memory_size tv) (type_memory_size_list tvs)
      s.vs_memory t.vs_memory /\
    (!i. ~(p + type_memory_size tv <= i /\
            i < p + type_memory_size tv + type_memory_size_list tvs) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      tuple_in_memory vs tvs (p + type_memory_size tv) m) ==>
    !m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
      tuple_in_memory (v::vs) (tv::tvs) p m
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
     val_in_memory tv v p m` by
    (rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`p + type_memory_size tv`, `s.vs_memory`, `t.vs_memory`,
                   `type_memory_size_list tvs`, `tn.t_mem`, `tn'.t_mem`] >>
     gvs[typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[val_in_memory_def]
QED

(* R selects precisely the smaller-rank entries supplied by a constructor. *)
Theorem widened_assign_typed_copy_fields_counted:
  !R cenv ctx D PG.
    (!dty sty dtv stv v.
      R dty sty dtv stv v ==>
      !a b dst src dw sw fn G tn s.
        compile_store_memory_typed cenv dst dty src sty a = ((),b) /\
        (!x. dst = Var x ==> not_fresh_at a x) /\
        (!x. src = Var x ==> not_fresh_at a x) /\
        eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
        op_taint tn dst = {} /\ op_taint tn src = {} /\
        (0 < type_memory_size dtv ==>
          ?x. dst = Var x /\ ptr_covers G tn x s (type_memory_size dtv)) /\
        (0 < type_memory_size stv ==>
          ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size stv)) /\
        w2n dw + type_memory_size dtv < dimword (:256) /\
        w2n sw + type_memory_size stv < dimword (:256) /\
        (w2n dw + type_memory_size dtv <= w2n sw \/
         w2n sw + type_memory_size stv <= w2n dw) /\
        (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
          val_in_memory stv v (w2n sw) m) /\
        fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
        s.vs_current_bb = a.cs_current_bb /\
        s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
        ~ctx_has_dalloca ctx ==>
        ?G' tn' t.
          gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
          t.vs_current_bb = b.cs_current_bb /\
          t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
          (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
            val_in_memory dtv v (w2n dw) m) /\
          typed_copy_state_frame a (w2n dw) (type_memory_size dtv) s t /\
          (!x. not_fresh_at a x ==>
            lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
            op_taint tn' (Var x) = op_taint tn (Var x)) /\
          tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
          tn'.t_imm = tn.t_imm /\
          (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
            (i IN tn'.t_mem <=> i IN tn.t_mem))) /\
    (!root off a op b G tn s w total n fn.
      compile_with_byte_offset (Var root) off a = (op,b) /\
      not_fresh_at a root /\ lookup_var root s = SOME w /\
      op_taint tn (Var root) = {} /\
      (0 < n ==> ptr_covers G tn root s total) /\ off+n <= total /\
      w2n w + off < dimword (:256) /\
      fn_has_code a b fn /\ s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      cs_extends a b /\ a.cs_next_var <= b.cs_next_var /\
      ?p Gf tf u.
        op = Var p /\ not_fresh_at b p /\
        lookup_var p u = SOME (n2w (w2n w+off)) /\
        op_taint tf (Var p) = {} /\
        (0 < n ==> ptr_covers Gf tf p u n) /\
        gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
        u.vs_current_bb = b.cs_current_bb /\
        u.vs_inst_idx = LENGTH b.cs_current_insts /\ ~u.vs_halted /\
        (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
        tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
        tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
        (!x. not_fresh_at a x ==>
          lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
          op_taint tf (Var x) = op_taint tn (Var x))) ==>
    !dtys stys dtvs stvs vs dst src doff soff dc sc a b G tn s dw sw fn.
      LENGTH dtys = LENGTH stys /\ LENGTH dtys = LENGTH dtvs /\
      LENGTH dtys = LENGTH stvs /\ LENGTH dtys = LENGTH vs /\
      (!i. i < LENGTH dtys ==>
        R (EL i dtys) (EL i stys) (EL i dtvs) (EL i stvs) (EL i vs) /\
        type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
        type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs)) /\
      tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs /\
      compile_typed_copy_fields cenv dst src dtys stys doff soff a = ((),b) /\
      (!x. dst = Var x ==> not_fresh_at a x) /\
      (!x. src = Var x ==> not_fresh_at a x) /\
      eval_operand dst s = SOME dw /\ eval_operand src s = SOME sw /\
      op_taint tn dst = {} /\ op_taint tn src = {} /\
      doff + type_memory_size_list dtvs <= dc /\
      soff + type_memory_size_list stvs <= sc /\
      w2n dw + dc < dimword (:256) /\ w2n sw + sc < dimword (:256) /\
      (w2n dw + dc <= w2n sw \/ w2n sw + sc <= w2n dw) /\
      (0 < dc ==> ?x. dst = Var x /\ ptr_covers G tn x s dc) /\
      (0 < sc ==> ?x. src = Var x /\ ptr_covers G tn x s sc) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        tuple_in_memory vs stvs (w2n sw+soff) m) /\
      fn_has_code a b fn /\ fn_inst_ids_distinct fn /\
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = LENGTH a.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx ==>
      ?G' tn' t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
        t.vs_current_bb = b.cs_current_bb /\
        t.vs_inst_idx = LENGTH b.cs_current_insts /\ ~t.vs_halted /\
        (!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
          tuple_in_memory vs dtvs (w2n dw+doff) m) /\
        typed_copy_state_frame a (w2n dw+doff) (type_memory_size_list dtvs) s t /\
        (!x. not_fresh_at a x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
          op_taint tn' (Var x) = op_taint tn (Var x)) /\
        tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
        tn'.t_imm = tn.t_imm /\
        (!i. ~(w2n dw+doff <= i /\
                i < w2n dw+doff+type_memory_size_list dtvs) ==>
          (i IN tn'.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!dty sty dtv stv v. R dty sty dtv stv v ==> _` (mk_asm "child") >>
  qpat_x_assum `!root off a op b G tn s w total n fn.
    compile_with_byte_offset (Var root) off a = (op,b) /\ _ ==> _`
    (mk_asm "offset") >>
  `!root off sa dp sb G tn s w total n fn.
    compile_with_byte_offset root off sa = (dp,sb) /\
    (!x. root = Var x ==> not_fresh_at sa x) /\
    eval_operand root s = SOME w /\ op_taint tn root = {} /\
    (0 < total ==> ?x. root = Var x /\ ptr_covers G tn x s total) /\
    off+n <= total /\ w2n w+off < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tf u.
      (!x. dp = Var x ==> not_fresh_at sb x) /\
      eval_operand dp u = SOME (n2w (w2n w+off)) /\ op_taint tf dp = {} /\
      (0 < n ==> ?x. dp = Var x /\ ptr_covers Gf tf x u n) /\
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK u) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted /\
      (u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
      tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
      tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==>
        lookup_var x u = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
        op_taint tf (Var x) = op_taint tn (Var x))` by
    (rpt gen_tac >> strip_tac >> rename1 `off+n <= cap` >>
     Cases_on `cap = 0`
     >- (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
         gvs[compile_with_byte_offset_def, comp_return_def] >>
         qexistsl_tac [`G`, `tn`, `s`] >>
         simp[cj 1 gas_path_ptr_rules, venom_state_component_equality]) >>
     `0 < cap` by decide_tac >>
     qpat_x_assum `0 < cap ==> _` drule >> strip_tac >> gvs[] >>
     rename1 `ptr_covers G tn p s cap` >>
     `lookup_var p s = SOME w` by gvs[eval_operand_def] >>
     `0 < n ==> ptr_covers G tn p s cap` by simp[] >>
     `off+n <= cap /\ w2n w+off < dimword (:256)` by decide_tac >>
     asm "offset" drule_all >> strip_tac >>
     qexistsl_tac [`Gf`, `tf`, `u`] >> gvs[eval_operand_def]) >>
  pop_assum (mk_asm "root_offset") >>
  Induct_on `dtys`
  >- (rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
      asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
      gvs[LENGTH_NIL] >>
      gvs[Once compile_store_memory_typed_def, comp_return_def] >>
      qexistsl_tac [`G`, `tn`, `s`] >>
      simp[cj 1 gas_path_ptr_rules, val_in_memory_def, type_memory_size_def]) >>
  pop_assum (mk_asm "ih") >>
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  Cases_on `stys`
  >- (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
      asm_x "ih" kall_tac >> gvs[]) >>
  Cases_on `dtvs`
  >- (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
      asm_x "ih" kall_tac >> gvs[]) >>
  Cases_on `stvs`
  >- (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
      asm_x "ih" kall_tac >> gvs[]) >>
  Cases_on `vs`
  >- (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
      asm_x "ih" kall_tac >> gvs[]) >>
  rename1 `compile_typed_copy_fields cenv dst src (dty::dtys) (sty::stys) doff soff a = ((),b)` >>
  qmatch_goalsub_rename_tac `tuple_in_memory (v::vs) (dtv::dtvs)` >>
  qmatch_asmsub_rename_tac `tuple_in_memory (v::vs) (stv::stvs)` >>
  qpat_assum `!i. i < _ ==> R _ _ _ _ _ /\ _`
    (qspec_then `0` mp_tac) >> simp[NoAsms] >> strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> RULE_L_ASSUM_TAC CONJUNCTS >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty c = (u,z)` >>
  Cases_on `u` >>
  `cs_extends a cs' /\ cs_extends cs' c` by
    (conj_tac
     >- (qpat_assum `compile_with_byte_offset dst doff a = _`
           (mp_tac o MATCH_MP compile_with_byte_offset_extends) >> simp[]) >>
     qpat_assum `compile_with_byte_offset src soff cs' = _`
       (mp_tac o MATCH_MP compile_with_byte_offset_extends) >> simp[]) >>
  `ci_mono c z` by
    (mp_tac (cj 1 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `dp`, `dty`, `sp`, `sty`, `c`] mp_tac) >>
     simp[]) >>
  `ci_mono z b` by
    (mp_tac (cj 2 ci_mono_typed_memory_family) >>
     disch_then (qspecl_then [`cenv`, `dst`, `src`, `dtys`, `stys`,
       `doff+type_memory_size dtv`, `soff+type_memory_size stv`, `z`] mp_tac) >>
     simp[]) >>
  `cs_extends c z /\ cs_extends z b` by fs[ci_mono_def] >>
  `cs_extends cs' b /\ cs_extends c b /\ cs_extends a c` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code a cs' fn /\ fn_has_code cs' c fn /\
   fn_has_code c z fn /\ fn_has_code z b fn` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[fn_has_code_split]) >>
  `doff+type_memory_size dtv <= dc /\ w2n dw+doff < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  asm "root_offset" drule_all >>
  strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG G tn s 0 Gd td (OK sd)` >>
  `sd.vs_memory = s.vs_memory` by
    (qpat_x_assum `sd with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand src sd = SOME sw /\ op_taint td src = {}` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     `sd.vs_labels = s.vs_labels` by
       (qpat_x_assum `sd with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
        simp[venom_state_component_equality]) >>
     Cases_on `src` >> fs[eval_operand_def, op_taint_def] >>
     metis_tac[]) >>
  `a.cs_next_var <= cs'.cs_next_var` by
    (drule_all compile_with_byte_offset_fresh >> simp[]) >>
  `!x. src = Var x ==> not_fresh_at cs' x` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(0 < sc ==> ?x. src = Var x /\ ptr_covers Gd td x sd sc)` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     strip_tac >> qpat_x_assum `0 < sc ==> _` drule >> strip_tac >>
     qexists_tac `x` >> fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `soff+type_memory_size stv <= sc /\ w2n sw+soff < dimword (:256)` by
    (fs[type_memory_size_def] >> decide_tac) >>
  asm "root_offset" drule_all >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gd td sd 0 Gs ts (OK ss)` >>
  `cs'.cs_next_var <= c.cs_next_var` by
    (drule_all compile_with_byte_offset_fresh >> simp[]) >>
  `(!x. dp = Var x ==> not_fresh_at c x) /\
   eval_operand dp ss = SOME (n2w (w2n dw+doff)) /\ op_taint ts dp = {} /\
   (0 < type_memory_size dtv ==> ?x. dp = Var x /\
      ptr_covers Gs ts x ss (type_memory_size dtv))` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     `ss.vs_labels = sd.vs_labels` by
       (qpat_assum `ss with <|vs_vars := _; vs_inst_idx := _|> = sd` mp_tac >>
        simp[venom_state_component_equality]) >>
     rpt conj_tac
     >- metis_tac[freshWritesTheory.not_fresh_at_mono]
     >- (Cases_on `dp` >> fs[eval_operand_def] >> metis_tac[])
     >- (Cases_on `dp` >> fs[op_taint_def] >> metis_tac[]) >>
     strip_tac >> qpat_x_assum `0 < type_memory_size dtv ==> _` drule >>
     strip_tac >> qexists_tac `x` >>
     fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[]) >>
  `ss.vs_memory = s.vs_memory /\ ts.t_mem = tn.t_mem` by
    (qpat_assum `ss with <|vs_vars := _; vs_inst_idx := _|> = sd` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!m. mem_agree_outside ts.t_mem ss.vs_memory m ==>
    val_in_memory stv v (w2n (n2w (w2n sw+soff):256 word)) m` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     simp[w2n_n2w, LESS_MOD] >> rpt strip_tac >>
     qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _`
       (qspec_then `m` mp_tac) >>
     simp[val_in_memory_def]) >>
  Q.SUBGOAL_THEN
  `w2n (n2w (w2n dw+doff):256 word) + type_memory_size dtv < dimword (:256) /\
   w2n (n2w (w2n sw+soff):256 word) + type_memory_size stv < dimword (:256) /\
   (w2n (n2w (w2n dw+doff):256 word) + type_memory_size dtv <=
      w2n (n2w (w2n sw+soff):256 word) \/
    w2n (n2w (w2n sw+soff):256 word) + type_memory_size stv <=
      w2n (n2w (w2n dw+doff):256 word))`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN assume_tac))
  >- (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  asm "child" drule >> disch_then drule_all >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG Gs ts ss 0 Gh th (OK sh)` >>
  `!x. not_fresh_at a x ==> not_fresh_at c x` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS]) >>
  `(!x. not_fresh_at a x ==> lookup_var x sh = lookup_var x s /\
       FLOOKUP Gh x = FLOOKUP G x /\ op_taint th (Var x) = op_taint tn (Var x))` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(!x. dst = Var x ==> not_fresh_at z x) /\
   (!x. src = Var x ==> not_fresh_at z x)` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand dst sh = SOME dw /\ eval_operand src sh = SOME sw /\
   op_taint th dst = {} /\ op_taint th src = {}` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     `sh.vs_labels = s.vs_labels` by
       (fs[typed_copy_state_frame_def, venom_state_component_equality]) >>
     conj_tac
     >- (Cases_on `dst` >> fs[eval_operand_def] >> metis_tac[]) >>
     conj_tac
     >- (Cases_on `src` >> fs[eval_operand_def] >> metis_tac[]) >>
     conj_tac
     >- (Cases_on `dst` >> fs[op_taint_def] >> metis_tac[]) >>
     Cases_on `src` >> fs[op_taint_def] >> metis_tac[]) >>
  `(!i. i < LENGTH dtys ==> R (EL i dtys) (EL i stys) (EL i dtvs)
      (EL i stvs) (EL i vs) /\
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs))` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     gen_tac >> strip_tac >> qpat_x_assum `!i. i < LENGTH (dty::dtys) ==> _`
      (qspec_then `SUC i` mp_tac) >> fs[EL]) >>
  `tuple_val_wf vs dtvs /\ tuple_val_wf vs stvs` by
    fs[val_wf_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    tuple_in_memory vs stvs (w2n sw+soff+type_memory_size stv) m` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     rpt strip_tac >>
     qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _`
       (qspec_then `m` mp_tac) >> simp[val_in_memory_def]) >>
  `typed_copy_frame (w2n dw+doff) (type_memory_size dtv)
     s.vs_memory sh.vs_memory` by
    (qpat_x_assum `typed_copy_state_frame c _ _ ss sh` mp_tac >>
     simp[typed_copy_state_frame_def, w2n_n2w, LESS_MOD, ADD_COMM]) >>
  `!i. ~(w2n dw+doff <= i /\ i < w2n dw+doff+type_memory_size dtv) ==>
      (i IN th.t_mem <=> i IN tn.t_mem)` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     qpat_x_assum `!i. ~(_ <= i /\ i < _) ==> (i IN th.t_mem <=> _)` mp_tac >>
     simp[w2n_n2w, LESS_MOD, ADD_COMM]) >>
  `!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
    tuple_in_memory vs stvs (w2n sw+(soff+type_memory_size stv)) m` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     rpt strip_tac >> irule widened_assign_robust_tuple_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`w2n dw+doff`, `s.vs_memory`, `sh.vs_memory`,
       `type_memory_size dtv`, `tn.t_mem`, `th.t_mem`] >>
     rpt conj_tac
     >- (pure_rewrite_tac [ADD_ASSOC] >> first_assum ACCEPT_TAC)
     >- (first_assum ACCEPT_TAC)
     >- (fs[type_memory_size_def] >> decide_tac)
     >- (first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `(0 < dc ==> ?x. dst = Var x /\ ptr_covers Gh th x sh dc) /\
   (0 < sc ==> ?x. src = Var x /\ ptr_covers Gh th x sh sc)` by
    (asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
     asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
     conj_tac >> strip_tac
     >- (qpat_x_assum `0 < dc ==> _` drule >> strip_tac >>
         qexists_tac `x` >> fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])
     >- (qpat_x_assum `0 < sc ==> _` drule >> strip_tac >>
         qexists_tac `x` >> fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[])) >>
  `(doff+type_memory_size dtv)+type_memory_size_list dtvs <= dc /\
   (soff+type_memory_size stv)+type_memory_size_list stvs <= sc` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `LENGTH dtys = LENGTH stys /\ LENGTH dtys = LENGTH dtvs /\
   LENGTH dtys = LENGTH stvs /\ LENGTH dtys = LENGTH vs` by fs[] >>
  asm "ih" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  asm_x "child" kall_tac >> asm_x "offset" kall_tac >>
  asm_x "root_offset" kall_tac >> asm_x "ih" kall_tac >>
  `!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
    val_in_memory dtv v (w2n dw+doff) m` by
    (qpat_x_assum `!m. mem_agree_outside th.t_mem sh.vs_memory m ==> val_in_memory dtv v _ m`
       mp_tac >> simp[w2n_n2w, LESS_MOD, ADD_COMM]) >>
  `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==>
    tuple_in_memory (v::vs) (dtv::dtvs) (w2n dw+doff) m` by
    (rpt strip_tac >> irule widened_assign_robust_tuple_cons >>
     conj_tac >- fs[val_wf_def] >>
     qexistsl_tac [`sh`, `t`, `th`, `tn'`] >> rpt conj_tac
     >- (first_assum ACCEPT_TAC)
     >- (qpat_x_assum `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> _` mp_tac >>
         pure_rewrite_tac [ADD_ASSOC] >> disch_then ACCEPT_TAC)
     >- (qpat_x_assum `!i. _ ==> (i IN tn'.t_mem <=> i IN th.t_mem)` mp_tac >>
         pure_rewrite_tac [ADD_ASSOC] >> disch_then ACCEPT_TAC)
     >- (first_assum ACCEPT_TAC) >>
     qpat_assum `typed_copy_state_frame z _ _ sh t` mp_tac >>
     pure_rewrite_tac [typed_copy_state_frame_def, ADD_ASSOC] >> simp[]) >>
  `!x. not_fresh_at a x ==> not_fresh_at z x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[] >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t)` by
    (qpat_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 Gd td (OK sd)`
       (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[] >>
     disch_then (mp_then Any mp_tac gas_path_ptr_then) >> disch_then drule >> simp[]) >>
  `typed_copy_frame (w2n dw+doff+type_memory_size dtv)
      (type_memory_size_list dtvs) sh.vs_memory t.vs_memory` by
    (qpat_assum `typed_copy_state_frame z _ _ sh t` mp_tac >>
     pure_rewrite_tac [typed_copy_state_frame_def, ADD_ASSOC] >> simp[]) >>
  `typed_copy_frame (w2n dw+doff)
    (type_memory_size dtv+type_memory_size_list dtvs) s.vs_memory sh.vs_memory` by
    (irule typed_copy_frame_subinterval >>
     qexistsl_tac [`w2n dw+doff`, `type_memory_size dtv`] >> simp[]) >>
  `typed_copy_frame (w2n dw+doff)
    (type_memory_size dtv+type_memory_size_list dtvs) sh.vs_memory t.vs_memory` by
    (irule typed_copy_frame_subinterval >>
     qexistsl_tac [`w2n dw+doff+type_memory_size dtv`, `type_memory_size_list dtvs`] >> simp[]) >>
  `typed_copy_frame (w2n dw+doff)
    (type_memory_size_list (dtv::dtvs)) s.vs_memory t.vs_memory` by
    (pure_rewrite_tac[type_memory_size_def] >>
     irule typed_copy_frame_trans >> qexists_tac `sh.vs_memory` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `typed_copy_state_frame a (w2n dw+doff)
    (type_memory_size_list (dtv::dtvs)) s t` by
    (pure_rewrite_tac[typed_copy_state_frame_def] >>
     conj_tac
     >- fs[typed_copy_state_frame_def, venom_state_component_equality] >>
     conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
  `!i. ~(w2n dw+doff <= i /\
      i < w2n dw+doff+type_memory_size_list (dtv::dtvs)) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> strip_tac >>
     `~(w2n dw+doff <= i /\ i < w2n dw+doff+type_memory_size dtv) /\
      ~(w2n dw+(doff+type_memory_size dtv) <= i /\
        i < w2n dw+(doff+type_memory_size dtv)+type_memory_size_list dtvs)` by
       (fs[type_memory_size_def] >> decide_tac) >>
     qpat_x_assum `!i. _ ==> (i IN tn'.t_mem <=> i IN th.t_mem)`
       (qspec_then `i` mp_tac) >>
     qpat_x_assum `!i. _ ==> (i IN th.t_mem <=> i IN tn.t_mem)`
       (qspec_then `i` mp_tac) >>
     simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >>
  rpt conj_tac
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- (qpat_x_assum `!m. mem_agree_outside tn'.t_mem t.vs_memory m ==> tuple_in_memory (v::vs) _ _ m`
        mp_tac >> pure_rewrite_tac[Once ADD_COMM] >> disch_then ACCEPT_TAC)
  >- (qpat_x_assum `typed_copy_state_frame a _ _ s t` mp_tac >>
        pure_rewrite_tac[Once ADD_COMM] >> disch_then ACCEPT_TAC)
  >- (first_assum ACCEPT_TAC)
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!i. _ ==> (i IN tn'.t_mem <=> i IN tn.t_mem)`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- (fs[] >> decide_tac)) >> simp[]
QED
