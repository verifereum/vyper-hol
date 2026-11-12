(* The joint typed memory copies of tuples and structs, field by field. *)
Theory typedCopyOriginPtrFields
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy robustCopyTransportPtr vyperTypeDefaults
  context compileEnv loweringStateRelDefs emitHelper venomState venomInst codegenRel venomExecSemantics
  vyperValue vyperTyping valueEncodingDefs valueEncoding

Libs
  vyperValueTheory vyperTypingTheory vyperASTTheory listTheory vyperTypeSystemTheory
  valueEncodingDefsTheory valueEncodingTheory contextTheory compileEnvTheory

Theorem typed_copy_origin_ptr_fields_path_from_offset:
  (!cenv ctx dty sty dtv stv v xd xs doff soff dtotal stotal
     sa s1 s2 sb dp sp lo explicit func PG s G tn dw sw.
    typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v /\
    compile_with_byte_offset (Var xd) doff sa = (dp,s1) /\
    compile_with_byte_offset (Var xs) soff s1 = (sp,s2) /\
    compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory stv v (w2n sw + soff) mem) /\
    doff + type_memory_size dtv <= dtotal /\
    soff + type_memory_size stv <= stotal /\
    w2n sw + soff + type_memory_size stv < dimword (:256) /\
    w2n dw + doff + type_memory_size dtv < dimword (:256) /\
    (type_memory_size stv = 0 \/
     w2n sw + soff + type_memory_size stv <= s.vs_alloca_next) /\
    (type_memory_size dtv = 0 \/
     w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
     w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size dtv) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         val_in_memory dtv v (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p))) ==>
  (!cenv ctx dtys stys dtvs stvs vs xd xs doff soff dtotal stotal
     sa sb lo explicit func PG s G tn dw sw.
    LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
    LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs) /\
      typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
        (EL i dtvs) (EL i stvs) (EL i vs)) /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv (Var xd) (Var xs)
      dtys stys doff soff sa = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       tuple_in_memory vs stvs (w2n sw + soff) mem) /\
    doff + type_memory_size_list dtvs <= dtotal /\
    soff + type_memory_size_list stvs <= stotal /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (type_memory_size_list stvs = 0 \/
     w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next) /\
    (type_memory_size_list dtvs = 0 \/
     w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size_list dtvs) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         tuple_in_memory vs dtvs (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p)))
Proof
  disch_then (mk_asm "offset") >>
  map_every qx_gen_tac [`cenv`, `ctx`] >> Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_store_memory_typed_def, comp_return_def,
          val_in_memory_def, type_memory_size_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >>
      simp[gas_origin_ptr_path_rules]) >>
  first_x_assum (mk_asm "ih") >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  namedCases_on `stys` ["", "sty stys"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `dtvs` ["", "dtv dtvs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `stvs` ["", "stv stvs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  namedCases_on `vs` ["", "v vs"]
  >- (qpat_x_assum `LENGTH [] = LENGTH (_::_)` mp_tac >> simp[]) >>
  rename1 `compile_typed_copy_fields cenv (Var xd) (Var xs)
    (dty::dtys) (sty::stys) doff soff sa = ((),sb)` >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  qpat_assum `!i. i < SUC (LENGTH dtys) ==> _`
    (qspec_then `0` mp_tac) >>
  simp_tac std_ss [listTheory.EL, listTheory.HD] >>
  strip_tac >>
  qpat_x_assum `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >>
  strip_tac >> rpt (qpat_x_assum `_ /\ _` strip_assume_tac) >>
  rename1 `compile_store_memory_typed cenv dp dty sp sty sc2 = (u,sc)` >>
  Cases_on `u` >>
  `ci_mono sa sc /\ ci_mono sc sb` by
    (asm_x "ih" kall_tac >> asm_x "offset" kall_tac >>
     `ci_mono sa cs' /\ ci_mono cs' sc2` by
       metis_tac[typed_copy_offset_mono] >>
     `ci_mono sc2 sc /\ ci_mono sc sb` by
       metis_tac[cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family,
                 cj 2 exprLoweringPropsTheory.ci_mono_typed_memory_family,
                 pairTheory.SND] >>
     gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sb func` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[fragExecTheory.fn_has_code_split]) >>
  asm "offset" (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_with_byte_offset (Var xd) _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_with_byte_offset (Var xs) _ _ = _`)) >>
  disch_then (drule_at (Pat `typed_copy_origin_ptr_entry _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xd _ _`)) >>
  disch_then (qspecl_then [`lo`, `explicit`, `func`, `PG`] mp_tac) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var xd _ = _`)) >>
  (impl_tac >- (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
    simp[] >> rpt conj_tac >> decide_tac)) >>
  strip_tac >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
     tuple_in_memory vs' stvs' (w2n sw + soff + type_memory_size stv) mem` by
    (`!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory (TupleTV stvs') (ArrayV (TupleV vs'))
         (w2n sw + soff + type_memory_size stv) mem`
       suffices_by (simp_tac (srw_ss()) [val_in_memory_def]) >>
     rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- simp[val_wf_def] >>
     qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tnf.t_mem`,
       `{i | w2n dw + doff <= i /\ i < w2n dw + doff + type_memory_size dtv}`] >>
     asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     simp[val_wf_def, val_in_memory_def, loweringPostsTheory.val_footprint_def,
       type_memory_size_def] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var xs t = SOME sw /\ lookup_var xd t = SOME dw /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     gvs[typed_copy_state_frame_def, venomStateTheory.venom_state_component_equality]) >>
  `not_fresh_at sc xs /\ not_fresh_at sc xd` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
               exprLoweringPropsTheory.ci_mono_def]) >>
  `ptr_covers Gf tnf xs t stotal /\ ptr_covers Gf tnf xd t dtotal` by
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo s` mp_tac >>
     pure_rewrite_tac [allocas_from_def] >> asm_rewrite_tac []) >>
  qpat_x_assum `ptr_covers G tn xs s stotal` kall_tac >>
  qpat_x_assum `ptr_covers G tn xd s dtotal` kall_tac >>
  qpat_x_assum `lookup_var xs s = SOME sw` kall_tac >>
  qpat_x_assum `lookup_var xd s = SOME dw` kall_tac >>
  asm "ih" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xd _ _`)) >>
  disch_then (drule_at (Pat `lookup_var xs _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var xd _ = _`)) >>
  disch_then (qspecl_then [`dtvs'`, `stvs'`, `vs'`, `lo`, `explicit`, `func`, `PG`] mp_tac) >>
  (impl_tac >-
    (asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
     `!i. i < LENGTH dtys ==>
       type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs') /\
       type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs') /\
       typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
         (EL i dtvs') (EL i stvs') (EL i vs')` by
       (rpt strip_tac >>
        qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _`
          (qspec_then `SUC i` mp_tac) >> simp[]) >>
     qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _` kall_tac >>
     rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       (qpat_x_assum `!i. i < LENGTH dtys ==> _` kall_tac >>
        asm_rewrite_tac [allocas_from_def, arithmeticTheory.ADD_ASSOC] >> decide_tac)])) >>
  strip_tac >> asm_x "offset" kall_tac >> asm_x "ih" kall_tac >>
  qpat_x_assum `!i. i < SUC (LENGTH dtys) ==> _` kall_tac >>
  `!mem. mem_agree_outside tnf'.t_mem t'.vs_memory mem ==>
     val_in_memory dtv v (w2n dw + doff) mem` by
    (rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`t.vs_memory`, `t'.vs_memory`, `tnf.t_mem`, `tnf'.t_mem`,
       `{i | w2n dw + (doff + type_memory_size dtv) <= i /\
             i < w2n dw + (doff + type_memory_size dtv) + type_memory_size_list dtvs'}`] >>
     `loweringPosts$val_footprint dtv v <= type_memory_size dtv` by
       metis_tac[exprSimPropsTheory.val_footprint_le] >>
     simp[] >>
     gvs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `typed_copy_state_frame sa (w2n dw + doff)
     (type_memory_size dtv + type_memory_size_list dtvs') s t'` by
    (irule typed_copy_state_frame_trans >> qexists_tac `t` >> conj_tac
     >- (irule typed_copy_state_frame_subinterval >>
         goal_assum (drule_at Any) >> decide_tac) >>
     irule typed_copy_state_frame_subinterval >>
     qexistsl_tac [`w2n dw + (doff + type_memory_size dtv)`,
                  `type_memory_size_list dtvs'`] >>
     simp[] >> irule typed_copy_state_frame_mono >>
     goal_assum (drule_at Any) >>
     metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`t'`, `Gf'`, `tnf'`] >>
  conj_tac
  >- metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
  `val_in_memory dtv v (w2n dw + doff) t'.vs_memory` by
    (qpat_assum `!mem. _ ==> val_in_memory dtv v _ mem`
       (qspec_then `t'.vs_memory` mp_tac) >>
     simp[mem_agree_outside_def]) >>
  rule_assum_tac (SIMP_RULE (srw_ss())
    [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_x_assum `!i. _ ==> (i IN tnf.t_mem <=> i IN tn.t_mem)`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> disch_tac >>
      qpat_x_assum `!i. _ ==> (i IN tnf'.t_mem <=> i IN tnf.t_mem)`
        (qspec_then `i` mp_tac) >>
      (impl_tac >- decide_tac) >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sc p` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono,
              exprLoweringPropsTheory.ci_mono_def] >>
  metis_tac[]
QED

Theorem typed_copy_origin_ptr_byte_offset_path:
  !root off n total sa op sb a lo explicit ctx func PG s G tn base len.
  compile_with_byte_offset (Var root) off sa = (op,sb) /\
  not_fresh_at sa root /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s total /\ off + n <= total /\
  w2n a + off < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p t Gf tnf.
    op = Var p /\ lookup_var p t = SOME (n2w (w2n a + off)) /\
    not_fresh_at sb p /\ ptr_covers Gf tnf p t n /\
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    allocas_from lo t /\ typed_copy_state_frame sa base len s t /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!q. not_fresh_at sa q ==>
      lookup_var q t = lookup_var q s /\ FLOOKUP Gf q = FLOOKUP G q /\
      op_taint tnf (Var q) = op_taint tn (Var q)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >> Cases_on `off = 0`
  >- (gvs[compile_with_byte_offset_def, comp_return_def] >>
      qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
      conj_tac >- (gvs[ptr_covers_def] >> decide_tac) >>
      irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  `?out. op = Var out` by
    (gvs[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def] >> metis_tac[]) >>
  gvs[] >>
  `not_fresh_at sb out /\
   sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]] /\
   (!q. not_fresh_at sa q ==> q <> out)` by
    (gvs[compile_with_byte_offset_def, emit_op_def, comp_bind_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def,
         comp_return_def, not_fresh_at_def] >> metis_tac[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]` >>
  qabbrev_tac `u = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`, `gf`, `tf`] >>
  suspend "add"
QED

Resume typed_copy_origin_ptr_byte_offset_path[add]:
  `w2n (a + n2w off) = w2n a + off` by
    (irule typed_copy_offset_nonwrap >> decide_tac) >>
  conj_tac >- simp[Abbr `u`, lookup_var_def, update_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, GSYM wordsTheory.word_add_n2w,
    arithmeticTheory.ADD_COMM, wordsTheory.WORD_ADD_COMM] >>
  simp[] >> conj_tac >- suspend "coverage" >>
  conj_tac >- suspend "path" >>
  suspend "frame"
QED

Resume typed_copy_origin_ptr_byte_offset_path[coverage]:
  gvs[ptr_covers_def] >>
  simp[Abbr `gf`, Abbr `tf`, Abbr `i`, Abbr `u`,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       op_taint_def, mk_inst_def, eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  decide_tac
QED

Resume typed_copy_origin_ptr_byte_offset_path[path]:
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fragExecTheory.fn_has_code_same_block >>
     simp[] >> metis_tac[arithmeticTheory.ADD_0]) >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS` by
    simp[Abbr `i`, mk_inst_def, is_terminator_def] >>
  `step_inst_base i s = OK u` by suspend "step" >>
  `ptr_inst_ok
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
        d_ret := K {} |>) lo 0 ctx func G tn i s` by suspend "ptr" >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s` by suspend "mem" >>
  `gas_origin_ptr_edge
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
        d_ret := K {} |>,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (u with vs_inst_idx := SUC s.vs_inst_idx),gf,tf)` by
    (simp[Abbr `gf`, Abbr `tf`] >>
     drule_all straight_line_origin_ptr_edge >> simp[Abbr `i`, mk_inst_def,
       is_terminator_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[Abbr `u`, update_var_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[frame]:
  simp[Abbr `u`, update_var_def, allocas_from_def, typed_copy_state_frame_def,
       venom_state_component_equality] >>
  conj_tac >- gvs[allocas_from_def] >>
  conj_tac >- (rpt strip_tac >>
    `x <> out` by metis_tac[] >> simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `i`, step_taint_def,
       step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, imm_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, mk_inst_def, update_var_def] >>
  conj_tac >- simp[new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF,
    pred_setTheory.EXTENSION, SF CONJ_ss] >>
  rpt strip_tac >> `q <> out` by metis_tac[] >>
  Cases_on `FLOOKUP G root` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
       lookup_var_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[step]:
  simp[Abbr `i`, Abbr `u`, step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operand_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[mem]:
  simp[Abbr `i`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def]
QED

Resume typed_copy_origin_ptr_byte_offset_path[ptr]:
  `op_taint tn (Var root) = {}` by gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, Abbr `i`, mk_inst_def, access_ok_def, taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       source_memory_write_ranges_def, op_taint_def] >>
  conj_tac >- (Cases >> gvs[op_taint_def] >> metis_tac[]) >>
  gvs[step_inst_non_invoke, mk_inst_def] >>
  simp[Abbr `u`, update_var_def]
QED

Finalise typed_copy_origin_ptr_byte_offset_path

Theorem typed_copy_origin_ptr_offset_path:
 !cenv ctx dty sty dtv stv v xd xs doff soff dtotal stotal
   sa s1 s2 sb dp sp lo explicit func PG s G tn dw sw.
  typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v /\
  compile_with_byte_offset (Var xd) doff sa = (dp,s1) /\
  compile_with_byte_offset (Var xs) soff s1 = (sp,s2) /\
  compile_store_memory_typed cenv dp dty sp sty s2 = ((),sb) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv v (w2n sw + soff) mem) /\
  doff + type_memory_size dtv <= dtotal /\
  soff + type_memory_size stv <= stotal /\
  w2n sw + soff + type_memory_size stv < dimword (:256) /\
  w2n dw + doff + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/
   w2n sw + soff + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/
   w2n dw + doff + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + soff + type_memory_size stv <= w2n dw + doff \/
   w2n dw + doff + type_memory_size dtv <= w2n sw + soff) /\
  ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    val_in_memory dtv v (w2n dw + doff) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw + doff <= i /\
            i < w2n dw + doff + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory dtv v (w2n dw + doff) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\
       op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb` by
    metis_tac[typed_copy_offset_mono, cj 1 exprLoweringPropsTheory.ci_mono_typed_memory_family, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
   cs_extends s1 sb` by
    (gvs[exprLoweringPropsTheory.ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  qpat_assum `compile_with_byte_offset (Var xd) _ _ = _`
    (mp_then Any mp_tac typed_copy_origin_ptr_byte_offset_path) >>
  disch_then (qspecl_then [`type_memory_size dtv`, `dtotal`, `dw`,
    `lo`, `explicit`, `ctx`, `func`, `PG`, `s`, `G`, `tn`,
    `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  `not_fresh_at s1 xs` by
    (gvs[not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `lookup_var xs t = SOME sw /\ ptr_covers Gf tnf xs t stotal` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  qpat_assum `compile_with_byte_offset (Var xs) _ _ = _`
    (mp_then Any mp_tac typed_copy_origin_ptr_byte_offset_path) >>
  disch_then (qspecl_then [`type_memory_size stv`, `stotal`, `sw`,
    `lo`, `explicit`, `ctx`, `func`, `PG`, `t`, `Gf`, `tnf`,
    `w2n dw + doff`, `type_memory_size dtv`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  `not_fresh_at s2 p` by
    (gvs[not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `lookup_var p t' = SOME (n2w (w2n dw + doff)) /\
   ptr_covers Gf' tnf' p t' (type_memory_size dtv)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `w2n (n2w (w2n dw + doff):256 word) = w2n dw + doff /\
   w2n (n2w (w2n sw + soff):256 word) = w2n sw + soff` by
    (simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  qpat_x_assum `dp = _` SUBST_ALL_TAC >>
  qpat_x_assum `sp = _` SUBST_ALL_TAC >>
  drule typed_copy_origin_ptr_entry_run >>
  disch_then drule >>
  disch_then (qspecl_then [`tnf'`, `n2w (w2n sw + soff)`, `t'`,
    `lo`, `func`, `explicit`, `n2w (w2n dw + doff)`, `PG`, `Gf'`] mp_tac) >>
  (impl_tac >- (fs[arithmeticTheory.ADD_COMM] >> metis_tac[])) >> strip_tac >>
  qpat_assum `w2n (n2w (w2n dw + doff)) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `ci_mono sa s2` by
    (gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) t t'` by
    (irule typed_copy_state_frame_mono >> qexists_tac `s1` >> simp[]) >>
  `typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) t' t''` by
    (irule typed_copy_state_frame_mono >> qexists_tac `s2` >> simp[]) >>
  `typed_copy_state_frame sa (w2n dw + doff) (type_memory_size dtv) s t''` by
    metis_tac[typed_copy_state_frame_trans] >>
  qexistsl_tac [`t''`, `Gf''`, `tnf''`] >>
  conj_tac >- (metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at s1 p'' /\ not_fresh_at s2 p''` by
    (gvs[not_fresh_at_def, exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem tuple_val_wf_LIST_REL:
  !tvs vs. LENGTH vs = LENGTH tvs ==>
    (tuple_val_wf vs tvs <=> LIST_REL val_wf tvs vs)
Proof
  Induct >> Cases_on `vs` >> simp[val_wf_def]
QED

Theorem typed_copy_origin_ptr_tuple_entry_from_fields:
  (!cenv ctx dtys stys dtvs stvs vs xd xs doff soff dtotal stotal
     sa sb lo explicit func PG s G tn dw sw.
    LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
    LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs) /\
      typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
        (EL i dtvs) (EL i stvs) (EL i vs)) /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv (Var xd) (Var xs)
      dtys stys doff soff sa = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       tuple_in_memory vs stvs (w2n sw + soff) mem) /\
    doff + type_memory_size_list dtvs <= dtotal /\
    soff + type_memory_size_list stvs <= stotal /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (type_memory_size_list stvs = 0 \/
     w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next) /\
    (type_memory_size_list dtvs = 0 \/
     w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size_list dtvs) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         tuple_in_memory vs dtvs (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p))) ==>

  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  disch_then (mk_asm "fields") >>
  rpt gen_tac >> strip_tac >>
  `?stys. sty = TupleT stys` by metis_tac[typed_copy_tuple_widening] >> gvs[] >>
  `LIST_REL (type_widens_to tenv) stys dtys` by
    (`!ss ds. (ss = ds \/ arg_types_fit ss ds) /\
         (?tvs. OPT_MMAP (evaluate_type tenv) ds = SOME tvs) ==>
         LIST_REL (type_widens_to tenv) ss ds` suffices_by
       (strip_tac >> drule typed_copy_tuple_widening >>
        gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
        metis_tac[]) >>
     Induct >> Cases_on `ds` >>
     simp[arg_type_fits_def, OPT_MMAP_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     simp[type_widens_to_def, well_formed_type_def] >> metis_tac[]) >>
  gvs[evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  `LENGTH stys = LENGTH dtys /\ LENGTH tvs' = LENGTH dtys /\
   LENGTH tvs = LENGTH dtys /\ LENGTH l = LENGTH dtys /\
   (!i. i < LENGTH dtys ==>
     type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i tvs') /\
     type_memory_bytes cenv (EL i stys) = type_memory_size (EL i tvs) /\
     typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
       (EL i tvs') (EL i tvs) (EL i l))` by
    (gvs[vyperMiscTheory.OPT_MMAP_SOME_IFF, LIST_REL_EL_EQN,
         EVERY_MAP, EVERY_EL, LENGTH_MAP] >>
     `LENGTH l = LENGTH dtys` by
       metis_tac[values_have_types_length, LENGTH_MAP] >> simp[] >>
     rpt strip_tac >> simp[EL_MAP] >>
     `evaluate_type tenv (EL i dtys) = SOME (THE (evaluate_type tenv (EL i dtys))) /\
      evaluate_type tenv (EL i stys) = SOME (THE (evaluate_type tenv (EL i stys)))` by
       (`IS_SOME (evaluate_type tenv (EL i dtys)) /\
         IS_SOME (evaluate_type tenv (EL i stys))` by metis_tac[] >>
        Cases_on `evaluate_type tenv (EL i dtys)` >>
        Cases_on `evaluate_type tenv (EL i stys)` >> gvs[])
     >- (irule typed_copy_memory_size >> qexists_tac `tenv` >>
         simp[] >> metis_tac[EVERY_EL])
     >- (irule typed_copy_memory_size >> qexists_tac `tenv` >>
         simp[] >> metis_tac[EVERY_EL]) >>
     qpat_x_assum `!cd cs cdt cst cv. _` irule >>
     (conj_tac >- metis_tac[typedCopyDomainTheory.member_rank_lt_tuple, MEM_EL]) >>
     gvs[val_wf_def, tuple_val_wf_LIST_REL,
         vyperTypeDefaultsTheory.values_have_types_LIST_REL,
         LIST_REL_EL_EQN, EL_MAP]) >>
  pure_rewrite_tac[typed_copy_origin_ptr_entry_def] >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def] >> strip_tac >>
  asm "fields" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[val_in_memory_def, type_memory_size_def] >>
  disch_then irule >>
  gnvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  conj_tac >- (qexists_tac `type_memory_size_list tvs'` >> simp[]) >>
  qexistsl_tac [`type_memory_size_list tvs`, `tvs`] >>
  simp[]
QED

Theorem typed_copy_origin_ptr_struct_entry_from_fields:
  (!cenv ctx dtys stys dtvs stvs vs xd xs doff soff dtotal stotal
     sa sb lo explicit func PG s G tn dw sw.
    LENGTH stys = LENGTH dtys /\ LENGTH dtvs = LENGTH dtys /\
    LENGTH stvs = LENGTH dtys /\ LENGTH vs = LENGTH dtys /\
    (!i. i < LENGTH dtys ==>
      type_memory_bytes cenv (EL i dtys) = type_memory_size (EL i dtvs) /\
      type_memory_bytes cenv (EL i stys) = type_memory_size (EL i stvs) /\
      typed_copy_origin_ptr_entry cenv ctx (EL i dtys) (EL i stys)
        (EL i dtvs) (EL i stvs) (EL i vs)) /\
    tuple_val_wf vs stvs /\ tuple_val_wf vs dtvs /\
    compile_typed_copy_fields cenv (Var xd) (Var xs)
      dtys stys doff soff sa = ((),sb) /\
    not_fresh_at sa xs /\ not_fresh_at sa xd /\
    lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       tuple_in_memory vs stvs (w2n sw + soff) mem) /\
    doff + type_memory_size_list dtvs <= dtotal /\
    soff + type_memory_size_list stvs <= stotal /\
    w2n sw + soff + type_memory_size_list stvs < dimword (:256) /\
    w2n dw + doff + type_memory_size_list dtvs < dimword (:256) /\
    (type_memory_size_list stvs = 0 \/
     w2n sw + soff + type_memory_size_list stvs <= s.vs_alloca_next) /\
    (type_memory_size_list dtvs = 0 \/
     w2n dw + doff + type_memory_size_list dtvs <= s.vs_alloca_next) /\
    (w2n sw + soff + type_memory_size_list stvs <= w2n dw + doff \/
     w2n dw + doff + type_memory_size_list dtvs <= w2n sw + soff) /\
    ptr_covers G tn xs s stotal /\ ptr_covers G tn xd s dtotal /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t Gf tnf.
      gas_origin_ptr_path
        (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
            d_ret := K {} |>,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,Gf,tnf) /\
      tuple_in_memory vs dtvs (w2n dw + doff) t.vs_memory /\
      typed_copy_state_frame sa (w2n dw + doff)
        (type_memory_size_list dtvs) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\
      tnf.t_trans = tn.t_trans /\
      (!i. ~(w2n dw + doff <= i /\
              i < w2n dw + doff + type_memory_size_list dtvs) ==>
           (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
         tuple_in_memory vs dtvs (w2n dw + doff) mem) /\
      (!p. not_fresh_at sa p ==>
         FLOOKUP Gf p = FLOOKUP G p /\
         op_taint tnf (Var p) = op_taint tn (Var p))) ==>
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (StructT name) sty dtv stv v
Proof
  disch_then (markerLib.mk_asm "runtime") >>
  rpt gen_tac >> strip_tac >>
  drule typed_copy_struct_widening >> strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  rename1 `FLOOKUP tenv name = SOME (StructArgs args)` >>
  `?fields. FLOOKUP cenv.ce_struct_fields (nsid_to_string name) = SOME fields /\
     MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args` by
    (fs[sfields_tenv_consistent_def] >> metis_tac[]) >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyperTypeExprSoundnessTheory.evaluate_type_mono] >>
  `LENGTH (MAP FST args) = LENGTH tvs` by
    (gvs[evaluate_types_OPT_MMAP] >>
     drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  Cases_on `v` >> gvs[value_has_type_def, val_wf_def] >>
  `?vs. l = ZIP (MAP FST args,vs) /\ LENGTH vs = LENGTH args /\
        values_have_types tvs vs /\ tuple_val_wf vs tvs` by
    (drule_at (Pat `struct_has_type _ _`) typed_copy_struct_values >> simp[] >>
     disch_then drule_all >> simp[]) >> gvs[] >>
  `OPT_MMAP (evaluate_type tenv) (MAP (FST o SND) fields) = SOME tvs` by
    gvs[evaluate_types_OPT_MMAP] >>
  suspend "alignment"
QED

Resume typed_copy_origin_ptr_struct_entry_from_fields[alignment]:
  `!ty tv. evaluate_type tenv ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule typed_copy_memory_size >>
     qexists_tac `tenv` >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP FST fields) /\
   EVERY (\(fname,fty,sz). sz = type_memory_bytes cenv fty) fields` by
    (conj_tac >- metis_tac[] >>
     irule typed_copy_struct_field_bytes >>
     qexistsl_tac [`tenv`, `tvs`] >> simp[] >> metis_tac[]) >>
  `!i. i < LENGTH (MAP (FST o SND) fields) ==>
     type_memory_bytes cenv (EL i (MAP (FST o SND) fields)) =
       type_memory_size (EL i tvs) /\
     typed_copy_origin_ptr_entry cenv ctx (EL i (MAP (FST o SND) fields))
       (EL i (MAP (FST o SND) fields)) (EL i tvs) (EL i tvs) (EL i vs)` by
    suspend "children" >>
  `type_memory_size_fields (ZIP (MAP FST args,tvs)) = type_memory_size_list tvs` by
    (qpat_x_assum `LENGTH args = LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> qid_spec_tac `tvs` >>
     Induct_on `args` >> Cases_on `tvs` >> simp[type_memory_size_def]) >>
  rewrite_tac[typed_copy_origin_ptr_entry_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  gnvs[type_memory_size_def, val_in_memory_def, typed_copy_fields_tuple_zip] >>
  suspend "run"
QED

Resume typed_copy_origin_ptr_struct_entry_from_fields[children]:
  gen_tac >> disch_tac >>
  drule vyperTypeABITheory.OPT_MMAP_LIST_REL >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
  `evaluate_type tenv (EL i (MAP (FST o SND) fields)) = SOME (EL i tvs)` by
    gvs[] >>
  (conj_tac >- metis_tac[]) >>
  `type_rank cenv.ce_struct_fields (EL i (MAP (FST o SND) fields)) <
     type_rank cenv.ce_struct_fields (StructT name)` by suspend "rank" >>
  `value_has_type (EL i tvs) (EL i vs) /\ val_wf (EL i tvs) (EL i vs)` by
    (`i < LENGTH tvs` by gvs[] >>
     qpat_x_assum `values_have_types tvs vs` mp_tac >>
     qpat_x_assum `tuple_val_wf vs tvs` mp_tac >>
     qpat_x_assum `i < LENGTH tvs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[] >>
     qid_spec_tac `i` >> qid_spec_tac `vs` >>
     Induct_on `tvs` >> Cases_on `vs` >>
     simp[value_has_type_def, val_wf_def] >> rpt strip_tac >>
     Cases_on `i` >> gvs[] >> metis_tac[]) >>
  first_x_assum irule >> simp[vyperTypeArgFitsTheory.type_widens_to_refl] >> gvs[]
QED

Resume typed_copy_origin_ptr_struct_entry_from_fields[rank]:
  `MEM (EL i (MAP (FST o SND) fields)) (MAP (FST o SND) fields)` by
    simp[listTheory.EL_MEM] >>
  qpat_x_assum `MAP (FST o SND) fields = _` kall_tac >>
  fs[listTheory.MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  `MEM (y0,EL i (MAP (FST o SND) fields),y2)
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string name))` by
    simp[compileEnvTheory.get_struct_fields_def] >>
  drule_all typedCopyDomainTheory.member_rank_lt_struct >>
  simp[typedCopyDomainTheory.type_rank_def, compileEnvTheory.nsid_to_string_def]
QED

Resume typed_copy_origin_ptr_struct_entry_from_fields[run]:
  `MAP (\(name,ty,sz). ty) fields = MAP (FST o SND) fields` by
    (irule listTheory.MAP_CONG >> simp[pairTheory.FORALL_PROD]) >>
  `compile_struct_typed_copy cenv (Var xd) (Var xs) fields fields 0 0 =
   compile_typed_copy_fields cenv (Var xd) (Var xs)
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0` by
    (qpat_assum `MAP _ fields = MAP (FST o SND) fields`
       (fn th => rewrite_tac[GSYM th]) >>
     irule typed_copy_struct_fields_producer >> simp[listTheory.EVERY_MEM]) >>
  qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def,
       compileEnvTheory.is_word_type_def, compileEnvTheory.is_bytestring_type_def] >>
  strip_tac >>
  `compile_typed_copy_fields cenv (Var xd) (Var xs)
      (MAP (FST o SND) fields) (MAP (FST o SND) fields) 0 0 sa = ((),sb)` by
    gvs[compileEnvTheory.get_struct_fields_def] >>
  `LENGTH fields = LENGTH tvs` by
    (qpat_x_assum `MAP FST fields = MAP FST args`
       (mp_tac o AP_TERM ``LENGTH : string list -> num``) >> simp[]) >>
  asm "runtime" (drule_at (Pat `compile_typed_copy_fields _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then irule >>
  simp[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (qexists_tac `type_memory_size_list tvs` >> simp[]) >>
  qexistsl_tac [`type_memory_size_list tvs`, `tvs`] >> gvs[]
QED

Finalise typed_copy_origin_ptr_struct_entry_from_fields

Theorem typed_copy_origin_ptr_tuple_entry:
  !cenv tenv ctx dtys sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (TupleT dtys) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (TupleT dtys) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (TupleT dtys) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (TupleT dtys) sty dtv stv v
Proof
  cheat
QED

Theorem typed_copy_origin_ptr_struct_entry:
  !cenv tenv ctx name sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (StructT name) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (StructT name) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (StructT name) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (StructT name) sty dtv stv v
Proof
  cheat
QED
