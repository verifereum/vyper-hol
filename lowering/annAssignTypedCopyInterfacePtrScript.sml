(* Conditional recursive field boundary.  I carries the ambient pointer,
   declaration and control invariant; representation is robust, not clean. *)
Theory annAssignTypedCopyInterfacePtr
Ancestors
  assignBasePtrFieldsCompose typedCopyRobustTransportPtr context compileEnv
  valueEncodingDefs valueEncoding venomState fragGasPathPtr

Theorem annassign_typed_copy_cons_counted_robust:
  !ce dst src dt dts st sts doff soff sa sb sc sd sz dp sp
   D ctx fn PG I a b dtv stv dtvs stvs v vs.
    compile_with_byte_offset dst doff sa = (dp,sb) /\
    compile_with_byte_offset src soff sb = (sp,sc) /\
    compile_store_memory_typed ce dp dt sp st sc = ((),sd) /\
    compile_typed_copy_fields ce dst src dts sts
      (doff + type_memory_bytes ce dt) (soff + type_memory_bytes ce st) sd = ((),sz) /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    type_memory_bytes ce st = type_memory_size stv /\
    val_wf dtv v /\ val_wf (TupleTV stvs) (ArrayV (TupleV vs)) /\
    (a + soff + type_memory_size stv + type_memory_size_list stvs <= b + doff \/
     b + doff + type_memory_size dtv <= a + soff + type_memory_size stv) /\
    (!G tn s.
      I sa G tn s /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory stv v (a + soff) m) ==>
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\ I sd H tm t /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv v (b + doff) m) /\
        (!i. ~(b + doff <= i /\ i < b + doff + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem))) /\
    (!H tm t.
      I sd H tm t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        tuple_in_memory vs stvs (a + soff + type_memory_size stv) m) ==>
      ?K tf u.
        gas_path_ptr D 0 ctx fn PG H tm t 0 K tf (OK u) /\ I sz K tf u /\
        (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
          tuple_in_memory vs dtvs (b + doff + type_memory_size dtv) m) /\
        (!i. ~(b + doff + type_memory_size dtv <= i /\
               i < b + doff + type_memory_size dtv + type_memory_size_list dtvs) ==>
          mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 t.vs_memory /\
          (i IN tf.t_mem <=> i IN tm.t_mem))) ==>
    compile_typed_copy_fields ce dst src (dt::dts) (st::sts)
      doff soff sa = ((),sz) /\
    !G tn s.
      I sa G tn s /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        tuple_in_memory (v::vs) (stv::stvs) (a + soff) m) ==>
      ?K tf u.
        gas_path_ptr D 0 ctx fn PG G tn s 0 K tf (OK u) /\ I sz K tf u /\
        (!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
          tuple_in_memory (v::vs) (dtv::dtvs) (b + doff) m) /\
        (!i. ~(b + doff <= i /\
               i < b + doff + type_memory_size_list (dtv::dtvs)) ==>
          mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> disch_tac >> RULE_L_ASSUM_TAC CONJUNCTS >> conj_tac
  >- (simp[Once compile_store_memory_typed_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def] >> fs[]) >>
  rpt gen_tac >> strip_tac >>
  `(!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory stv v (a + soff) m) /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory (TupleTV stvs) (ArrayV (TupleV vs))
         (a + soff + type_memory_size stv) m)` by
    (qpat_x_assum `!m. _ ==> tuple_in_memory (v::vs) _ _ m` mp_tac >>
     simp[Once val_in_memory_def,
          GSYM valueEncodingPropsTheory.val_in_memory_tuple] >>
     metis_tac[]) >>
  qpat_x_assum `!G tn s. _` drule_all >> strip_tac >>
  `!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
       tuple_in_memory vs stvs (a + soff + type_memory_size stv) m` by
    (pure_rewrite_tac[GSYM valueEncodingPropsTheory.val_in_memory_tuple] >>
     rpt strip_tac >> irule robust_representation_exterior_frame >>
     conj_tac >- simp[] >>
     qexistsl_tac [`b + doff`, `s.vs_memory`, `t.vs_memory`,
       `type_memory_size dtv`, `tn.t_mem`, `tm.t_mem`] >>
     simp[type_memory_size_def] >> metis_tac[]) >>
  qpat_x_assum `!H tm t. _` drule_all >> strip_tac >>
  rename1 `gas_path_ptr D 0 ctx fn PG H tm t 0 Hf tf (OK u)` >>
  qexistsl_tac [`Hf`, `tf`, `u`] >> conj_tac
  >- (`gas_path_ptr D 0 ctx fn PG G tn s (0+0) Hf tf (OK u)` by
        (irule gas_path_ptr_then >> goal_assum (drule_at Any) >> simp[]) >> fs[]) >>
  simp[] >> conj_tac
  >- (simp[Once val_in_memory_def] >> rpt strip_tac >>
      irule robust_representation_exterior_frame >>
      conj_tac >- simp[] >>
      qexistsl_tac [`b + doff + type_memory_size dtv`,
        `t.vs_memory`, `u.vs_memory`, `type_memory_size_list dtvs`,
        `tm.t_mem`, `tf.t_mem`] >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `~(b + doff <= i /\ i < b + doff + type_memory_size dtv) /\
   ~(b + doff + type_memory_size dtv <= i /\
     i < b + doff + type_memory_size dtv + type_memory_size_list dtvs)` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  metis_tac[]
QED
