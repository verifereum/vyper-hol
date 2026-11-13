(* Value-indexed compiler-relative dynamic payload execution. *)
Theory annAssignTypedCopyDynamicSlowAdmissiblePtr
Ancestors
  annAssignTypedCopyDynamicCompilerResourcesPtr
  annAssignTypedCopyDynamicLoopPtr annAssignTypedCopyDynamicTestPtr
  annAssignTypedCopyFixedControlPtr typedNormalizeDynarrayLoop
  typedMemoryCopy bodyPtrDefs compileEnv emitHelper fragExec exprLoweringProps
  venomState venomInst venomExecSemantics words arithmetic list rich_list

Theorem annassign_dynamic_slow_payload_admissible_counted:
  !ce dst_op dt cap src_op st sa sb fn s src dst L f stv dtv G tn D ctx PG P.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst_op dt cap src_op st sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
    type_memory_bytes ce st = type_memory_size stv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    src + L * type_memory_size stv < dimword(:256) /\
    dst + L * type_memory_size dtv < dimword(:256) /\
    (src + L * type_memory_size stv <= dst \/
     dst + L * type_memory_size dtv <= src) /\ L < dimword(:256) /\
    (!i. i < L ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    (!i. i < L ==> P (f i)) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\ ~s.vs_halted /\
    lookup_var ("%" ++ toString sa.cs_next_var) s = SOME (n2w L) /\
    op_taint tn (Var ("%" ++ toString sa.cs_next_var)) = {} /\
    FLOOKUP G ("%" ++ toString sa.cs_next_var) = NONE /\
    lookup_var ("%" ++ toString (sa.cs_next_var+3)) s = SOME (n2w src) /\
    lookup_var ("%" ++ toString (sa.cs_next_var+4)) s = SOME (n2w dst) /\
    ptr_covers G tn ("%" ++ toString (sa.cs_next_var+3)) s (L * type_memory_size stv) /\
    ptr_covers G tn ("%" ++ toString (sa.cs_next_var+4)) s (L * type_memory_size dtv) /\
    (!i. i < L ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!sc se xr yr u aw bw H tm v.
      compile_store_memory_typed ce (Var yr) dt (Var xr) st sc = ((),se) /\
      fn_has_code sc se fn /\ not_fresh_at sc xr /\ not_fresh_at sc yr /\
      u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
      lookup_var xr u = SOME aw /\ lookup_var yr u = SOME bw /\
      ptr_covers H tm xr u (type_memory_size stv) /\
      ptr_covers H tm yr u (type_memory_size dtv) /\
      w2n aw + type_memory_size stv < dimword(:256) /\
      w2n bw + type_memory_size dtv < dimword(:256) /\
      (w2n aw + type_memory_size stv <= w2n bw \/
       w2n bw + type_memory_size dtv <= w2n aw) /\
      val_wf stv v /\ val_wf dtv v /\ P v /\
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
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        typed_copy_index_prefix f dtv dst L L m) /\
      typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
      (!i. ~(dst <= i /\ i < dst + L * type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
        x = "%" ++ toString (sa.cs_next_var+4) \/ x = "%" ++ toString sa.cs_next_var ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `!sc se xr yr u aw bw H tm v. _` (mk_asm "child") >>
  drule_all annassign_dynamic_child_frontier >> strip_tac >>
  `?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    t.vs_current_bb = fresh_label_output "typed_dyn_cond" sa.cs_next_label /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    lookup_var ("%" ++ toString (sa.cs_next_var+5)) t = SOME 0w /\
    op_taint tm (Var ("%" ++ toString (sa.cs_next_var+5))) = {} /\
    FLOOKUP H ("%" ++ toString (sa.cs_next_var+5)) = NONE /\
    typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
    t.vs_memory = s.vs_memory /\ tm.t_mem = tn.t_mem /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. x <> "%" ++ toString (sa.cs_next_var+5) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))` by
    (irule annassign_dynamic_compiler_entry >> simp[] >> metis_tac[]) >>
  `?K tk u. gas_path_ptr D 0 ctx fn PG H tm t 0 K tk (OK u) /\
    u.vs_current_bb = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    u.vs_inst_idx = 0 /\ ~u.vs_halted /\
    (!m. mem_agree_outside tk.t_mem u.vs_memory m ==>
      typed_copy_index_prefix f dtv dst L L m) /\
    typed_copy_state_frame sa dst (L * type_memory_size dtv) t u /\
    (!i. ~(dst <= i /\ i < dst + L * type_memory_size dtv) ==>
      mem_bytes_at i 1 u.vs_memory = mem_bytes_at i 1 t.vs_memory /\
      (i IN tk.t_mem <=> i IN tm.t_mem)) /\
    tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
    (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
      x = "%" ++ toString (sa.cs_next_var+4) \/ x = "%" ++ toString sa.cs_next_var ==>
      lookup_var x u = lookup_var x t /\ FLOOKUP K x = FLOOKUP H x /\
      op_taint tk (Var x) = op_taint tm (Var x))` by
    (rule_assum_tac (SRULE []) >>
     `!j. j < 5 ==> lookup_var ("%" ++ toString (sa.cs_next_var+j)) t =
       lookup_var ("%" ++ toString (sa.cs_next_var+j)) s /\
       FLOOKUP H ("%" ++ toString (sa.cs_next_var+j)) =
       FLOOKUP G ("%" ++ toString (sa.cs_next_var+j)) /\
       op_taint tm (Var ("%" ++ toString (sa.cs_next_var+j))) =
       op_taint tn (Var ("%" ++ toString (sa.cs_next_var+j)))` by
       (rpt strip_tac >> simp[]) >>
     map_every (fn j => qpat_assum `!j. j < 5 ==> _`
       (qspec_then j (assume_tac o SRULE []))) [`0`,`3`,`4`] >>
     `ptr_covers H tm ("%" ++ toString (sa.cs_next_var+3)) t
        (L * type_memory_size stv)` by gvs[ptr_covers_def] >>
     `ptr_covers H tm ("%" ++ toString (sa.cs_next_var+4)) t
        (L * type_memory_size dtv)` by gvs[ptr_covers_def] >>
     irule annassign_dynamic_payload_loop >> simp[] >>
     qexistsl [`cap`,`ce`,`dst_op`,`dt`,`sb`,`se`,`si`,`src`,`src_op`,`st`,`stv`] >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         irule annassign_dynamic_loop_address >> simp[] >>
         `k * type_memory_size stv < L * type_memory_size stv /\
          k * type_memory_size dtv < L * type_memory_size dtv /\
          (k+1) * type_memory_size stv <= L * type_memory_size stv /\
          (k+1) * type_memory_size dtv <= L * type_memory_size dtv` by simp[] >>
         rpt conj_tac
         >- decide_tac
         >- decide_tac
         >- (qexistsl [`cap`,`ce`,`dst_op`,`dt`,`sb`,`src_op`,`st`] >> simp[])
         >- (qexists_tac `L * type_memory_size dtv` >> simp[] >>
             gvs[RIGHT_ADD_DISTRIB] >> decide_tac) >>
         qexists_tac `L * type_memory_size stv` >> simp[] >>
         gvs[RIGHT_ADD_DISTRIB] >> decide_tac) >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         irule (SRULE [] annassign_dynamic_loop_backedge) >> simp[] >>
         qexistsl [`back`,`se`] >> simp[] >>
         `si.cs_next_var <= se.cs_next_var` by
           (qspec_then `ce` mp_tac (cj 1 ci_mono_typed_memory_family) >>
            disch_then (qspec_then `Var ("%" ++ toString (sa.cs_next_var+11))` mp_tac) >>
            disch_then (qspec_then `dt` mp_tac) >>
            disch_then (qspec_then `Var ("%" ++ toString (sa.cs_next_var+10))` mp_tac) >>
            disch_then (qspec_then `st` mp_tac) >>
            disch_then (qspec_then `si` mp_tac) >> simp[ci_mono_def]) >>
         conj_tac >- decide_tac >> metis_tac[cs_extends_trans]) >>
     reverse conj_tac
     >- (conj_tac
         >- (rpt gen_tac >> strip_tac >>
             irule (SRULE [] annassign_dynamic_loop_test) >> simp[] >>
             qexistsl [`cap`,`ce`,`dst_op`,`dt`,`sb`,`src_op`,`st`] >> simp[]) >> fs[]) >>
     rpt gen_tac >> strip_tac >>
     `not_fresh_at si ("%" ++ toString (sa.cs_next_var+10)) /\
      not_fresh_at si ("%" ++ toString (sa.cs_next_var+11))` by simp[] >>
     `k * type_memory_size stv < L * type_memory_size stv /\
      k * type_memory_size dtv < L * type_memory_size dtv /\
      (k+1) * type_memory_size stv <= L * type_memory_size stv /\
      (k+1) * type_memory_size dtv <= L * type_memory_size dtv` by simp[] >>
     `src + k * type_memory_size stv + type_memory_size stv < dimword (:256) /\
      dst + k * type_memory_size dtv + type_memory_size dtv < dimword (:256) /\
      (src + k * type_memory_size stv + type_memory_size stv <= dst + k * type_memory_size dtv \/
       dst + k * type_memory_size dtv + type_memory_size dtv <= src + k * type_memory_size stv)` by
       (rule_assum_tac (PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB]) >> decide_tac) >>
     `w2n (n2w (src + k * type_memory_size stv):256 word) = src + k * type_memory_size stv /\
      w2n (n2w (dst + k * type_memory_size dtv):256 word) = dst + k * type_memory_size dtv` by
       (simp[wordsTheory.w2n_n2w] >> conj_tac >> irule LESS_MOD >> decide_tac) >>
     `val_wf stv (f k) /\ val_wf dtv (f k) /\ P (f k)` by simp[] >>
     rule_assum_tac (SRULE []) >> asm "child" drule >>
     disch_then (qspec_then `s''` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`G'`,`tn'`,`f k`] mp_tac) >> simp[] >>
     strip_tac >> qexistsl [`K'`,`tk`,`z`] >> simp[] >>
     reverse conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     qpat_x_assum `typed_copy_state_frame si _ _ s'' z` mp_tac >>
     simp[typed_copy_state_frame_def] >> strip_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  qexistsl [`K'`,`tk`,`u`] >> conj_tac
  >- (ntac 2 (qpat_x_assum `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _` mp_tac) >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[fragGasPathPtrTheory.gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]) >>
  simp[] >> conj_tac >- metis_tac[typed_copy_state_frame_trans] >>
  qx_gen_tac `x` >> disch_tac >>
  `x <> "%" ++ toString (sa.cs_next_var+5)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def,
       ASCIInumbersTheory.toString_inj] >> rpt strip_tac >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
  qpat_x_assum `!x. (not_fresh_at sa x \/ _) ==> _` (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!x. x <> _ ==> _` (qspec_then `x` mp_tac) >> simp[]
QED
