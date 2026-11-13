(* Assembly boundaries for dynamic aggregate normalization. *)
Theory annAssignTypedCopyDynamicPtr
Ancestors
  annAssignTypedCopyDynamicCompilerResourcesPtr
  annAssignTypedCopyDynamicHeaderPtr annAssignTypedCopyDynamicBulkPtr
  annAssignTypedCopyDynamicTestPtr annAssignTypedCopyDynamicLoopPtr
  annAssignTypedCopyDynamicBulkAdapterPtr annAssignTypedCopyDynamicLoopAdapterPtr
  fragGasPathPtr valueEncodingDefs valueEncoding typedCopyRobustTransportPtr
  reasonCopySourcePtr
  typedNormalizeDynarray typedMemoryCopy normalizationPrefixPtr
  annAssignTypedCopyFixedMetadataPtr exprLoweringProps fragExec
  bodyPtrDefs context compileEnv emitHelper venomState venomInst
  venomExecSemantics words arithmetic list rich_list freshWrites ASCIInumbers loweringStateRelDefs

Theorem annassign_dynarray_counted_ptr:
 !ce tenv dt st dtv stv C S vs dst src sa sb fn s b a G tn D ctx PG.
 compile_copy_dynarray_typed ce (Var dst) dt C (Var src) st sa = ((),sb) /\
 type_memory_bytes ce dt = type_memory_size dtv /\
 type_memory_bytes ce st = type_memory_size stv /\
 type_widens_to tenv st dt /\
 evaluate_type tenv (ArrayT st (Dynamic S)) = SOME (ArrayTV stv (Dynamic S)) /\
 evaluate_type tenv (ArrayT dt (Dynamic C)) = SOME (ArrayTV dtv (Dynamic C)) /\
 value_has_type (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV stv (Dynamic S)) (ArrayV (DynArrayV vs)) /\
 val_wf (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) /\
 not_fresh_at sa src /\ not_fresh_at sa dst /\
 fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
 ~ctx_has_dalloca ctx /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (32 + S * type_memory_size stv) /\
 ptr_covers G tn dst s (32 + C * type_memory_size dtv) /\
 C < dimword (:256) /\
 w2n a + (32 + S * type_memory_size stv) < dimword (:256) /\
 w2n b + (32 + C * type_memory_size dtv) < dimword (:256) /\
 (w2n a + (32 + S * type_memory_size stv) <= w2n b \/
  w2n b + (32 + C * type_memory_size dtv) <= w2n a) /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   val_in_memory (ArrayTV stv (Dynamic S)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
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
   typed_copy_state_frame sa (w2n b) (32 + C * type_memory_size dtv) s t /\
   (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
     val_in_memory (ArrayTV dtv (Dynamic C)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
   tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
   (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)) /\
   (!i. ~(w2n b <= i /\ i < w2n b + (32 + C * type_memory_size dtv)) ==>
     mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
     (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
 rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
 qpat_x_assum `!sc se xr yr u aw bw H tm v. _` (mk_asm "child") >>
 rename1 `ArrayTV stv (Dynamic scap)` >>
 `LENGTH vs <= scap /\ LENGTH vs <= C /\
  (!i. i < LENGTH vs ==> val_wf stv (EL i vs) /\ val_wf dtv (EL i vs))` by
   (gvs[typed_copy_dynarray_wf] >> metis_tac[]) >>
 `w2n a + 32 < dimword (:256) /\ w2n b + 32 < dimword (:256)` by decide_tac >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   mem_word_at (w2n a) m = n2w (LENGTH vs)` by
   (rpt strip_tac >> first_x_assum drule >> simp[typed_copy_dynarray_representation]) >>
 drule_all (SRULE [] (Q.INST [
   `len` |-> `"%" ++ toString sa.cs_next_var`,
   `long` |-> `"%" ++ toString (sa.cs_next_var+1)`,
   `ok` |-> `"%" ++ toString (sa.cs_next_var+2)`,
   `sp` |-> `"%" ++ toString (sa.cs_next_var+3)`,
   `dp` |-> `"%" ++ toString (sa.cs_next_var+4)`]
   annassign_dynamic_compiler_header)) >>
 disch_then (qspecl_then [`D`,`PG`] mp_tac) >>
 simp[] >> strip_tac >>
 `!m. mem_agree_outside tf.t_mem u.vs_memory m ==>
   val_in_memory (ArrayTV stv (Dynamic scap)) (ArrayV (DynArrayV vs)) (w2n a) m` by
   (rpt strip_tac >> irule robust_representation_exterior_frame >>
    conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
    qexistsl_tac [`w2n b`,`s.vs_memory`,`u.vs_memory`,`32`,`tn.t_mem`,`tf.t_mem`] >>
    simp[type_memory_size_def] >> gvs[]) >>
 `!i. i < LENGTH vs ==> !m. mem_agree_outside tf.t_mem u.vs_memory m ==>
   val_in_memory stv (EL i vs) (w2n a + 32 + i * type_memory_size stv) m` by
   (rpt strip_tac >>
    qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV _ _) _ _ _` drule >>
    simp[typed_copy_dynarray_representation]) >>
 `LENGTH vs * type_memory_size stv <= scap * type_memory_size stv /\
  LENGTH vs * type_memory_size dtv <= C * type_memory_size dtv` by simp[] >>
 `ptr_covers H tf ("%" ++ toString (sa.cs_next_var+3)) u
    (LENGTH vs * type_memory_size stv) /\
  ptr_covers H tf ("%" ++ toString (sa.cs_next_var+4)) u
    (LENGTH vs * type_memory_size dtv)` by
   (conj_tac >> irule ptr_covers_mono >> goal_assum (drule_at Any) >> simp[]) >>
 `w2n a + 32 + LENGTH vs * type_memory_size stv < dimword (:256) /\
  w2n b + 32 + LENGTH vs * type_memory_size dtv < dimword (:256) /\
  (w2n a + 32 + LENGTH vs * type_memory_size stv <= w2n b + 32 \/
   w2n b + 32 + LENGTH vs * type_memory_size dtv <= w2n a + 32) /\
  LENGTH vs < dimword (:256)` by decide_tac >>
 `a + 32w = n2w (w2n a + 32) /\ b + 32w = n2w (w2n b + 32)` by
   simp[GSYM wordsTheory.word_add_n2w] >>
 `0 < type_memory_size stv /\ 0 < type_memory_size dtv` by
   metis_tac[annassign_evaluated_array_stride_positive] >>
 `?K tk z. gas_path_ptr D 0 ctx fn PG H tf u 0 K tk (OK z) /\
   z.vs_current_bb = sb.cs_current_bb /\
   z.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~z.vs_halted /\
   typed_copy_state_frame sa (w2n b+32) (LENGTH vs * type_memory_size dtv) u z /\
   (!i. i < LENGTH vs ==> !m. mem_agree_outside tk.t_mem z.vs_memory m ==>
     val_in_memory dtv (EL i vs) (w2n b+32+i*type_memory_size dtv) m) /\
   (!j. ~(w2n b+32 <= j /\ j < w2n b+32+LENGTH vs*type_memory_size dtv) ==>
     mem_bytes_at j 1 z.vs_memory = mem_bytes_at j 1 u.vs_memory /\
     (j IN tk.t_mem <=> j IN tf.t_mem)) /\
   tk.t_stor = tf.t_stor /\ tk.t_trans = tf.t_trans /\ tk.t_imm = tf.t_imm /\
   (!x. not_fresh_at sa x ==>
     lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
     op_taint tk (Var x) = op_taint tf (Var x))` by
   (Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st`
    >- (gvs[] >>
        `stv = dtv` by
          (qpat_assum `evaluate_type _ _ = SOME (ArrayTV stv _)`
             (strip_assume_tac o MATCH_MP vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv) >>
           qpat_assum `evaluate_type _ _ = SOME (ArrayTV dtv _)`
             (strip_assume_tac o MATCH_MP vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv) >>
           gvs[]) >>
        gvs[] >>
        mp_tac (Q.INST [`f` |-> `\i:num. EL i (vs:value list)`, `s` |-> `u`,
          `G` |-> `H`, `tn` |-> `tf`, `n` |-> `LENGTH (vs:value list)`,
          `ty` |-> `dt`, `tv` |-> `dtv`, `cap` |-> `C`,
          `a` |-> `n2w (w2n a+32):256 word`, `b` |-> `n2w (w2n b+32):256 word`,
          `len` |-> `"%" ++ toString sa.cs_next_var`,
          `sr` |-> `"%" ++ toString (sa.cs_next_var+3)`,
          `dr` |-> `"%" ++ toString (sa.cs_next_var+4)`,
          `tmp` |-> `"%" ++ toString (sa.cs_next_var+5)`]
          (SPEC_ALL annassign_dynamic_compiler_bulk_payload)) >>
        impl_tac >- (simp[wordsTheory.w2n_n2w] >> metis_tac[]) >>
        strip_tac >> qexistsl_tac [`H'`,`tf'`,`t`] >> gvs[] >> metis_tac[]) >>
    drule_at (Pos (el 2)) annassign_dynamic_slow_payload_counted >>
    disch_then (drule_at (Pos (el 2))) >>
    disch_then (drule_at (Pos (el 13))) >>
    disch_then (fn th => asm "child" (mp_then (Pos (el 22)) mp_tac th)) >>
    disch_then (drule_at (Pos (el 20))) >>
    disch_then (qspecl_then [`w2n a + 32`,`w2n b + 32`,
      `\i:num. EL i (vs:value list)`] mp_tac) >>
    impl_tac >- (gvs[] >> metis_tac[]) >>
    strip_tac >> qexistsl_tac [`H'`,`tm`,`t`] >>
    gvs[typed_copy_index_prefix_def] >> metis_tac[]) >>
 `typed_copy_state_frame sa (w2n b) (32+C*type_memory_size dtv) s u` by
   (irule typed_copy_state_frame_subinterval >>
    goal_assum (drule_at Any) >> simp[]) >>
 `typed_copy_state_frame sa (w2n b) (32+C*type_memory_size dtv) u z` by
   (irule typed_copy_state_frame_subinterval >>
    goal_assum (drule_at Any) >> simp[]) >>
 `typed_copy_state_frame sa (w2n b) (32+C*type_memory_size dtv) s z` by
   metis_tac[typed_copy_state_frame_trans] >>
 `!m. mem_agree_outside tk.t_mem z.vs_memory m ==>
   val_in_memory (BaseTV (UintT 256)) (FlagV (LENGTH vs)) (w2n b) m` by
   (rpt strip_tac >> irule robust_representation_exterior_frame >>
    conj_tac >- simp[val_wf_def,type_memory_size_def] >>
    qexistsl_tac [`w2n b+32`,`u.vs_memory`,`z.vs_memory`,
      `LENGTH vs*type_memory_size dtv`,`tf.t_mem`,`tk.t_mem`] >>
    simp[val_wf_def,type_memory_size_def,val_in_memory_def,val_to_w256_def] >>
    metis_tac[]) >>
 `!x. not_fresh_at sa x ==>
   lookup_var x u = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
   op_taint tf (Var x) = op_taint tn (Var x)` by
   (gen_tac >> disch_tac >>
    qpat_x_assum `!x. x <> _ /\ _ ==> _` irule >>
    fs[not_fresh_at_def]) >>
 `!i. ~(w2n b <= i /\ i < w2n b+(32+C*type_memory_size dtv)) ==>
   mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 s.vs_memory /\
   (i IN tk.t_mem <=> i IN tn.t_mem)` by
   (rpt strip_tac >>
    `~(w2n b <= i /\ i < w2n b+32) /\
     ~(w2n b+32 <= i /\ i < w2n b+32+LENGTH vs*type_memory_size dtv)` by decide_tac >>
    metis_tac[]) >>
 qexistsl_tac [`K'`,`tk`,`z`] >>
 conj_tac >- metis_tac[gas_path_ptr_then,ADD_CLAUSES] >>
 gvs[ADD_COMM,typed_copy_dynarray_representation,val_in_memory_def,val_to_w256_def] >>
 gvs[] >>
 qpat_x_assum `gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK u)` mp_tac >>
 qpat_x_assum `gas_path_ptr D 0 ctx fn PG H tf u 0 K' tk (OK z)` mp_tac >>
 rpt (pop_assum kall_tac) >>
 metis_tac[gas_path_ptr_then,ADD_CLAUSES]
QED
