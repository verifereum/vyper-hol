(*
 * The joint (gas-origin and pointer-ghost) twin of the typed memory copy's
 * forward run: the motive of its rank induction, and the counted element
 * loop the static and dynamic array copies share.
 *
 * TOP-LEVEL:
 *   typed_copy_origin_ptr_entry -- the rank-induction motive (proof-internal)
 *   typed_copy_origin_ptr_entry_run -- using it
 *   typed_copy_origin_ptr_index_loop -- the counted element-copy loop
 *)
Theory typedCopyOriginPtrBase
Ancestors
  placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr bodyPtrDefs
  ptrSafeRun ptrDiscipline typedMemoryCopy robustCopyTransportPtr

(* Every joint copy of type sty into type dty of the value v (evaluated at
   stv and dtv) through compile_store_memory_typed, between two pointer
   variables, reaches its end along a zero-mark joint path with no dead
   bytes: the destination holds v whatever its tainted bytes hold, only the
   destination changes, taint changes only inside the destination, and the
   older variables keep their ghosts. *)
Definition typed_copy_origin_ptr_entry_def:
  typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v <=>
    !lo explicit func PG xd xs sa sb s G tn dw sw.
      compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
      not_fresh_at sa xs /\ not_fresh_at sa xd /\
      lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory stv v (w2n sw) mem) /\
      w2n sw + type_memory_size stv < dimword (:256) /\
      w2n dw + type_memory_size dtv < dimword (:256) /\
      (type_memory_size stv = 0 \/
       w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
      (type_memory_size dtv = 0 \/
       w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
      (w2n sw + type_memory_size stv <= w2n dw \/
       w2n dw + type_memory_size dtv <= w2n sw) /\
      ptr_covers G tn xs s (type_memory_size stv) /\
      ptr_covers G tn xd s (type_memory_size dtv) /\
      allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
      fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?t Gf tnf.
        gas_origin_ptr_path
          (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
              d_ret := K {} |>,lo,explicit,ctx,func,PG)
          (s,G,tn) [] (OK t,Gf,tnf) /\
        val_in_memory dtv v (w2n dw) t.vs_memory /\
        typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
        (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
             (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
        (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
               val_in_memory dtv v (w2n dw) mem) /\
        (!p. not_fresh_at sa p ==>
           FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
End

Theorem typed_copy_origin_ptr_entry_run:
  typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv v /\
  compile_store_memory_typed cenv (Var xd) dty (Var xs) sty sa = ((),sb) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory stv v (w2n sw) mem) /\
  w2n sw + type_memory_size stv < dimword (:256) /\
  w2n dw + type_memory_size dtv < dimword (:256) /\
  (type_memory_size stv = 0 \/
   w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  (type_memory_size dtv = 0 \/
   w2n dw + type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (type_memory_size stv) /\
  ptr_covers G tn xd s (type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    val_in_memory dtv v (w2n dw) t.vs_memory /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
           val_in_memory dtv v (w2n dw) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp_tac std_ss [typed_copy_origin_ptr_entry_def] >> strip_tac >>
  first_x_assum (qspecl_then [`lo`,`explicit`,`func`,`PG`,`xd`,`xs`,
    `sa`,`sb`,`s`,`G`,`tn`,`dw`,`sw`] mp_tac) >>
  asm_rewrite_tac[]
QED

(* Robust values survive a child write outside their representation. *)
Theorem typed_copy_origin_ptr_index_robust_step:
  k < N /\
  (so + N * type_memory_size stv <= dst \/
   dst + N * type_memory_size dtv <= so) /\
  (!i. i < N ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
  (!i mem. i < N /\ mem_agree_outside tnq q.vs_memory mem ==>
    val_in_memory stv (f i) (so + i * type_memory_size stv) mem) /\
  (!i mem. i < k /\ mem_agree_outside tnq q.vs_memory mem ==>
    val_in_memory dtv (f i) (dst + i * type_memory_size dtv) mem) /\
  typed_copy_state_frame sa (dst + k * type_memory_size dtv)
    (type_memory_size dtv) q r /\
  (!i. ~(dst + k * type_memory_size dtv <= i /\
          i < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
    (i IN tnr <=> i IN tnq)) /\
  (!mem. mem_agree_outside tnr r.vs_memory mem ==>
    val_in_memory dtv (f k) (dst + k * type_memory_size dtv) mem) ==>
  (!i mem. i < N /\ mem_agree_outside tnr r.vs_memory mem ==>
    val_in_memory stv (f i) (so + i * type_memory_size stv) mem) /\
  (!i mem. i < SUC k /\ mem_agree_outside tnr r.vs_memory mem ==>
    val_in_memory dtv (f i) (dst + i * type_memory_size dtv) mem)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!a. ~(dst + k * type_memory_size dtv <= a /\
          a < dst + k * type_memory_size dtv + type_memory_size dtv) ==>
       mem_bytes_at a 1 r.vs_memory = mem_bytes_at a 1 q.vs_memory` by
    (fs[typed_copy_state_frame_def, typed_copy_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (map_every qx_gen_tac [`i`, `mem`] >> strip_tac >>
      `val_wf stv (f i)` by metis_tac[] >>
      `so <= so + i * type_memory_size stv /\
       so + i * type_memory_size stv + type_memory_size stv <=
       so + N * type_memory_size stv` by
        metis_tac[typed_copy_array_subinterval] >>
      `dst <= dst + k * type_memory_size dtv /\
       dst + k * type_memory_size dtv + type_memory_size dtv <=
       dst + N * type_memory_size dtv` by
        metis_tac[typed_copy_array_subinterval] >>
      drule exprSimPropsTheory.val_footprint_le >> disch_tac >>
      irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
      qexistsl_tac [`q.vs_memory`, `r.vs_memory`, `tnq`, `tnr`,
        `{a | dst + k * type_memory_size dtv <= a /\
               a < dst + k * type_memory_size dtv + type_memory_size dtv}`] >>
      simp[] >> rpt strip_tac >> decide_tac) >>
  map_every qx_gen_tac [`i`, `mem`] >> strip_tac >>
  Cases_on `i = k` >- metis_tac[] >>
  `i < k /\ i < N` by decide_tac >>
  `val_wf dtv (f i)` by metis_tac[] >>
  `dst + i * type_memory_size dtv + type_memory_size dtv <=
   dst + k * type_memory_size dtv` by
    metis_tac[typed_copy_array_subinterval] >>
  drule exprSimPropsTheory.val_footprint_le >> disch_tac >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`q.vs_memory`, `r.vs_memory`, `tnq`, `tnr`,
    `{a | dst + k * type_memory_size dtv <= a /\
           a < dst + k * type_memory_size dtv + type_memory_size dtv}`] >>
  simp[] >> rpt strip_tac >> decide_tac
QED

Theorem typed_copy_origin_ptr_index_prefix_frame_step:
  typed_copy_state_frame sa dst (k * stride) s q /\
  typed_copy_state_frame sa (dst + k * stride) stride q r /\
  (!i. ~(dst <= i /\ i < dst + k * stride) ==>
    (i IN tnq <=> i IN tn)) /\
  (!i. ~(dst + k * stride <= i /\ i < dst + k * stride + stride) ==>
    (i IN tnr <=> i IN tnq)) ==>
  typed_copy_state_frame sa dst (SUC k * stride) s r /\
  (!i. ~(dst <= i /\ i < dst + SUC k * stride) ==>
    (i IN tnr <=> i IN tn))
Proof
  strip_tac >> conj_tac
  >- (irule typed_copy_state_frame_trans >> qexists_tac `q` >>
      conj_tac
      >- (irule typed_copy_state_frame_subinterval >>
          qexistsl_tac [`dst`, `k * stride`] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
      irule typed_copy_state_frame_subinterval >>
      qexistsl_tac [`dst + k * stride`, `stride`] >> simp[arithmeticTheory.MULT_CLAUSES]) >>
  rpt strip_tac >>
  `~(dst <= i /\ i < dst + k * stride) /\
   ~(dst + k * stride <= i /\ i < dst + k * stride + stride)` by
    (fs[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  metis_tac[]
QED

Theorem typed_copy_origin_ptr_emit_op_path:
  emit_op opc args a = (op,b) /\ fn_has_code a b func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!out. step_inst_base (mk_inst a.cs_next_id opc args [out]) s =
    OK (update_var out w s)) /\
  (!out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst a.cs_next_id opc args [out]) s) /\
  (!out. inst_mem_below_frontier (mk_inst a.cs_next_id opc args [out]) s /\
    inst_dload_in_section (mk_inst a.cs_next_id opc args [out]) s) ==>
  ?out t G' tn'.
    op = Var out /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst a.cs_next_id opc args [out])
      (update_var out w s) /\
    tn' = step_taint (mk_inst a.cs_next_id opc args [out]) s
      (update_var out w s) tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\
    typed_copy_state_frame a off len s t /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `b.cs_current_bb = a.cs_current_bb` by
    gvs[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
        compileEnvTheory.fresh_var_def, compileEnvTheory.fresh_id_def,
        compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.comp_return_def,
        compileEnvTheory.emit_def] >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH a.cs_current_insts) =
    SOME (mk_inst a.cs_next_id opc args
      [STRING #"%" (toString a.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qexists_tac `STRING #"%" (toString a.cs_next_var)` >>
  simp[IgnAsm `s.vs_inst_idx = _`] >>
  rpt (irule_at Any EQ_REFL) >>
  conj_tac >-
    (qmatch_goalsub_abbrev_tac `step_prov PG G inst u` >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
        step_prov PG G inst u, step_taint inst s u tn)` by
       (mp_tac (straight_line_origin_ptr_edge |> Q.INST [`i` |-> `inst`, `u` |-> `u`]) >>
        simp[Abbr `inst`, Abbr `u`, venomInstTheory.mk_inst_def] >>
        disch_then irule >> simp[]) >>
     `~(u with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
       simp[Abbr `u`, venomStateTheory.update_var_def] >>
     drule (cj 1 gas_origin_ptr_path_rules) >> strip_tac >>
     drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspecl_then [`[]`,
       `OK (u with vs_inst_idx := SUC s.vs_inst_idx)`,
       `step_prov PG G inst u`, `step_taint inst s u tn`] mp_tac) >> simp[]) >>
  simp[venomStateTheory.eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       venomStateTheory.update_var_def, typed_copy_state_frame_def,
       venomStateTheory.lookup_var_def, venomStateTheory.venom_state_component_equality,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString a.cs_next_var)` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Finite iteration is independent of the concrete header invariant. *)
Theorem typed_copy_origin_ptr_counted_path:
  (!j q G tn. j < N /\ H j q G tn ==>
     ?r Gr tnr. gas_origin_ptr_path cfg (q,G,tn) [] (OK r,Gr,tnr) /\
                H (SUC j) r Gr tnr) /\
  (!q G tn. H N q G tn ==>
     ?t Gf tnf. gas_origin_ptr_path cfg (q,G,tn) [] (OK t,Gf,tnf) /\
                R t Gf tnf) ==>
  !k q G tn. k <= N /\ H k q G tn ==>
    ?t Gf tnf. gas_origin_ptr_path cfg (q,G,tn) [] (OK t,Gf,tnf) /\
               R t Gf tnf
Proof
  strip_tac >> measureInduct_on `N-k` >> rpt strip_tac >>
  Cases_on `k = N`
  >- metis_tac[] >>
  `k < N` by decide_tac >>
  qpat_assum `!j q G tn. j < N /\ _ ==> _`
    (qspecl_then [`k`,`q`,`G`,`tn`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!k'. _ ==> _`
    (qspec_then `SUC k` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`r`,`Gr`,`tnr`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexistsl_tac [`t`,`Gf`,`tnf`] >> simp[] >>
  qpat_x_assum `gas_origin_ptr_path cfg (q,G,tn) [] _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  simp[] >> metis_tac[]
QED

(* The counted loop that copies N elements from xs to xd, element i at
   offset i times the element size on each side (the joint twin of
   placeTypedCopyRecursivePath's typed_copy_forward_index_loop_path). *)
Theorem typed_copy_origin_ptr_index_loop:
  emit_inst ASSIGN [Lit 0w] [counter] init = ((),st0) /\
  emit_inst JMP [Label hdr] [] st0 = ((),st1) /\
  new_block hdr st1 = (u1,sth) /\
  emit_op LT [Var counter; length] sth = (lt,h1) /\
  emit_op ISZERO [lt] h1 = (done,stj) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] stj = ((),st2) /\
  new_block blabel st2 = (u2,stb) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1) /\
  emit_op MUL [Var counter; Lit (n2w (type_memory_size dtv))] b1 = (doff,b2) /\
  emit_op ADD [Var xs;so] b2 = (sp,b3) /\
  emit_op ADD [Var xd;doff] b3 = (dp,b4) /\
  compile_store_memory_typed cenv dp dty sp sty b4 = ((),b5) /\
  emit_op ADD [Var counter; Lit 1w] b5 = (inc,b6) /\
  emit_inst ASSIGN [inc] [counter] b6 = ((),ste) /\
  emit_inst JMP [Label hdr] [] ste = ((),st3) /\
  new_block exit st3 = (u3,stx) /\
  ci_mono sa init /\ ci_mono sa st0 /\ ci_mono sa sth /\ ci_mono sa stb /\
  ci_mono init st0 /\ ci_mono st0 stx /\
  cs_extends sth stj /\ cs_extends stb ste /\
  ~not_fresh_at sa counter /\ not_fresh_at sth counter /\
  not_fresh_at stb counter /\
  sa.cs_current_bb = init.cs_current_bb /\
  sa.cs_current_insts = init.cs_current_insts /\ sa.cs_blocks = init.cs_blocks /\
  (!x. length = Var x ==>
       not_fresh_at sa x /\ FLOOKUP G x = NONE /\ op_taint tn (Var x) = {}) /\
  eval_operand length s = SOME (n2w N) /\ N < dimword (:256) /\
  (!i. i < N ==> typed_copy_origin_ptr_entry cenv ctx dty sty dtv stv (f i) /\
                   val_wf stv (f i) /\ val_wf dtv (f i)) /\
  not_fresh_at sa xs /\ not_fresh_at sa xd /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  (!i mem. i < N /\ mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory stv (f i) (w2n sw + i * type_memory_size stv) mem) /\
  w2n sw + N * type_memory_size stv < dimword (:256) /\
  w2n dw + N * type_memory_size dtv < dimword (:256) /\
  (N * type_memory_size stv = 0 \/
   w2n sw + N * type_memory_size stv <= s.vs_alloca_next) /\
  (N * type_memory_size dtv = 0 \/
   w2n dw + N * type_memory_size dtv <= s.vs_alloca_next) /\
  (w2n sw + N * type_memory_size stv <= w2n dw \/
   w2n dw + N * type_memory_size dtv <= w2n sw) /\
  ptr_covers G tn xs s (N * type_memory_size stv) /\
  ptr_covers G tn xd s (N * type_memory_size dtv) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code sa stx func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    (!i. i < N ==> val_in_memory dtv (f i)
       (w2n dw + i * type_memory_size dtv) t.vs_memory) /\
    typed_copy_state_frame sa (w2n dw) (N * type_memory_size dtv) s t /\
    ~t.vs_halted /\ t.vs_current_bb = stx.cs_current_bb /\
    t.vs_inst_idx = LENGTH stx.cs_current_insts /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. ~(w2n dw <= i /\ i < w2n dw + N * type_memory_size dtv) ==>
         (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!i mem. i < N /\ mem_agree_outside tnf.t_mem t.vs_memory mem ==>
       val_in_memory dtv (f i) (w2n dw + i * type_memory_size dtv) mem) /\
    (!p. not_fresh_at sa p ==>
       FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  cheat
QED
