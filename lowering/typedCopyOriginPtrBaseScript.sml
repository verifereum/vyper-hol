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
  emitHelperProps fragExec venomExecSemantics venomInst venomState fragGasEmitCtrl
  finite_map list words contextCodegenRel codegenRel unitTransformDefs instMemFrontier

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

Theorem typed_copy_origin_ptr_assign_path:
  emit_inst ASSIGN [op] [out] a = ((),b) /\
  eval_operand op s = SOME w /\ op_prov G op = NONE /\ op_taint tn op = {} /\
  fn_has_code a b func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = DRESTRICT G (COMPL {out}) /\
    tnf = (tn with t_var := tn.t_var |+ (out,{})) /\
    lookup_var out t = SOME w /\ t.vs_memory = s.vs_memory /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst a.cs_next_id ASSIGN [op] [out])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst a.cs_next_id ASSIGN [op] [out]) s =
    OK (update_var out w s)` by
    simp[step_inst_base_def, mk_inst_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst a.cs_next_id ASSIGN [op] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `inst_mem_below_frontier (mk_inst a.cs_next_id ASSIGN [op] [out]) s /\
   inst_dload_in_section (mk_inst a.cs_next_id ASSIGN [op] [out]) s` by
    simp[inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
         mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G (mk_inst a.cs_next_id ASSIGN [op] [out]) (update_var out w s),
      step_taint (mk_inst a.cs_next_id ASSIGN [op] [out]) s (update_var out w s) tn)` by
    (mp_tac (Q.INST [`i` |-> `mk_inst a.cs_next_id ASSIGN [op] [out]`,
       `u` |-> `update_var out w s`] straight_line_origin_ptr_edge) >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[mk_inst_def]) >>
  `step_prov PG G (mk_inst a.cs_next_id ASSIGN [op] [out])
      (update_var out w s) = DRESTRICT G (COMPL {out})` by
    simp[step_prov_def, out_prov_def, first_prov_def, set_prov_def, mk_inst_def] >>
  `step_taint (mk_inst a.cs_next_id ASSIGN [op] [out]) s
      (update_var out w s) tn = (tn with t_var := tn.t_var |+ (out,{}))` by
    (simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
          store_taint_def, imm_taint_def, adopt_reset_def, out_taint_def, range_bytes_def,
          set_var_taint_def, mk_inst_def, new_site_bytes_def, update_var_def,
          source_memory_write_ranges_def, taint_component_equality,
          FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss]) >>
  qexistsl_tac [`update_var out w s with vs_inst_idx := SUC s.vs_inst_idx`,
    `DRESTRICT G (COMPL {out})`, `tn with t_var := tn.t_var |+ (out,{})`] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` mp_tac >>
  simp[update_var_def] >> strip_tac >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[gas_origin_ptr_path_rules]
QED

Theorem typed_copy_origin_ptr_counter_init_path:
  emit_inst ASSIGN [Lit 0w] [counter] a = ((),b) /\
  emit_inst JMP [Label hdr] [] b = ((),c) /\
  fn_has_code a c func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ?t Gf tnf.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t = jump_to hdr (update_var counter 0w s) /\
    Gf = DRESTRICT G (COMPL {counter}) /\
    tnf = (tn with t_var := tn.t_var |+ (counter,{})) /\
    lookup_var counter t = SOME 0w /\ FLOOKUP Gf counter = NONE /\
    op_taint tnf (Var counter) = {} /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    (!p. p <> counter ==> lookup_var p t = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code a b func /\ fn_has_code b c func` by metis_tac[fn_has_code_split] >>
  `eval_operand (Lit 0w) s = SOME 0w /\ op_prov G (Lit 0w) = NONE /\
   op_taint tn (Lit 0w) = {}` by simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all typed_copy_origin_ptr_assign_path >> strip_tac >>
  first_x_assum (qspecl_then [`explicit`,`PG`,`D`] strip_assume_tac) >>
  `allocas_from lo t` by (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  drule_all emit_jmp_origin_ptr >>
  disch_then (qspecl_then [`tnf`,`explicit`,`PG`,`Gf`,`D`] mp_tac) >>
  strip_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to hdr t),Gf,tnf)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`t`,`Gf`,`tnf`,`[]`,`OK (jump_to hdr t)`,`Gf`,`tnf`] mp_tac) >>
     simp[]) >>
  qexistsl_tac [`jump_to hdr t`,`Gf`,`tnf`] >>
  simp[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, op_taint_def] >>
  `b.cs_current_bb = a.cs_current_bb` by metis_tac[emit_inst_extends] >> simp[]
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

(* Pure address arithmetic has no memory accesses or observable requests. *)
Theorem typed_copy_origin_ptr_binop_checks:
  (opc = MUL \/ opc = ADD) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc [left;right] [out]) s =
    OK (update_var out w s) ==>
  ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst id opc [left;right] [out]) s /\
  inst_mem_below_frontier (mk_inst id opc [left;right] [out]) s /\
  inst_dload_in_section (mk_inst id opc [left;right] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, venomInstTheory.mk_inst_def,
       codegenRelTheory.source_memory_write_ranges_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def] >>
  simp[GSYM venomInstTheory.mk_inst_def,
       venomExecSemanticsTheory.step_inst_non_invoke] >>
  rpt strip_tac >> gvs[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem typed_copy_origin_ptr_binop_path:
  emit_op opc [left;right] a = (op,b) /\ fn_has_code a b func /\
  (opc = MUL /\ w = x * y \/ opc = ADD /\ w = x + y) /\
  eval_operand left s = SOME x /\ eval_operand right s = SOME y /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?out t G' tn'.
    op = Var out /\ not_fresh_at b out /\
    t = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G' = step_prov PG G (mk_inst a.cs_next_id opc [left;right] [out])
      (update_var out w s) /\
    tn' = step_taint (mk_inst a.cs_next_id opc [left;right] [out]) s
      (update_var out w s) tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
    eval_operand op t = SOME w /\ t.vs_memory = s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\
    typed_copy_state_frame a off len s t /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts
Proof
  strip_tac >>
  `!out. step_inst_base (mk_inst a.cs_next_id opc [left;right] [out]) s =
    OK (update_var out w s)` by
    (gvs[] >>
     simp_tac std_ss [Once venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, venomInstTheory.instruction_accessors,
       venomInstTheory.instruction_accfupds, venomInstTheory.opcode_case_def] >>
     simp[venomExecSemanticsTheory.exec_pure2_def]) >>
  `opc = MUL \/ opc = ADD` by metis_tac[] >>
  `!out. ptr_inst_ok D lo 0 ctx func G tn
       (mk_inst a.cs_next_id opc [left;right] [out]) s /\
     inst_mem_below_frontier (mk_inst a.cs_next_id opc [left;right] [out]) s /\
     inst_dload_in_section (mk_inst a.cs_next_id opc [left;right] [out]) s` by
    (gen_tac >> irule typed_copy_origin_ptr_binop_checks >> simp[] >>
     metis_tac[]) >>
  `opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc` by
    (gvs[] >> simp[venomInstTheory.is_terminator_def]) >>
  `!out. op = Var out ==> not_fresh_at b out` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh] >>
  metis_tac[typed_copy_origin_ptr_emit_op_path]
QED

Theorem typed_copy_origin_ptr_index_addresses_exact:
  emit_op MUL [Var counter; Lit (n2w ss)] a = (so,b) /\
  emit_op MUL [Var counter; Lit (n2w ds)] b = (doff,c) /\
  emit_op ADD [Var xs;so] c = (sp,d) /\
  emit_op ADD [Var xd;doff] d = (dp,e) /\
  not_fresh_at a counter /\ not_fresh_at a xs /\ not_fresh_at a xd /\
  lookup_var counter s = SOME (n2w j) /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  op_taint tn (Var counter) = {} /\
  op_taint tn (Var xs) = {} /\ op_taint tn (Var xd) = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  fn_has_code a e func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  (!opc left right id out w q tau.
    (opc = MUL \/ opc = ADD) /\
    op_taint tau left = {} /\ op_taint tau right = {} ==>
    op_taint (step_taint (mk_inst id opc [left;right] [out]) q
      (update_var out w q) tau) (Var out) = {} /\
    (!p. p <> out ==>
      op_taint (step_taint (mk_inst id opc [left;right] [out]) q
        (update_var out w q) tau) (Var p) = op_taint tau (Var p))) ==>
  ?vso vdo vsp vdp q1 q2 q3 t G1 G2 G3 G4 tn1 tn2 tn3 tn4.
    so = Var vso /\ doff = Var vdo /\ sp = Var vsp /\ dp = Var vdp /\
    ALL_DISTINCT [vso;vdo;vsp;vdp] /\
    (!p. not_fresh_at a p ==> ~MEM p [vso;vdo;vsp;vdp]) /\
    vso = STRING #"%" (toString a.cs_next_var) /\
    vdo = STRING #"%" (toString b.cs_next_var) /\
    vsp = STRING #"%" (toString c.cs_next_var) /\
    vdp = STRING #"%" (toString d.cs_next_var) /\
    q1 = (update_var vso (n2w (j*ss)) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    q2 = (update_var vdo (n2w (j*ds)) q1 with vs_inst_idx := SUC q1.vs_inst_idx) /\
    q3 = (update_var vsp (sw+n2w (j*ss)) q2 with vs_inst_idx := SUC q2.vs_inst_idx) /\
    t = (update_var vdp (dw+n2w (j*ds)) q3 with vs_inst_idx := SUC q3.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst a.cs_next_id MUL [Var counter;Lit (n2w ss)] [vso])
      (update_var vso (n2w (j*ss)) s) /\
    G2 = step_prov PG G1 (mk_inst b.cs_next_id MUL [Var counter;Lit (n2w ds)] [vdo])
      (update_var vdo (n2w (j*ds)) q1) /\
    G3 = step_prov PG G2 (mk_inst c.cs_next_id ADD [Var xs;so] [vsp])
      (update_var vsp (sw+n2w (j*ss)) q2) /\
    G4 = step_prov PG G3 (mk_inst d.cs_next_id ADD [Var xd;doff] [vdp])
      (update_var vdp (dw+n2w (j*ds)) q3) /\
    tn1 = step_taint (mk_inst a.cs_next_id MUL [Var counter;Lit (n2w ss)] [vso]) s
      (update_var vso (n2w (j*ss)) s) tn /\
    tn2 = step_taint (mk_inst b.cs_next_id MUL [Var counter;Lit (n2w ds)] [vdo]) q1
      (update_var vdo (n2w (j*ds)) q1) tn1 /\
    tn3 = step_taint (mk_inst c.cs_next_id ADD [Var xs;so] [vsp]) q2
      (update_var vsp (sw+n2w (j*ss)) q2) tn2 /\
    tn4 = step_taint (mk_inst d.cs_next_id ADD [Var xd;doff] [vdp]) q3
      (update_var vdp (dw+n2w (j*ds)) q3) tn3 /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G4,tn4) /\
    eval_operand sp t = SOME (sw+n2w (j*ss)) /\
    eval_operand dp t = SOME (dw+n2w (j*ds)) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    typed_copy_state_frame a off len s t /\
    ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
    t.vs_inst_idx = LENGTH e.cs_current_insts
Proof
  strip_tac >>
  `ci_mono a b /\ ci_mono b c /\ ci_mono c d /\ ci_mono d e` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono] >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d /\ cs_extends d e` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `cs_extends b e /\ cs_extends c e` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code a b func /\ fn_has_code b c func /\
   fn_has_code c d func /\ fn_has_code d e func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  suspend "steps"
QED

Resume typed_copy_origin_ptr_index_addresses_exact[steps]:
  `?vso q1 G1 tn1.
    so = Var vso /\ not_fresh_at b vso /\
    q1 = (update_var vso (n2w (j*ss)) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    G1 = step_prov PG G (mk_inst a.cs_next_id MUL [Var counter;Lit (n2w ss)] [vso])
      (update_var vso (n2w (j*ss)) s) /\
    tn1 = step_taint (mk_inst a.cs_next_id MUL [Var counter;Lit (n2w ss)] [vso]) s
      (update_var vso (n2w (j*ss)) s) tn /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q1,G1,tn1) /\
    eval_operand so q1 = SOME (n2w (j*ss)) /\ q1.vs_memory = s.vs_memory /\
    q1.vs_alloca_next = s.vs_alloca_next /\ typed_copy_state_frame a off len s q1 /\
    ~q1.vs_halted /\ q1.vs_current_bb = b.cs_current_bb /\
    q1.vs_inst_idx = LENGTH b.cs_current_insts` by
    (irule typed_copy_origin_ptr_binop_path >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
          wordsTheory.word_mul_n2w] >> metis_tac[]) >>
  `vso = STRING #"%" (toString a.cs_next_var)` by
    metis_tac[emitHelperPropsTheory.emitted_insts_emit_op, venomStateTheory.operand_11] >>
  `counter <> vso /\ xs <> vso /\ xd <> vso` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL] >>
  `lookup_var counter q1 = SOME (n2w j) /\
   lookup_var xs q1 = SOME sw /\ lookup_var xd q1 = SOME dw /\ allocas_from lo q1` by
    (gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE, ptrDisciplineTheory.allocas_from_def] >>
     metis_tac[]) >>
  `op_taint tn1 (Var counter) = {} /\ op_taint tn1 (Var xs) = {} /\
   op_taint tn1 (Var xd) = {} /\ op_taint tn1 so = {}` by
    (qpat_x_assum `tn1 = _` (fn th => rewrite_tac[th]) >>
     `op_taint tn (Lit (n2w ss)) = {}` by simp[ptrDisciplineTheory.op_taint_def] >>
     metis_tac[]) >>
  suspend "second"
QED

Resume typed_copy_origin_ptr_index_addresses_exact[second]:
  `?vdo q2 G2 tn2.
    doff = Var vdo /\ not_fresh_at c vdo /\
    q2 = (update_var vdo (n2w (j*ds)) q1 with vs_inst_idx := SUC q1.vs_inst_idx) /\
    G2 = step_prov PG G1 (mk_inst b.cs_next_id MUL [Var counter;Lit (n2w ds)] [vdo])
      (update_var vdo (n2w (j*ds)) q1) /\
    tn2 = step_taint (mk_inst b.cs_next_id MUL [Var counter;Lit (n2w ds)] [vdo]) q1
      (update_var vdo (n2w (j*ds)) q1) tn1 /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q1,G1,tn1) [] (OK q2,G2,tn2) /\
    eval_operand doff q2 = SOME (n2w (j*ds)) /\ q2.vs_memory = q1.vs_memory /\
    q2.vs_alloca_next = q1.vs_alloca_next /\ typed_copy_state_frame b off len q1 q2 /\
    ~q2.vs_halted /\ q2.vs_current_bb = c.cs_current_bb /\
    q2.vs_inst_idx = LENGTH c.cs_current_insts` by
    (irule typed_copy_origin_ptr_binop_path >>
     simp[venomStateTheory.eval_operand_def, ptrDisciplineTheory.op_taint_def,
          wordsTheory.word_mul_n2w] >> metis_tac[]) >>
  `vdo = STRING #"%" (toString b.cs_next_var)` by
    metis_tac[emitHelperPropsTheory.emitted_insts_emit_op, venomStateTheory.operand_11] >>
  `not_fresh_at b counter /\ not_fresh_at b xs /\ not_fresh_at b xd` by
    (fs[exprLoweringPropsTheory.ci_mono_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `counter <> vdo /\ xs <> vdo /\ xd <> vdo /\ vso <> vdo` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL] >>
  `lookup_var xs q2 = SOME sw /\ lookup_var xd q2 = SOME dw /\
   eval_operand so q2 = SOME (n2w (j*ss)) /\ allocas_from lo q2` by
    (gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE,
         ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `op_taint tn2 (Var xs) = {} /\ op_taint tn2 (Var xd) = {} /\
   op_taint tn2 so = {} /\ op_taint tn2 doff = {}` by
    (qpat_x_assum `tn2 = _` (fn th => rewrite_tac[th]) >>
     `op_taint tn1 (Lit (n2w ds)) = {}` by simp[ptrDisciplineTheory.op_taint_def] >>
     metis_tac[]) >>
  suspend "third"
QED

Resume typed_copy_origin_ptr_index_addresses_exact[third]:
  `?vsp q3 G3 tn3.
    sp = Var vsp /\ not_fresh_at d vsp /\
    q3 = (update_var vsp (sw+n2w (j*ss)) q2 with vs_inst_idx := SUC q2.vs_inst_idx) /\
    G3 = step_prov PG G2 (mk_inst c.cs_next_id ADD [Var xs;so] [vsp])
      (update_var vsp (sw+n2w (j*ss)) q2) /\
    tn3 = step_taint (mk_inst c.cs_next_id ADD [Var xs;so] [vsp]) q2
      (update_var vsp (sw+n2w (j*ss)) q2) tn2 /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q2,G2,tn2) [] (OK q3,G3,tn3) /\
    eval_operand sp q3 = SOME (sw+n2w (j*ss)) /\ q3.vs_memory = q2.vs_memory /\
    q3.vs_alloca_next = q2.vs_alloca_next /\ typed_copy_state_frame c off len q2 q3 /\
    ~q3.vs_halted /\ q3.vs_current_bb = d.cs_current_bb /\
    q3.vs_inst_idx = LENGTH d.cs_current_insts` by
    (irule typed_copy_origin_ptr_binop_path >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `vsp = STRING #"%" (toString c.cs_next_var)` by
    metis_tac[emitHelperPropsTheory.emitted_insts_emit_op, venomStateTheory.operand_11] >>
  `not_fresh_at c xs /\ not_fresh_at c xd /\ not_fresh_at c vso` by
    (fs[exprLoweringPropsTheory.ci_mono_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `xs <> vsp /\ xd <> vsp /\ vso <> vsp /\ vdo <> vsp` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL] >>
  `lookup_var xd q3 = SOME dw /\ eval_operand doff q3 = SOME (n2w (j*ds)) /\
   allocas_from lo q3` by
    (gvs[venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
         venomStateTheory.eval_operand_def, finite_mapTheory.FLOOKUP_UPDATE,
         ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  `op_taint tn3 (Var xd) = {} /\ op_taint tn3 doff = {}` by
    (qpat_x_assum `tn3 = _` (fn th => rewrite_tac[th]) >> metis_tac[]) >>
  suspend "fourth"
QED

Resume typed_copy_origin_ptr_index_addresses_exact[fourth]:
  `?vdp t G4 tn4.
    dp = Var vdp /\ not_fresh_at e vdp /\
    t = (update_var vdp (dw+n2w (j*ds)) q3 with vs_inst_idx := SUC q3.vs_inst_idx) /\
    G4 = step_prov PG G3 (mk_inst d.cs_next_id ADD [Var xd;doff] [vdp])
      (update_var vdp (dw+n2w (j*ds)) q3) /\
    tn4 = step_taint (mk_inst d.cs_next_id ADD [Var xd;doff] [vdp]) q3
      (update_var vdp (dw+n2w (j*ds)) q3) tn3 /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (q3,G3,tn3) [] (OK t,G4,tn4) /\
    eval_operand dp t = SOME (dw+n2w (j*ds)) /\ t.vs_memory = q3.vs_memory /\
    t.vs_alloca_next = q3.vs_alloca_next /\ typed_copy_state_frame d off len q3 t /\
    ~t.vs_halted /\ t.vs_current_bb = e.cs_current_bb /\
    t.vs_inst_idx = LENGTH e.cs_current_insts` by
    (irule typed_copy_origin_ptr_binop_path >>
     simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `vdp = STRING #"%" (toString d.cs_next_var)` by
    metis_tac[emitHelperPropsTheory.emitted_insts_emit_op, venomStateTheory.operand_11] >>
  suspend "join"
QED

Resume typed_copy_origin_ptr_index_addresses_exact[join]:
  `!p. not_fresh_at a p ==>
    not_fresh_at b p /\ not_fresh_at c p /\ not_fresh_at d p` by
    (fs[exprLoweringPropsTheory.ci_mono_def, loweringStateRelDefsTheory.not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `not_fresh_at c vso` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `not_fresh_at d vso /\ not_fresh_at d vdo` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `vso <> vdp /\ vdo <> vdp /\ vsp <> vdp` by
    metis_tac[loweringStateRelDefsTheory.not_fresh_at_def, arithmeticTheory.LESS_EQ_REFL] >>
  `ALL_DISTINCT [vso;vdo;vsp;vdp]` by simp[] >>
  `!p. not_fresh_at a p ==> ~MEM p [vso;vdo;vsp;vdp]` by
    (simp[] >> metis_tac[loweringStateRelDefsTheory.not_fresh_at_def,
                        arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand sp t = SOME (sw+n2w (j*ss))` by
    (gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
         venomStateTheory.update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `ci_mono a c /\ ci_mono a d` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `typed_copy_state_frame a off len q1 q2 /\
   typed_copy_state_frame a off len q2 q3 /\
   typed_copy_state_frame a off len q3 t` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_mono] >>
  `typed_copy_state_frame a off len s q3` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans] >>
  `typed_copy_state_frame a off len s t` by
    metis_tac[typedMemoryCopyTheory.typed_copy_state_frame_trans] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q2,G2,tn2)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q1,G1,tn1)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`q1`,`G1`,`tn1`,`[]`,`OK q2`,`G2`,`tn2`] mp_tac) >>
     simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q3,G3,tn3)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q2,G2,tn2)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`q2`,`G2`,`tn2`,`[]`,`OK q3`,`G3`,`tn3`] mp_tac) >>
     simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G4,tn4)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q3,G3,tn3)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`q3`,`G3`,`tn3`,`[]`,`OK t`,`G4`,`tn4`] mp_tac) >>
     simp[]) >>
  qexistsl_tac [`vso`,`vdo`,`vsp`,`vdp`,`q1`,`q2`,`q3`,`t`,
               `G1`,`G2`,`G3`,`G4`,`tn1`,`tn2`,`tn3`,`tn4`] >>
  simp[]
QED

Finalise typed_copy_origin_ptr_index_addresses_exact

Theorem typed_copy_origin_ptr_binop_ghost_frame:
  (opc = MUL \/ opc = ADD) ==>
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn) (Var out) = {} /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_imm = tn.t_imm /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn) (Var p) = op_taint tn (Var p)) /\
  (opc = MUL ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s)) out = NONE)
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[ptrDisciplineTheory.new_site_bytes_def, venomStateTheory.update_var_def,
         finite_mapTheory.FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >> Cases_on `eval_operand left s` >>
  Cases_on `first_prov G [left;right]` >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.step_taint_def,
       venomInstTheory.mk_inst_def, ptrDisciplineTheory.set_var_taint_def,
       ptrDisciplineTheory.out_taint_def, ptrDisciplineTheory.op_taint_def,
       ptrDisciplineTheory.store_taint_def, ptrDisciplineTheory.adopt_reset_def,
       ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrDisciplineTheory.written_taint_def, ptrDisciplineTheory.range_bytes_def,
       ptrDisciplineTheory.imm_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem typed_copy_origin_ptr_offset_covers:
  !PG G tn s root offset out id a off total n.
  lookup_var root s = SOME a /\
  eval_operand offset s = SOME (n2w off) /\
  ptr_covers G tn root s total /\ off + n <= total /\
  w2n a + off < dimword(:256) /\ root <> out ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root;offset] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root;offset] [out]) s
      (update_var out (a + n2w off) s) tn)
    out (update_var out (a + n2w off) s) n
Proof
  rpt gen_tac >> strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root;offset] [out]) s
    (update_var out (a + n2w off) s) tn) (Var out) = {}` by
    simp[typed_copy_origin_ptr_binop_ghost_frame] >>
  gvs[bodyPtrDefsTheory.ptr_covers_def] >>
  `off < dimword(:256)` by decide_tac >>
  simp[ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.set_prov_def,
       ptrDisciplineTheory.out_prov_def, ptrDisciplineTheory.first_prov_def,
       ptrDisciplineTheory.op_prov_def, venomInstTheory.mk_inst_def,
       finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.lookup_var_def,
       venomStateTheory.update_var_def, wordsTheory.w2n_add_2,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

(* The header's two scalar instructions and its conditional transfer. *)
Theorem typed_copy_origin_ptr_header_branch_path:
  emit_op LT [Var counter; length] a = (lt,b) /\
  emit_op ISZERO [lt] b = (done,c) /\
  emit_inst JNZ [done; Label exit; Label blabel] [] c = ((),d) /\
  lookup_var counter s = SOME (n2w k) /\
  eval_operand length s = SOME (n2w N) /\ k <= N /\ N < dimword(:256) /\
  FLOOKUP G counter = NONE /\ op_prov G length = NONE /\
  op_taint tn (Var counter) = {} /\ op_taint tn length = {} /\
  fn_has_code a d func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?x y t Gf tnf.
    lt = Var x /\ done = Var y /\
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t = jump_to (if k = N then exit else blabel)
      (update_var y (if k = N then 1w else 0w)
        (update_var x (if k < N then 1w else 0w) s)) /\
    Gf = DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y}) /\
    tnf = (tn with t_var := (tn.t_var |+ (x,{})) |+ (y,{})) /\
    t.vs_memory = s.vs_memory /\ t.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    ~t.vs_halted /\ t.vs_inst_idx = 0 /\
    t.vs_current_bb = (if k = N then exit else blabel) /\
    (!p. p <> x /\ p <> y ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
      exprLoweringPropsTheory.ci_mono_def, cs_extends_emit_inst] >>
  `fn_has_code a b func /\ fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  `!out. step_inst_base (mk_inst a.cs_next_id LT [Var counter;length] [out]) s =
    OK (update_var out (if k < N then 1w else 0w) s)` by
    (simp[step_inst_base_def, mk_inst_def, exec_pure2_def, eval_operand_def,
          wordsTheory.WORD_LO, wordsTheory.w2n_n2w] >>
     `k < dimword(:256)` by decide_tac >>
     Cases_on `k < N` >> simp[arithmeticTheory.LESS_MOD, bool_to_word_def]) >>
  `!out. ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst a.cs_next_id LT [Var counter;length] [out]) s` by
    (simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     conj_tac >- (Cases_on `length` >> gvs[op_prov_def, finite_mapTheory.FLOOKUP_DEF]) >>
     simp[update_var_def] >> metis_tac[]) >>
  `!out. inst_mem_below_frontier (mk_inst a.cs_next_id LT [Var counter;length] [out]) s /\
    inst_dload_in_section (mk_inst a.cs_next_id LT [Var counter;length] [out]) s` by
    simp[inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
         mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `LT <> INVOKE /\ LT <> GAS /\ ~is_terminator LT` by simp[is_terminator_def] >>
  drule_all typed_copy_origin_ptr_emit_op_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`] strip_assume_tac) >>
  rename1 `lt = Var x` >>
  rename1 `gas_origin_ptr_path _ (s,G,tn) [] (OK q,G1,tn1)` >>
  `G1 = DRESTRICT G (COMPL {x}) /\
   tn1 = (tn with t_var := tn.t_var |+ (x,{}))` by
    (simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
     simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, out_taint_def,
       range_bytes_def, set_var_taint_def, new_site_bytes_def, update_var_def,
       source_memory_write_ranges_def, taint_component_equality,
       FLOOKUP_DEF, pred_setTheory.EXTENSION, eval_operand_def, SF CONJ_ss]) >>
  `op_taint tn1 lt = {}` by simp[op_taint_def, FLOOKUP_UPDATE] >>
  `allocas_from lo q` by (gvs[allocas_from_def, update_var_def] >> metis_tac[]) >>
  suspend "iszero"
QED

Resume typed_copy_origin_ptr_header_branch_path[iszero]:
  `!out. step_inst_base (mk_inst b.cs_next_id ISZERO [lt] [out]) q =
    OK (update_var out (if k = N then 1w else 0w) q)` by
    (simp[step_inst_base_def, mk_inst_def, exec_pure1_def] >>
     Cases_on `k < N` >>
     simp[bool_to_word_def, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `!out. ptr_inst_ok D lo 0 ctx func G1 tn1
      (mk_inst b.cs_next_id ISZERO [lt] [out]) q` by
    (gen_tac >>
     qpat_assum `!out. step_inst_base (mk_inst b.cs_next_id ISZERO _ _) q = _`
       (qspec_then `out` assume_tac) >>
     simp[NoAsms, ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     gvs[update_var_def, op_taint_def, FLOOKUP_UPDATE]) >>
  `!out. inst_mem_below_frontier (mk_inst b.cs_next_id ISZERO [lt] [out]) q /\
    inst_dload_in_section (mk_inst b.cs_next_id ISZERO [lt] [out]) q` by
    simp[inst_mem_below_frontier_def, memSafeRunTheory.inst_dload_in_section_def,
         mk_inst_def, source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  `ISZERO <> INVOKE /\ ISZERO <> GAS /\ ~is_terminator ISZERO` by simp[is_terminator_def] >>
  qpat_x_assum `emit_op LT _ _ = _` kall_tac >>
  drule_all typed_copy_origin_ptr_emit_op_path >>
  disch_then (qspecl_then [`0`,`0`,`explicit`,`PG`] strip_assume_tac) >>
  suspend "branch"
QED

Resume typed_copy_origin_ptr_header_branch_path[branch]:
  rename1 `done = Var y` >>
  rename1 `gas_origin_ptr_path _ (q,G1,tn1) [] (OK r,G2,tn2)` >>
  `G2 = DRESTRICT G1 (COMPL {y}) /\
   tn2 = (tn1 with t_var := tn1.t_var |+ (y,{}))` by
    (simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
     simp[step_taint_def, mem_taint_def, step_writes_def, written_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, out_taint_def,
       range_bytes_def, set_var_taint_def, new_site_bytes_def, update_var_def,
       source_memory_write_ranges_def, taint_component_equality,
       FLOOKUP_DEF, pred_setTheory.EXTENSION, eval_operand_def, lookup_var_def,
       FLOOKUP_UPDATE, SF CONJ_ss]) >>
  `op_taint tn2 done = {}` by simp[op_taint_def, FLOOKUP_UPDATE] >>
  `allocas_from lo r` by
    (simp[allocas_from_def, update_var_def] >> rpt strip_tac >>
     qpat_x_assum `allocas_from lo s` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then drule >> simp[]) >>
  drule_all emit_jnz_origin_ptr >>
  disch_then (qspecl_then [`explicit`,`PG`,`G2`,`D`] assume_tac) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK r,G2,tn2)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) _ _`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`q`,`G1`,`tn1`,`[]`,`OK r`,`G2`,`tn2`] mp_tac) >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (jump_to (if k = N then exit else blabel) r),G2,tn2)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK r,G2,tn2)`
       (mp_then Any mp_tac gas_origin_ptr_path_append) >>
     disch_then (qspecl_then [`r`,`G2`,`tn2`,`[]`,
       `OK (jump_to (if k = N then exit else blabel) r)`,`G2`,`tn2`] mp_tac) >> simp[]) >>
  qexistsl_tac [`x`,`y`,`jump_to (if k = N then exit else blabel) r`,`G2`,`tn2`] >>
  simp[jump_to_def, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, op_taint_def] >>
  gvs[update_var_def]
QED

Finalise typed_copy_origin_ptr_header_branch_path

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
