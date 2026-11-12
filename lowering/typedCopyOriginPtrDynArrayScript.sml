(* The joint typed memory copy of a dynamic array: length, check, data. *)
Theory typedCopyOriginPtrDynArray
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy
  compileEnv emitHelper loweringStateRelDefs

(* A single checked emitted instruction, with its concrete ghosts. *)
Theorem typed_copy_emit_inst_origin_ptr_path:
  emit_inst opc args outs sa = ((),sb) /\ fn_has_code sa sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  inst_mem_below_frontier (mk_inst sa.cs_next_id opc args outs) s /\
  inst_dload_in_section (mk_inst sa.cs_next_id opc args outs) s /\
  ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc args outs) s /\
  step_inst_base (mk_inst sa.cs_next_id opc args outs) s = OK u ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc args outs) u,
     step_taint (mk_inst sa.cs_next_id opc args outs) s u tn)
Proof
  strip_tac >> drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  drule_all fragExecTheory.fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc args outs)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc args outs) u,
     step_taint (mk_inst sa.cs_next_id opc args outs) s u tn)` by
    (mp_tac (straight_line_origin_ptr_edge |> Q.INST
       [`i` |-> `mk_inst sa.cs_next_id opc args outs`]) >>
     simp[venomInstTheory.mk_inst_def] >> disch_then irule >> simp[]) >>
  `~u.vs_halted` by
    ( `step_inst 0 ctx (mk_inst sa.cs_next_id opc args outs) s = OK u` by
        simp[venomExecSemanticsTheory.step_inst_non_invoke, venomInstTheory.mk_inst_def] >>
      drule venomInstProofsTheory.step_preserves_halted >>
      simp[venomInstTheory.mk_inst_def]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  simp[] >> disch_then irule >>
  irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

(* Package the emitted dynamic-array payload loop; the shared loop theorem
   owns the recursive execution and ghost invariant. *)
Theorem typed_copy_origin_ptr_dynarray_slow_data_path:
  fresh_label "typed_dyn_cond" sa = (hdr,l1) /\
  fresh_label "typed_dyn_body" l1 = (blabel,l2) /\
  fresh_label "typed_dyn_exit" l2 = (exit,l3) /\
  fresh_var l3 = (counter,init) /\
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
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all typed_copy_dynarray_slow_layout >> strip_tac >>
  irule typed_copy_origin_ptr_index_loop >> simp[] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (irule_at (Pat `emit_inst ASSIGN [Lit 0w] _ _ = _`)) >>
  qpat_assum `emit_op LT _ _ = _` (irule_at (Pat `emit_op LT _ _ = _`)) >>
  qpat_assum `emit_op ISZERO _ _ = _` (irule_at (Pat `emit_op ISZERO _ _ = _`)) >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (irule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  qpat_assum `compile_store_memory_typed _ _ _ _ _ _ = _`
    (irule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  qpat_assum `emit_op ADD [Var xs;so] b2 = (sp,b3)`
    (irule_at (Pat `emit_op ADD [Var _;_] _ = _`)) >>
  qpat_assum `emit_op MUL [Var counter; Lit (n2w (type_memory_size stv))] stb = (so,b1)`
    (irule_at (Pat `emit_op MUL _ stb = _`)) >>
  rpt (goal_assum (drule_at Any)) >> gvs[]
QED

Theorem typed_copy_origin_ptr_offset_path:
  !k N.
  emit_op ADD [Var x; Lit (n2w k)] a = (Var r,b) /\
  not_fresh_at a x /\ lookup_var x s = SOME w /\ ptr_covers G tn x s N /\
  k <= N /\ w2n w + N < dimword (:256) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
    t = ((update_var r (w+n2w k) s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    ptr_covers Gf tnf r t (N-k) /\ eval_operand (Var r) t = SOME (w+n2w k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> r ==> FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `u = update_var r (w+n2w k) s` >>
  qabbrev_tac `i = mk_inst a.cs_next_id ADD [Var x; Lit (n2w k)] [r]` >>
  qabbrev_tac `a0 = a with cs_next_var := a.cs_next_var+1` >>
  `emit_inst ADD [Var x; Lit (n2w k)] [r] a0 = ((),b)` by
    (gvs[Abbr `a0`, emit_op_def, emit_inst_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def]) >>
  suspend "offset"
QED

Resume typed_copy_origin_ptr_offset_path[offset]:
  `fn_has_code a0 b func` by
    gvs[Abbr `a0`, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (u with vs_inst_idx := SUC s.vs_inst_idx),step_prov PG G i u,step_taint i s u tn)` by
    (mp_tac (typed_copy_emit_inst_origin_ptr_path |> Q.INST
       [`sa` |-> `a0`, `sb` |-> `b`, `opc` |-> `ADD`,
        `args` |-> `[Var x; Lit (n2w k)]`, `outs` |-> `[r]`,
        `D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
                     d_imm := K {}; d_ret := K {} |>`]) >>
     simp[Abbr `i`, Abbr `a0`] >> disch_then irule >>
     simp[venomInstTheory.is_terminator_def] >> rpt conj_tac
     >~ [`inst_mem_below_frontier _ _`] >-
       simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
            contextCodegenRelTheory.source_memory_read_ranges_def,
            codegenRelTheory.source_memory_write_ranges_def, venomInstTheory.mk_inst_def]
     >~ [`ptr_inst_ok _ _ _ _ _ _ _ _ _`] >- suspend "offset_ptr" >>
     simp[Abbr `u`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
          venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def,
          venomExecSemanticsTheory.exec_pure2_def]) >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
               `step_prov PG G i u`, `step_taint i s u tn`] >>
  simp[] >> suspend "offset_post"
QED

Resume typed_copy_origin_ptr_offset_path[offset_ptr]:
  gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       venomInstTheory.mk_inst_def, op_taint_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def] >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_pure2_def,
       venomStateTheory.eval_operand_def, venomStateTheory.update_var_def] >>
  gen_tac >> Cases_on `op = Var x` >- gvs[op_taint_def] >>
  Cases_on `op = Lit (n2w k)` >> gvs[]
QED

Resume typed_copy_origin_ptr_offset_path[offset_post]:
  `b.cs_current_bb = a.cs_current_bb /\
   LENGTH b.cs_current_insts = SUC (LENGTH a.cs_current_insts)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         fresh_var_def, fresh_id_def, emit_def]) >>
  gvs[ptr_covers_def] >>
  `w2n (w+n2w k : bytes32) = w2n w+k` by
    (`k < dimword (:256) /\ w2n w+k < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  simp[Abbr `i`, Abbr `u`, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
       step_prov_def, out_prov_def, first_prov_def, op_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, new_site_bytes_def, finite_mapTheory.FLOOKUP_DEF,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_DRESTRICT,
       imm_taint_def, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  rpt strip_tac >> simp[finite_mapTheory.FAPPLY_FUPDATE_THM]
QED

Finalise typed_copy_origin_ptr_offset_path

Theorem typed_copy_origin_ptr_dyn_data_path:
  !S T.
  emit_void MSTORE [Var xd; Var lv] a = ((),b) /\
  emit_op ADD [Var xs; Lit 32w] b = (Var sdv,c) /\
  emit_op ADD [Var xd; Lit 32w] c = (Var ddv,d) /\
  not_fresh_at a xs /\ not_fresh_at a xd /\ not_fresh_at a lv /\
  lookup_var xs s = SOME sw /\ lookup_var xd s = SOME dw /\
  eval_operand (Var lv) s = SOME w /\
  FLOOKUP G lv = NONE /\ op_taint tn (Var lv) = {} /\
  ptr_covers G tn xs s S /\ ptr_covers G tn xd s T /\
  32 <= S /\ 32 <= T /\
  w2n sw + S < dimword (:256) /\ w2n dw + T < dimword (:256) /\
  w2n sw + S <= s.vs_alloca_next /\ w2n dw + T <= s.vs_alloca_next /\
  (w2n sw + S <= w2n dw \/ w2n dw + T <= w2n sw) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  fn_has_code a d func /\ fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?t Gf tnf.
    gas_origin_ptr_path
      (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {};
          d_ret := K {} |>,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tnf) /\
    typed_copy_state_frame a (w2n dw) 32 s t /\
    ~t.vs_halted /\ t.vs_current_bb = d.cs_current_bb /\
    t.vs_inst_idx = LENGTH d.cs_current_insts /\
    t.vs_alloca_next = s.vs_alloca_next /\
    tnf.t_imm = tn.t_imm /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at a p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    ptr_covers Gf tnf xs t S /\ ptr_covers Gf tnf xd t T /\
    eval_operand (Var lv) t = SOME w /\
    FLOOKUP Gf lv = NONE /\ op_taint tnf (Var lv) = {} /\
    eval_operand (Var sdv) t = SOME (sw+32w) /\
    eval_operand (Var ddv) t = SOME (dw+32w) /\
    ptr_covers Gf tnf sdv t (S-32) /\ ptr_covers Gf tnf ddv t (T-32) /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+32) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
      mem_word_at (w2n dw) mem = w)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!p. not_fresh_at a p ==> p <> sdv /\ p <> ddv` by
    (gvs[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         not_fresh_at_def] >> metis_tac[]) >>
  `cs_extends a b /\ cs_extends b c /\ cs_extends c d` by
    (gvs[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         cs_extends_def] >> simp[]) >>
  `fn_has_code a b func /\ fn_has_code b d func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  qabbrev_tac `u = mstore (w2n dw) w s` >>
  qabbrev_tac `tn0 = tn with t_mem := tn.t_mem DIFF
    {i | w2n dw <= i /\ i < w2n dw+32}` >>
  `step_prov PG G (mk_inst a.cs_next_id MSTORE [Var xd; Var lv] []) u = G /\
   step_taint (mk_inst a.cs_next_id MSTORE [Var xd; Var lv] []) s u tn = tn0` by
    suspend "store_ghost" >>
  `gas_origin_ptr_path
    (<| d_stor := K (K {}); d_trans := K (K {}); d_imm := K {}; d_ret := K {} |>,
       lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),G,tn0)` by
    suspend "store_path" >>
  suspend "adds"
QED

Resume typed_copy_origin_ptr_dyn_data_path[store_ghost]:
  rpt strip_tac >>
  simp[Abbr `u`, Abbr `tn0`, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, venomInstTheory.mk_inst_def, set_var_taint_def,
       finite_mapTheory.DRESTRICT_UNIV, store_taint_def, adopt_reset_def,
       mem_taint_def, step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def, venomStateTheory.eval_operand_def,
       written_taint_def, range_bytes_def, new_site_bytes_def,
       venomStateTheory.mstore_def, finite_mapTheory.FLOOKUP_DEF,
       imm_taint_def, taint_component_equality, pred_setTheory.EXTENSION, SF CONJ_ss]
QED

Resume typed_copy_origin_ptr_dyn_data_path[store_path]:
  mp_tac (typed_copy_emit_inst_origin_ptr_path |> Q.INST
    [`sa` |-> `a`, `sb` |-> `b`, `opc` |-> `MSTORE`,
     `args` |-> `[Var xd; Var lv]`, `outs` |-> `[]`,
     `D` |-> `<| d_stor := K (K {}); d_trans := K (K {});
                  d_imm := K {}; d_ret := K {} |>`]) >>
  simp[] >> disch_then irule >>
  simp[emit_inst_def, GSYM emit_void_def, venomInstTheory.is_terminator_def] >>
  rpt conj_tac
  >~ [`inst_mem_below_frontier _ _`] >- suspend "store_mem"
  >~ [`ptr_inst_ok _ _ _ _ _ _ _ _ _`] >- suspend "store_ptr" >>
  simp[Abbr `u`, venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def,
       venomExecSemanticsTheory.exec_write2_def] >>
  gvs[venomStateTheory.eval_operand_def]
QED

Resume typed_copy_origin_ptr_dyn_data_path[store_mem]:
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       venomInstTheory.mk_inst_def, venomStateTheory.eval_operand_def] >>
  decide_tac
QED

Resume typed_copy_origin_ptr_dyn_data_path[store_ptr]:
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
       venomInstTheory.mk_inst_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def,
       venomStateTheory.eval_operand_def] >>
  gvs[ptr_covers_def] >>
  simp[memLocDefsTheory.mem_write_ops_def, op_prov_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomExecSemanticsTheory.exec_write2_def,
       venomStateTheory.eval_operand_def, venomStateTheory.mstore_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]
QED

Resume typed_copy_origin_ptr_dyn_data_path[adds]:
  qabbrev_tac `s0 = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `fn_has_code b c func /\ fn_has_code c d func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `not_fresh_at b xs /\ not_fresh_at c xd /\ sdv <> ddv` by
    (gvs[emit_void_def, emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         not_fresh_at_def] >> simp[]) >>
  `b.cs_current_bb = a.cs_current_bb /\
   LENGTH b.cs_current_insts = SUC (LENGTH a.cs_current_insts)` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  `lookup_var xs s0 = SOME sw /\ ptr_covers G tn0 xs s0 S' /\
   allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\ ~s0.vs_halted /\
   s0.vs_current_bb = b.cs_current_bb /\
   s0.vs_inst_idx = LENGTH b.cs_current_insts` by
    (gvs[Abbr `s0`, Abbr `u`, Abbr `tn0`, venomStateTheory.mstore_def,
         venomStateTheory.lookup_var_def, ptr_covers_def, op_taint_def, allocas_from_def] >>
     metis_tac[]) >>
  drule_all (typed_copy_origin_ptr_offset_path |> Q.SPECL [`32`,`S'`]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s1` (qx_choose_then `G1`
      (qx_choose_then `tn1` strip_assume_tac)))) >>
  suspend "second_add"
QED

Resume typed_copy_origin_ptr_dyn_data_path[second_add]:
  `xd <> sdv` by metis_tac[] >>
  `lookup_var xd s1 = SOME dw /\ ptr_covers G1 tn1 xd s1 T' /\
   allocas_from lo s1 /\ lo <= s1.vs_alloca_next` by
    (simp[Abbr `s0`, Abbr `u`, Abbr `tn0`, venomStateTheory.mstore_def,
          venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, ptr_covers_def, op_taint_def,
          allocas_from_def] >>
     gvs[ptr_covers_def, op_taint_def,
         venomStateTheory.lookup_var_def, allocas_from_def] >> metis_tac[]) >>
  drule_all (typed_copy_origin_ptr_offset_path |> Q.SPECL [`32`,`T'`]) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `s2` (qx_choose_then `G2`
      (qx_choose_then `tn2` strip_assume_tac)))) >>
  qexistsl_tac [`s2`,`G2`,`tn2`] >>
  conj_tac >- suspend "compose" >>
  suspend "data_post"
QED

Resume typed_copy_origin_ptr_dyn_data_path[compose]:
  metis_tac[gas_origin_ptr_path_append, listTheory.APPEND_NIL]
QED

Resume typed_copy_origin_ptr_dyn_data_path[data_post]:
  `!p. not_fresh_at a p ==>
      lookup_var p s2 = lookup_var p s /\ FLOOKUP G2 p = FLOOKUP G p /\
      op_taint tn2 (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >>
     `p <> sdv /\ p <> ddv` by metis_tac[] >>
     simp[Abbr `s0`, Abbr `u`, venomStateTheory.update_var_def,
          venomStateTheory.mstore_def, venomStateTheory.lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
     `op_taint tn0 (Var p) = op_taint tn (Var p)` by
       simp[Abbr `tn0`, op_taint_def] >> metis_tac[]) >>
  conj_tac >- suspend "data_frame" >>
  simp[Abbr `tn0`] >>
  rpt conj_tac
  >~ [`ptr_covers _ _ xs _ _`] >- suspend "old_coverage"
  >~ [`ptr_covers _ _ xd _ _`] >- suspend "old_coverage"
  >~ [`ptr_covers _ _ sdv _ _`] >- suspend "sdv_coverage"
  >~ [`mem_word_at _ _`] >- suspend "header_robust" >>
  simp[Abbr `s0`, Abbr `u`, venomStateTheory.update_var_def,
       venomStateTheory.mstore_def, venomStateTheory.eval_operand_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      ptr_covers_def, venomStateTheory.update_var_def,
      venomStateTheory.mstore_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Resume typed_copy_origin_ptr_dyn_data_path[data_frame]:
  `typed_copy_state_frame a (w2n dw) 32 s s0` by
    simp[Abbr `s0`, Abbr `u`, typed_copy_mstore_state_frame] >>
  gvs[typed_copy_state_frame_def, Abbr `s0`, Abbr `u`,
       venomStateTheory.update_var_def] >>
  metis_tac[]
QED

Resume typed_copy_origin_ptr_dyn_data_path[old_coverage]:
  markerLib.RESUME_TAC >>
  gvs[ptr_covers_def, Abbr `s0`, Abbr `u`,
      venomStateTheory.update_var_def, venomStateTheory.mstore_def,
      venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
      finite_mapTheory.FLOOKUP_UPDATE, op_taint_def] >> metis_tac[]
QED

Resume typed_copy_origin_ptr_dyn_data_path[sdv_coverage]:
  gvs[ptr_covers_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Resume typed_copy_origin_ptr_dyn_data_path[header_robust]:
  gen_tac >> strip_tac >>
  `s2.vs_memory = (mstore (w2n dw) w s).vs_memory` by
    simp[Abbr `s0`, Abbr `u`, venomStateTheory.update_var_def] >>
  `mem_bytes_at (w2n dw) 32 mem =
   mem_bytes_at (w2n dw) 32 s2.vs_memory` by
    (irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
     gvs[mem_agree_outside_def] >> rpt strip_tac >>
     first_x_assum irule >> simp[]) >>
  fs[GSYM entryDecodeStaticPropsTheory.mem_bytes_at_word_eq, Abbr `u`,
     valueEncodingPropsTheory.mem_bytes_at_mstore_same]
QED

Finalise typed_copy_origin_ptr_dyn_data_path

Theorem typed_copy_origin_ptr_dynarray_entry:
  !cenv tenv ctx de cap sty dtv stv v.
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields tenv /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname, fty, sz). !tv.
        evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
    type_widens_to tenv sty (ArrayT de (Dynamic cap)) /\
    evaluate_type tenv sty = SOME stv /\
    evaluate_type tenv (ArrayT de (Dynamic cap)) = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    (!cd cs cdt cst cv.
      type_rank cenv.ce_struct_fields cd <
        type_rank cenv.ce_struct_fields (ArrayT de (Dynamic cap)) ==>
      type_widens_to tenv cs cd /\ evaluate_type tenv cs = SOME cst /\
      evaluate_type tenv cd = SOME cdt /\ value_has_type cst cv /\
      value_has_type cdt cv /\ val_wf cst cv /\ val_wf cdt cv ==>
      typed_copy_origin_ptr_entry cenv ctx cd cs cdt cst cv) ==>
    typed_copy_origin_ptr_entry cenv ctx (ArrayT de (Dynamic cap)) sty dtv stv v
Proof
  cheat
QED
