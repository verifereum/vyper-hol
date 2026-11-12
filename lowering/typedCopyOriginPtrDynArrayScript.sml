(* The joint typed memory copy of a dynamic array: length, check, data. *)
Theory typedCopyOriginPtrDynArray
Ancestors
  typedCopyOriginPtrBase placeTypedCopyRecursivePath fragGasOriginPtr fragGasSeqPtr
  bodyPtrDefs ptrSafeRun ptrDiscipline typedMemoryCopy

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
