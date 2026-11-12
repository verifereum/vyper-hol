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
