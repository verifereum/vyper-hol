(* Runtime-bound dynamic payload traversal and its compiler frontier. *)
Theory annAssignTypedCopyDynamicLoopPtr
Ancestors
  typedNormalizeDynarrayLoop annAssignTypedCopyFixedMetadataPtr
  annAssignTypedCopyArrayTraversalPtr typedMemoryCopy fragGasPathPtr
  bodyPtrDefs context compileEnv fragExec exprLoweringProps
  venomState venomInst venomExecSemantics words arithmetic list

Theorem annassign_dynamic_child_frontier:
  ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
  compile_copy_dynarray_typed ce dst dt cap src st sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?si se.
    compile_store_memory_typed ce
      (Var ("%" ++ toString (sa.cs_next_var+11))) dt
      (Var ("%" ++ toString (sa.cs_next_var+10))) st si = ((),se) /\
    si.cs_current_bb = fresh_label_output "typed_dyn_body" (sa.cs_next_label+1) /\
    LENGTH si.cs_current_insts = 4 /\ si.cs_next_var = sa.cs_next_var+12 /\
    cs_extends sa si /\ cs_extends si se /\ cs_extends se sb /\
    fn_has_code si se fn /\
    (!j. j < 12 ==> not_fresh_at si ("%" ++ toString (sa.cs_next_var+j))) /\
    (!x j. not_fresh_at sa x ==> x <> "%" ++ toString (sa.cs_next_var+j)) /\
    (!x. not_fresh_at sa x ==> not_fresh_at si x) /\
    ALL_DISTINCT (GENLIST (\j. "%" ++ toString (sa.cs_next_var+j)) 12) /\
    (?body. lookup_block si.cs_current_bb fn.fn_blocks = SOME body /\
      isPREFIX si.cs_current_insts body.bb_instructions) /\
    (?back. lookup_block se.cs_current_bb fn.fn_blocks = SOME back /\
      back.bb_instructions = se.cs_current_insts ++
        typed_sa_backedge_insts se.cs_next_id
          ("%" ++ toString (sa.cs_next_var+5)) ("%" ++ toString se.cs_next_var)
          (fresh_label_output "typed_dyn_cond" sa.cs_next_label)) /\
    sb.cs_current_bb = fresh_label_output "typed_dyn_exit" (sa.cs_next_label+2) /\
    sb.cs_current_insts = []
Proof
  strip_tac >> drule_all typed_dynarray_child_states >> strip_tac >>
  `cs_extends sc ec` by gvs[ci_mono_def] >>
  `?body. lookup_block sc.cs_current_bb fn.fn_blocks = SOME body /\
    isPREFIX sc.cs_current_insts body.bb_instructions` by
    metis_tac[fn_has_code_start] >>
  `?back. lookup_block ec.cs_current_bb fn.fn_blocks = SOME back /\
    back.bb_instructions = ec.cs_current_insts ++
      typed_sa_backedge_insts ec.cs_next_id
        ("%" ++ toString (sa.cs_next_var+5)) ("%" ++ toString ec.cs_next_var)
        (fresh_label_output "typed_dyn_cond" sa.cs_next_label)` by
    (qpat_x_assum `fn_has_code ec sb fn` mp_tac >>
     simp[fn_has_code_def, emitted_blocks_def] >> strip_tac >>
     first_x_assum (qspec_then `HD sb.cs_blocks` mp_tac) >> simp[]) >>
  qexistsl_tac [`sc`,`ec`] >> simp[] >>
  `sa.cs_next_var+12 <= sc.cs_next_var` by simp[] >>
  drule annassign_generated_register_range >> strip_tac >>
  gvs[ci_mono_def]
QED
