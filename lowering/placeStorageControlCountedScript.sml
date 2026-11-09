(* Code-containment boundaries for the dynamic storage traversal. *)
Theory placeStorageControlCounted
Ancestors
  placeStorageElementPaths placeStorageLayoutCounted fragExec
  bodyMemAssignTopCopyCompiler emitHelper emitHelperProps compileEnv
  context venomInst list rich_list

Theorem dyn_storage_word_code:
  compile_dynarray_to_storage src dst 1 em tr sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  (!bb. MEM bb (TAKE 3 sb.cs_blocks) ==>
     lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX sb.cs_current_insts bb.bb_instructions
Proof
  strip_tac >> drule dyn_storage_word_layout >> strip_tac >>
  fs[fn_has_code_def, emitted_blocks_def]
QED

Theorem dyn_storage_suffix_layout:
  (do nc <- emit_op ADD [Var ctr; Lit 1w];
      emit_inst ASSIGN [nc] [ctr];
      emit_inst JMP [Label hdr] [];
      new_block exit;
      emit_void (if tr then TSTORE else SSTORE) [dst; Var len]
   od) sd = ((),sb) ==>
  sb.cs_current_bb = exit /\
  sb.cs_current_insts =
    [mk_inst (sd.cs_next_id+3) (if tr then TSTORE else SSTORE) [dst; Var len] []] /\
  sb.cs_blocks =
    <|bb_label := sd.cs_current_bb;
      bb_instructions := sd.cs_current_insts ++
        [mk_inst sd.cs_next_id ADD [Var ctr; Lit 1w] ["%" ++ toString sd.cs_next_var];
         mk_inst (sd.cs_next_id+1) ASSIGN [Var ("%" ++ toString sd.cs_next_var)] [ctr];
         mk_inst (sd.cs_next_id+2) JMP [Label hdr] []]|> :: sd.cs_blocks
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, emit_inst_def, emit_def, fresh_id_def,
    fresh_var_def, new_block_def] >> strip_tac >> gvs[]
QED

Theorem dyn_storage_suffix_extends:
  (do nc <- emit_op ADD [Var ctr; Lit 1w];
      emit_inst ASSIGN [nc] [ctr];
      emit_inst JMP [Label hdr] [];
      new_block exit;
      emit_void (if tr then TSTORE else SSTORE) [dst; Var len]
   od) sd = ((),sb) ==> cs_extends sd sb
Proof
  strip_tac >> drule dyn_storage_suffix_layout >> strip_tac >>
  simp[cs_extends_def] >>
  qexists_tac `TAKE 1 sb.cs_blocks` >> simp[IS_PREFIX_APPEND]
QED

Theorem dyn_storage_suffix_code:
  (do nc <- emit_op ADD [Var ctr; Lit 1w];
      emit_inst ASSIGN [nc] [ctr];
      emit_inst JMP [Label hdr] [];
      new_block exit;
      emit_void (if tr then TSTORE else SSTORE) [dst; Var len]
   od) sd = ((),sb) /\
  cs_extends sa sd /\ fn_has_code sa sb fn ==>
  fn_has_code sd sb fn /\
  lookup_block sd.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := sd.cs_current_bb;
      bb_instructions := sd.cs_current_insts ++
        [mk_inst sd.cs_next_id ADD [Var ctr; Lit 1w] ["%" ++ toString sd.cs_next_var];
         mk_inst (sd.cs_next_id+1) ASSIGN [Var ("%" ++ toString sd.cs_next_var)] [ctr];
         mk_inst (sd.cs_next_id+2) JMP [Label hdr] []]|> /\
  ?bb. lookup_block exit fn.fn_blocks = SOME bb /\
       isPREFIX [mk_inst (sd.cs_next_id+3) (if tr then TSTORE else SSTORE)
                   [dst; Var len] []] bb.bb_instructions
Proof
  strip_tac >> drule dyn_storage_suffix_layout >> strip_tac >>
  `cs_extends sd sb` by metis_tac[dyn_storage_suffix_extends] >>
  `fn_has_code sd sb fn` by metis_tac[fn_has_code_split] >>
  simp[] >> fs[fn_has_code_def, emitted_blocks_def] >> gvs[]
QED

Theorem dyn_storage_multi_code:
  ew <> 1 /\
  compile_dynarray_to_storage src dst ew em tr sa = ((),sb) /\
  fn_has_code sa sb fn ==>
  ?sc sd lbl.
    compile_word_copy_loop
      (Var ("%" ++ toString (sa.cs_next_var+6)))
      (Var ("%" ++ toString (sa.cs_next_var+9))) ew LocMemory
      (if tr then LocTransient else LocStorage) F sc = (lbl,sd) /\
    fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn /\
    sc.cs_next_var = sa.cs_next_var+10 /\
    LENGTH sc.cs_current_insts = 6 /\ sd.cs_current_insts = [] /\
    (!bb. MEM bb (TAKE 2 sc.cs_blocks) ==>
       lookup_block bb.bb_label fn.fn_blocks = SOME bb)
Proof
  strip_tac >> drule_all dyn_storage_multi_split >> strip_tac >>
  `cs_extends sa sc` by
    (simp[cs_extends_def] >> qexists_tac `TAKE 2 sc.cs_blocks` >>
     simp[IS_PREFIX_APPEND]) >>
  `cs_extends sd sb` by metis_tac[dyn_storage_suffix_extends] >>
  `cs_extends sc sd /\ sd.cs_current_insts = []` by
    (drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
       topcopy_compile_certificate >>
     (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
     conj_tac >- metis_tac[cs_extends_trans] >>
     qpat_x_assum `new_block _ _ = (_,sd)` mp_tac >> simp[new_block_def] >>
     strip_tac >> gvs[]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sd fn /\ fn_has_code sd sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  qexistsl_tac [`sc`, `sd`, `lbl`] >> simp[] >>
  fs[fn_has_code_def, emitted_blocks_def] >> gvs[] >> metis_tac[]
QED
