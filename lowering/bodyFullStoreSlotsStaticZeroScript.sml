Theory bodyFullStoreSlotsStaticZero
Ancestors
  externalReturnZeroLayout abiTypeBoundProps typedMemoryCopy
  placeStaticCopyExit placeStoreCopyPath fragGasMode fragGasSeqAbort
  context compileEnv valueEncodingProps valueEncodingDefs
  venomExecSemantics venomState venomInst list rich_list words arithmetic finite_map

Theorem slots_zero_layout_compiler_static:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ type_slot_size tv = 0 ==>
  ~is_abi_dynamic cenv.ce_struct_fields ty /\ type_memory_bytes cenv ty = 0
Proof
  strip_tac >>
  `type_memory_size tv = 0` by simp[type_memory_size_slots] >>
  `~vyper_is_dynamic tenv ty` by
    metis_tac[evaluated_zero_layout_static] >>
  conj_tac
  >- metis_tac[abi_props_vyper_typed] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typed_copy_memory_size >> metis_tac[]) >> simp[]
QED

(* The zero-count word loop executes only its initializer and first test.
   Jumps are recorded before any external continuation PHIs are entered. *)
Theorem slots_zero_readonly_completion:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
      sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ type_slot_size tv = 0 /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?states.
    states <> [] /\ HD states = s /\
    (LAST states).vs_current_bb = sb.cs_current_bb /\
    (LAST states).vs_inst_idx = LENGTH sb.cs_current_insts /\
    EVERY (\q. ~q.vs_halted) states /\
    (!j. SUC j < LENGTH states ==>
      ?bb inst mid.
        lookup_block (EL j states).vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb (EL j states).vs_inst_idx = SOME inst /\
        MEM inst.inst_opcode [ASSIGN; EQ; JMP; JNZ] /\
        step_inst 0 ctx inst (EL j states) = OK mid /\
        ((~is_terminator inst.inst_opcode /\
          EL (SUC j) states = mid with vs_inst_idx :=
            SUC (EL j states).vs_inst_idx) \/
         (?lbl. is_terminator inst.inst_opcode /\
           mid = jump_to lbl (EL j states) /\ EL (SUC j) states = mid)))
Proof
  strip_tac >>
  drule_all slots_zero_layout_compiler_static >> strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `(if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst 0 sa = (ret,sb)` >>
  `compile_word_copy_loop_op src dst (Lit 0w) LocMemory
     (if tr then LocTransient else LocStorage) F sa = (ret,sb)` by
    (Cases_on `tr` >>
     gvs[compile_memory_to_storage_def, compile_memory_to_transient_def,
         compile_word_copy_loop_def]) >>
  qpat_assum `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`
    (mp_then Any (qspec_then `func` mp_tac) place_store_runtime_copy_code) >>
  (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
  suspend "trace"
QED

Resume slots_zero_readonly_completion[trace]:
  rename1 `mk_inst idh EQ [Var cv; Lit 0w] [test]` >>
  qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
    (mp_then Any strip_assume_tac instruction_prefix_cursor) >>
  drule instruction_prefix_cursor >> strip_tac >>
  qpat_x_assum `isPREFIX [mk_inst _ EQ _ _; _] _`
    (strip_assume_tac o REWRITE_RULE [IS_PREFIX_APPEND]) >>
  `get_instruction bbh 0 = SOME (mk_inst idh EQ [Var cv; Lit 0w] [test]) /\
   get_instruction bbh 1 = SOME
     (mk_inst (idh+1) JNZ [Var test; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def] >>
  qabbrev_tac `a = (update_var cv 0w s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `b = jump_to hdr a` >>
  qabbrev_tac `c = (update_var test 1w b) with vs_inst_idx := 1` >>
  qexists_tac `[s; a; b; c; jump_to exit c]` >>
  simp[Abbr `a`, Abbr `b`, Abbr `c`, update_var_def, jump_to_def] >>
  rpt strip_tac >>
  `j = 0 \/ j = 1 \/ j = 2 \/ j = 3` by decide_tac >>
  gvs[] >> suspend "edges"
QED

Resume slots_zero_readonly_completion[edges]:
  markerLib.RESUME_TAC >>
  simp[step_inst_non_invoke, mk_inst_def, step_inst_base_opcode_eqs,
       is_terminator_def, exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, jump_to_def, bool_to_word_def,
       FLOOKUP_UPDATE] >> metis_tac[]
QED
Finalise slots_zero_readonly_completion
