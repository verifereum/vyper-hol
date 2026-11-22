(* The static window starts just before the blueprint DALLOCA.  Its
 * consuming instruction is a fact about the code, not about the run. *)
Theory entryBlueprintBudgetSite
Ancestors
  dallocaCreateGeometry externalEntryShape fragExec contextCodegenRel
  builtinCreate context compileEnv emitHelper exprLoweringProps emitHelperProps
  venomExecSemantics venomExecProofs venomInst venomState list rich_list pair

Definition entry_blueprint_window_def:
  entry_blueprint_window fn i s <=>
    ?bb a m n e c add effect rest target value salt offset code args_ptr
       args_len sz ptr.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      s.vs_current_bb = a.cs_current_bb /\
      s.vs_inst_idx = SUC (LENGTH a.cs_current_insts) /\
      DROP (LENGTH a.cs_current_insts) bb.bb_instructions =
        add :: i :: (emitted_insts n c ++ effect :: rest) /\
      emitted_insts a m = [add] /\
      add.inst_opcode = ADD /\ add.inst_operands = [code;args_len] /\
      emitted_insts m n = [i] /\
      i.inst_opcode = DALLOCA /\ i.inst_operands = [sz] /\
      emit_op ADD [code;args_len] a = (sz,m) /\
      compile_alloc_dynamic sz m = (ptr,n) /\
      emit_void EXTCODECOPY [target;ptr;offset;code] n = ((),e) /\
      (if args_len = Lit 0w then c = e else
         ?dst x. emit_op ADD [ptr;code] e = (dst,x) /\
                 compile_copy_memory_dynamic dst args_ptr args_len x = ((),c)) /\
      (case salt of
         NONE => effect.inst_opcode = CREATE /\
                 effect.inst_operands = [value;ptr;sz]
       | SOME salt_op => effect.inst_opcode = CREATE2 /\
                         effect.inst_operands = [value;ptr;sz;salt_op]) /\
      EVERY (\j. ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                     CREATE;CREATE2;INVOKE] /\
                 ~is_terminator j.inst_opcode) (emitted_insts n c)
End

Theorem blueprint_emit_op[local]:
  emit_op opc ops a = (v,b) ==>
  b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  ?j. emitted_insts a b = [j] /\ j.inst_opcode = opc /\ j.inst_operands = ops
Proof
  strip_tac >> drule emit_op_extends >> drule emitted_insts_emit_op >>
  simp[same_blocks_def, mk_inst_def]
QED

Theorem blueprint_emit_void[local]:
  emit_void opc ops a = ((),b) ==>
  b.cs_blocks = a.cs_blocks /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
  ?j. emitted_insts a b = [j] /\ j.inst_opcode = opc
Proof
  strip_tac >> drule emit_void_extends >> drule emitted_insts_emit_void >>
  simp[same_blocks_def, mk_inst_def]
QED

Theorem blueprint_append_segment[local]:
  !a m n e c d target value salt offset code args_ptr args_len sz ptr created.
  emit_op ADD [code;args_len] a = (sz,m) /\
  compile_alloc_dynamic sz m = (ptr,n) /\
  emit_void EXTCODECOPY [target;ptr;offset;code] n = ((),e) /\
  (if args_len = Lit 0w then c = e else
     ?dst x. emit_op ADD [ptr;code] e = (dst,x) /\
             compile_copy_memory_dynamic dst args_ptr args_len x = ((),c)) /\
  (case salt of NONE => emit_op CREATE [value;ptr;sz]
     | SOME salt_op => emit_op CREATE2 [value;ptr;sz;salt_op]) c = (created,d) ==>
  cs_extends a d /\ d.cs_current_bb = a.cs_current_bb /\
  ?add i effect.
    d.cs_current_insts = a.cs_current_insts ++
      (add :: i :: (emitted_insts n c ++ [effect])) /\
    emitted_insts a m = [add] /\
    add.inst_opcode = ADD /\ add.inst_operands = [code;args_len] /\
    emitted_insts m n = [i] /\
    i.inst_opcode = DALLOCA /\ i.inst_operands = [sz] /\
    (case salt of
       NONE => effect.inst_opcode = CREATE /\
               effect.inst_operands = [value;ptr;sz]
     | SOME salt_op => effect.inst_opcode = CREATE2 /\
                       effect.inst_operands = [value;ptr;sz;salt_op]) /\
    EVERY (\j. ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                   CREATE;CREATE2;INVOKE] /\
               ~is_terminator j.inst_opcode) (emitted_insts n c)
Proof
  rpt gen_tac >> Cases_on `args_len = Lit 0w` >> Cases_on `salt` >>
  simp[compile_alloc_dynamic_def, compile_copy_memory_dynamic_def] >>
  strip_tac >>
  rpt (FIRST [dxrule blueprint_emit_op, dxrule blueprint_emit_void] >> strip_tac) >>
  (conj_tac >- (simp[cs_extends_def] >>
                pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[])) >>
  simp[] >>
  simp[emitted_insts_def, DROP_APPEND, is_terminator_def] >>
  `LENGTH a.cs_current_insts + 2 - (LENGTH a.cs_current_insts + 3) = 0 /\
   LENGTH a.cs_current_insts + 2 - (LENGTH a.cs_current_insts + 4) = 0`
    by decide_tac >>
  simp[DROP_LENGTH_TOO_LONG, is_terminator_def]
QED

Theorem blueprint_append_window:
  compile_create_blueprint_append target value salt offset code args_ptr
    args_len rof a = (result,b) /\
  fn_has_code a b fn /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = SUC (LENGTH a.cs_current_insts) ==>
  ?i. active_inst fn i s /\ entry_blueprint_window fn i s
Proof
  strip_tac >> drule create_blueprint_create_prefix >> strip_tac >>
  drule_all blueprint_append_segment >> strip_tac >>
  `cs_extends sd b` by metis_tac[compile_check_create_result_labels, SND] >>
  `fn_has_code sd b fn` by metis_tac[fn_has_code_split] >>
  drule_all fn_has_code_start >> strip_tac >>
  fs[IS_PREFIX_APPEND] >>
  rename1 `bb.bb_instructions = _ ++ rest` >>
  rename1 `emit_op ADD [code;args_len] a = (sz,sm)` >>
  rename1 `emitted_insts a sm = [add_inst]` >>
  `DROP (LENGTH a.cs_current_insts) bb.bb_instructions =
      add_inst :: i :: (emitted_insts sn sc ++ effect :: rest)` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     REFL_TAC) >>
  qexists_tac `i` >> conj_tac
  >- (`DROP s.vs_inst_idx bb.bb_instructions =
         i :: (emitted_insts sn sc ++ effect :: rest)` by metis_tac[DROP_EQ_CONS] >>
      simp[active_inst_def] >> qexists_tac `bb` >>
      metis_tac[DROP_EQ_CONS, lookup_block_MEM, lookup_block_label]) >>
  pure_rewrite_tac[entry_blueprint_window_def] >>
  qexistsl_tac [`bb`,`a`,`sm`,`sn`,`se`,`sc`,`add_inst`,`effect`,`rest`,
                `target`,`value`,`salt`,`offset`,`code`,`args_ptr`,`args_len`,
                `sz`,`alloc_ptr`] >>
  simp[] >> metis_tac[]
QED

(* The append up to (and including) the consuming CREATE, before the
 * result check. The initial state's label and instruction prefix are
 * retained when this segment is placed in a completed block. *)
Definition blueprint_append_code_def:
  blueprint_append_code target value salt offset code args_ptr args_len a created d chunk <=>
    ?m n e c add alloc effect sz ptr.
      cs_extends a d /\ d.cs_current_bb = a.cs_current_bb /\
      d.cs_current_insts = a.cs_current_insts ++ chunk /\
      chunk = add :: alloc :: (emitted_insts n c ++ [effect]) /\
      emitted_insts a m = [add] /\
      add.inst_opcode = ADD /\ add.inst_operands = [code;args_len] /\
      emitted_insts m n = [alloc] /\
      alloc.inst_opcode = DALLOCA /\ alloc.inst_operands = [sz] /\
      emit_op ADD [code;args_len] a = (sz,m) /\
      compile_alloc_dynamic sz m = (ptr,n) /\
      emit_void EXTCODECOPY [target;ptr;offset;code] n = ((),e) /\
      (if args_len = Lit 0w then c = e else
         ?dst x. emit_op ADD [ptr;code] e = (dst,x) /\
                 compile_copy_memory_dynamic dst args_ptr args_len x = ((),c)) /\
      (case salt of NONE => emit_op CREATE [value;ptr;sz]
       | SOME salt_op => emit_op CREATE2 [value;ptr;sz;salt_op]) c = (created,d) /\
      (case salt of
         NONE => effect.inst_opcode = CREATE /\
                 effect.inst_operands = [value;ptr;sz]
       | SOME salt_op => effect.inst_opcode = CREATE2 /\
                         effect.inst_operands = [value;ptr;sz;salt_op]) /\
      EVERY (\j. ~MEM j.inst_opcode [DALLOCA;CALL;STATICCALL;DELEGATECALL;
                                     CREATE;CREATE2;INVOKE] /\
                 ~is_terminator j.inst_opcode) (emitted_insts n c)
End

Theorem blueprint_append_segment_geometry:
  compile_create_blueprint_append target value salt offset code args_ptr
    args_len rof a = (result,b) ==>
  ?created d chunk.
    blueprint_append_code target value salt offset code args_ptr args_len a created d chunk /\
    compile_check_create_result created rof d = (result,b)
Proof
  strip_tac >> drule create_blueprint_create_prefix >> strip_tac >>
  drule_all blueprint_append_segment >> strip_tac >>
  qexistsl_tac [`created`,`sd`,`add' :: i :: (emitted_insts sn sc ++ [effect])`] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[blueprint_append_code_def] >>
  qexistsl_tac [`sm`,`sn`,`se`,`sc`,`add'`,`i`,`effect`,`size'`,`alloc_ptr`] >>
  asm_rewrite_tac[]
QED

Theorem blueprint_append_code_only_dalloca:
  blueprint_append_code target value salt offset code args_ptr args_len a created d chunk ==>
  1 < LENGTH chunk /\ (EL 1 chunk).inst_opcode = DALLOCA /\
  !k. k < LENGTH chunk /\ (EL k chunk).inst_opcode = DALLOCA ==> k = 1
Proof
  Cases_on `salt` >>
  rw[blueprint_append_code_def] >> simp[] >>
  `EVERY (\j. j.inst_opcode <> DALLOCA) (emitted_insts n c ++ [effect])` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `k` >> gvs[] >>
  rename1 `j = 0` >> Cases_on `j` >> gs[EL_APPEND_EQN, EVERY_EL] >>
  rename1 `idx < LENGTH (emitted_insts n c) + 1` >>
  `idx < LENGTH (emitted_insts n c) \/ idx = LENGTH (emitted_insts n c)` by decide_tac >>
  gvs[]
QED
