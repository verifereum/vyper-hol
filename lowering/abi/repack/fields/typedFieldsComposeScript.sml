(* TOP-LEVEL: root operands survive a field prefix, and actual head/tail
   execution paths compose with complete tuple memory and operand frames. *)
Theory typedFieldsCompose
Ancestors
  typedFieldsMemory typedCopyOperandFrames typedSArrayDynInvariant
  abiStaticLoopCode memoryValueDefs valueEncoding
  fragExec fragBlockPath venomState venomInst list arithmetic

Theorem compiler_operands_survive_prefix:
  !dst src var_start var_mid var_end initial middle.
    var_start <= var_mid /\ var_mid <= var_end /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names var_start (var_end - var_start)) /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names var_start (var_mid - var_start)) ==>
      eval_operand arg_op middle = eval_operand arg_op initial) ==>
    eval_operand dst middle = eval_operand dst initial /\
    eval_operand src middle = eval_operand src initial /\
    EVERY (\name. dst <> Var name /\ src <> Var name)
      (compiler_var_names var_mid (var_end - var_mid))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `var_start`, `var_start`, `var_mid`, `var_end`]
    compiler_operands_avoid_interval) >> impl_tac >- simp[] >> DISCH_TAC >>
  drule_all compiler_operands_frame_pair >> strip_tac >> asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`dst`, `src`, `var_start`, `var_mid`, `var_end`, `var_end`]
    compiler_operands_avoid_interval) >> simp[]
QED

Theorem tuple_fields_copy_compose:
  !ctx func ftv ftvs v vs dst_off var_start var_mid var_end initial middle final.
    var_start <= var_mid /\ var_mid <= var_end /\
    fragment_path ctx func initial middle /\ fragment_path ctx func middle final /\
    value_has_type ftv v /\ memory_value_rel ftv v dst_off middle.vs_memory /\
    memory_tuple_rel ftvs vs (dst_off + type_memory_size ftv) final.vs_memory /\
    array_copy_frame ftv 1 dst_off initial.vs_memory middle.vs_memory /\
    array_copy_frame (TupleTV ftvs) 1 (dst_off + type_memory_size ftv) middle.vs_memory final.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names var_start (var_mid - var_start)) ==>
      eval_operand arg_op middle = eval_operand arg_op initial) /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names var_mid (var_end - var_mid)) ==>
      eval_operand arg_op final = eval_operand arg_op middle) ==>
    fragment_path ctx func initial final /\
    memory_tuple_rel (ftv::ftvs) (v::vs) dst_off final.vs_memory /\
    array_copy_frame (TupleTV (ftv::ftvs)) 1 dst_off initial.vs_memory final.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name)
      (compiler_var_names var_start (var_end - var_start)) ==>
      eval_operand arg_op final = eval_operand arg_op initial)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule fragment_path_trans >> qexists_tac `middle` >> simp[]) >> conj_tac
  >- (mp_tac (Q.SPECL [`ftv`, `ftvs`, `v`, `vs`, `dst_off`, `middle.vs_memory`, `final.vs_memory`]
       tuple_copy_target_cons) >> simp[]) >> conj_tac
  >- (mp_tac (Q.SPECL [`ftv`, `ftvs`, `dst_off`, `initial.vs_memory`, `middle.vs_memory`, `final.vs_memory`]
       tuple_copy_frame_cons) >> simp[]) >>
  mp_tac (Q.SPECL [`var_start`, `var_mid`, `var_end`, `initial`, `middle`, `final`]
    compiler_operands_frame_intervals) >> simp[]
QED
