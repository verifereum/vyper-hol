(* TOP-LEVEL: the repacking loop invariant retains the complete source,
   an increasing target prefix, all disjoint typed memory and live operands.
   Helpers compose memory frames independently of instruction generation. *)
Theory typedSArrayDynInvariant
Ancestors
  typedArrayCopyMemory abiBytestringCode abiStaticLoopCode
  memoryValueDefs valueEncoding compileEnv venomState venomInst list words arithmetic

Definition array_copy_frame_def:
  array_copy_frame ftv copy_count dst_off before_mem after_mem <=>
    !other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off \/
        dst_off + copy_count * type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem
End

Theorem array_copy_frame_refl[simp]:
  !ftv copy_count dst_off mem. array_copy_frame ftv copy_count dst_off mem mem
Proof
  simp[array_copy_frame_def]
QED

Theorem array_copy_frame_trans:
  !ftv copy_count dst_off before_mem mid_mem after_mem.
    array_copy_frame ftv copy_count dst_off before_mem mid_mem /\
    array_copy_frame ftv copy_count dst_off mid_mem after_mem ==>
    array_copy_frame ftv copy_count dst_off before_mem after_mem
Proof
  rpt gen_tac >> simp_tac bool_ss [array_copy_frame_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `memory_value_rel other_tv other_v offset mid_mem` by
    (qpat_x_assum `!other_tv other_v offset. memory_value_rel _ _ _ before_mem /\ _ ==> _`
      (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `!other_tv other_v offset. memory_value_rel _ _ _ mid_mem /\ _ ==> _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem array_copy_fixed_frame:
  !tv copy_count dst_off before_mem after_mem.
    array_copy_frame tv copy_count dst_off before_mem after_mem ==>
    !other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off \/
        dst_off + type_memory_size (ArrayTV tv (Fixed copy_count)) <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem
Proof
  rpt gen_tac >> rewrite_tac[array_copy_frame_def] >> DISCH_TAC >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `_ \/ _` mp_tac >> simp_tac bool_ss [type_memory_size_def] >> DISCH_TAC >>
  qpat_x_assum `!other_tv other_v offset. _`
    (qspecl_then [`other_tv`, `other_v`, `offset`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Definition array_copy_memory_inv_def:
  array_copy_memory_inv ftv atv at_index copy_count src_off dst_off initial_mem i current_mem <=>
    array_copy_prefix atv at_index copy_count src_off current_mem /\
    array_copy_prefix ftv at_index i dst_off current_mem /\
    array_copy_frame ftv copy_count dst_off initial_mem current_mem
End

Theorem array_copy_memory_inv_initial:
  !ftv atv at_index copy_count src_off dst_off mem.
    array_copy_prefix atv at_index copy_count src_off mem ==>
    array_copy_memory_inv ftv atv at_index copy_count src_off dst_off mem 0 mem
Proof
  simp[array_copy_memory_inv_def]
QED

Theorem array_copy_memory_inv_source:
  !ftv atv at_index copy_count src_off dst_off initial_mem copied current_mem i.
    array_copy_memory_inv ftv atv at_index copy_count src_off dst_off initial_mem copied current_mem /\
    i < copy_count ==>
    memory_value_rel atv (at_index i) (src_off + i * type_memory_size atv) current_mem
Proof
  rpt gen_tac >> simp_tac bool_ss [array_copy_memory_inv_def, array_copy_prefix_def] >> strip_tac >>
  qpat_x_assum `!j. j < copy_count ==> memory_value_rel atv _ _ _` (qspec_then `i` mp_tac) >> simp[]
QED

Theorem array_copy_memory_inv_step:
  !ftv atv at_index copy_count i src_off dst_off initial_mem before_mem after_mem.
    array_copy_memory_inv ftv atv at_index copy_count src_off dst_off initial_mem i before_mem /\
    i < copy_count /\ (!j. j < copy_count ==> val_wf atv (at_index j)) /\
    (!j. j < i ==> val_wf ftv (at_index j)) /\
    (src_off + copy_count * type_memory_size atv <= dst_off \/
      dst_off + copy_count * type_memory_size ftv <= src_off) /\
    memory_value_rel ftv (at_index i) (dst_off + i * type_memory_size ftv) after_mem /\
    (!other_tv other_v offset.
      memory_value_rel other_tv other_v offset before_mem /\ val_wf other_tv other_v /\
      (offset + type_memory_size other_tv <= dst_off + i * type_memory_size ftv \/
        dst_off + i * type_memory_size ftv + type_memory_size ftv <= offset) ==>
      memory_value_rel other_tv other_v offset after_mem) ==>
    array_copy_memory_inv ftv atv at_index copy_count src_off dst_off initial_mem (SUC i) after_mem
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `array_copy_memory_inv _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [array_copy_memory_inv_def] >> strip_tac >>
  mp_tac (Q.SPECL [`ftv`, `atv`, `at_index`, `copy_count`, `i`, `src_off`, `dst_off`,
    `before_mem`, `after_mem`] array_copy_progress) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `array_copy_frame ftv copy_count dst_off before_mem after_mem` by
    (rewrite_tac[array_copy_frame_def] >> first_assum MATCH_ACCEPT_TAC) >>
  asm_simp_tac bool_ss [] >>
  irule array_copy_frame_trans >> qexists_tac `before_mem` >> simp[]
QED

Definition sarray_dynarray_loop_inv_def:
  sarray_dynarray_loop_inv var_base cond_label ftv atv at_index copy_count
      (dst_addr:bytes32) (src_addr:bytes32) initial i current <=>
    current.vs_current_bb = cond_label /\ current.vs_inst_idx = 0 /\ ~current.vs_halted /\
    eval_operand (Var (compiler_var_name var_base 0)) current = SOME (n2w i) /\
    array_copy_memory_inv ftv atv at_index copy_count (w2n src_addr) (w2n dst_addr)
      initial.vs_memory i current.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name) (compiler_var_names var_base 14) ==>
      eval_operand arg_op current = eval_operand arg_op initial)
End

Theorem compiler_operands_frame_trans:
  !names before mid after.
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op mid = eval_operand arg_op before) /\
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op mid) ==>
    !arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op before
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `arg_op` >> DISCH_TAC >>
  qpat_x_assum `!arg_op. _ ==> eval_operand _ mid = _` (qspec_then `arg_op` mp_tac) >>
  qpat_x_assum `!arg_op. _ ==> eval_operand _ after = _` (qspec_then `arg_op` mp_tac) >> simp[]
QED

Theorem compiler_operands_frame_pair:
  !names before after dst src.
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op before) /\
    EVERY (\name. dst <> Var name /\ src <> Var name) names ==>
    eval_operand dst after = eval_operand dst before /\
    eval_operand src after = eval_operand src before
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\name. dst <> Var name) names` by fs[EVERY_CONJ] >>
  `EVERY (\name. src <> Var name) names` by fs[EVERY_CONJ] >> conj_tac
  >- (qpat_x_assum `!arg_op. _` (qspec_then `dst` mp_tac) >> simp[]) >>
  qpat_x_assum `!arg_op. _` (qspec_then `src` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed fixed/dynamic array invariant theorem: " ^ name)
  end) (DB.thms "typedSArrayDynInvariant")
