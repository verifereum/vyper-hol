(* TOP-LEVEL: saved Log argument lists survive a copied field. Source
   separation and freshness also restrict to smaller destination/name ranges. *)
Theory typedLogArgsFrames
Ancestors
  typedLogArgs typedLogValueFrames typedCopyOperandFrames typedSArrayDynInvariant
  valueLoadProps valueEncoding compileEnv venomState venomInst list words arithmetic

Theorem log_args_avoid_interval:
  !ops var_start sub_start sub_end var_end.
    var_start <= sub_start /\ sub_start <= sub_end /\ sub_end <= var_end /\
    log_args_avoid ops (compiler_var_names var_start (var_end - var_start)) ==>
    log_args_avoid ops (compiler_var_names sub_start (sub_end - sub_start))
Proof
  rpt gen_tac >> simp_tac bool_ss [log_args_avoid_def, EVERY_MEM] >> strip_tac >>
  qx_gen_tac `arg` >> DISCH_TAC >>
  qpat_x_assum `!arg. MEM arg ops ==> _` (qspec_then `arg` mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`FST (arg:operand # type)`, `var_start`, `sub_start`, `sub_end`, `var_end`]
    compiler_operand_avoid_interval) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [EVERY_MEM] >> NO_TAC]) >> simp[EVERY_MEM]
QED

Theorem log_args_safe_subrange:
  !ops tvs ss outer_off outer_size inner_off inner_size.
    log_args_safe ops tvs ss outer_off outer_size /\
    outer_off <= inner_off /\ inner_off + inner_size <= outer_off + outer_size ==>
    log_args_safe ops tvs ss inner_off inner_size
Proof
  Induct_on `ops`
  >- (rpt gen_tac >> Cases_on `tvs` >> simp[log_args_safe_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `tvs`, `ss`, `outer_off`, `outer_size`, `inner_off`, `inner_size`] >>
  Cases_on `arg` >> Cases_on `tvs` >- simp[log_args_safe_def] >>
  rename1 `log_args_safe ((src,ty)::ops) (tv::tvs) ss outer_off outer_size` >>
  simp_tac bool_ss [log_args_safe_def] >> strip_tac >> conj_tac
  >- (mp_tac (Q.SPECL [`src`, `ty`, `tv`, `ss`, `outer_off`, `outer_size`, `inner_off`, `inner_size`]
       log_arg_safe_subrange) >> simp[]) >>
  qpat_x_assum `!tvs ss outer_off outer_size inner_off inner_size. _`
    (qspecl_then [`tvs`, `ss`, `outer_off`, `outer_size`, `inner_off`, `inner_size`] mp_tac) >> simp[]
QED

Theorem log_args_frame:
  !ops tvs vs before after ftv copy_count dst_off names.
    log_args_rel ops tvs vs before /\
    log_args_safe ops tvs before dst_off (copy_count * type_memory_size ftv) /\
    log_args_avoid ops names /\
    array_copy_frame ftv copy_count dst_off before.vs_memory after.vs_memory /\
    (!arg_op. EVERY (\name. arg_op <> Var name) names ==>
      eval_operand arg_op after = eval_operand arg_op before) ==>
    log_args_rel ops tvs vs after /\
    log_args_safe ops tvs after dst_off (copy_count * type_memory_size ftv)
Proof
  Induct_on `ops`
  >- (rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >> simp[log_args_rel_def, log_args_safe_def]) >>
  MAP_EVERY qx_gen_tac [`arg`, `tvs`, `vs`, `before`, `after`, `ftv`, `copy_count`, `dst_off`, `names`] >>
  Cases_on `arg` >> Cases_on `tvs` >- simp[log_args_rel_def, log_args_safe_def] >>
  Cases_on `vs` >- simp[log_args_rel_def] >>
  rename1 `log_args_rel ((src,ty)::ops) (tv::tvs) (v::vs) before` >>
  simp_tac (srw_ss()) [log_args_rel_def, log_args_safe_def, log_args_avoid_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `eval_operand src after = eval_operand src before` by
    (qpat_x_assum `!arg_op. _` (qspec_then `src` mp_tac) >> simp[]) >>
  `lowered_value_rel ty tv v src after` by
    (mp_tac (Q.SPECL [`ty`, `tv`, `v`, `src`, `before`, `after`, `ftv`, `copy_count`, `dst_off`]
       lowered_value_rel_copy_frame) >> simp[]) >>
  `log_arg_safe src ty tv after dst_off (copy_count * type_memory_size ftv)` by
    (mp_tac (Q.SPECL [`src`, `ty`, `tv`, `before`, `after`, `dst_off`, `copy_count * type_memory_size ftv`]
       log_arg_safe_operand_frame) >> simp[]) >>
  qpat_x_assum `!tvs vs before after ftv copy_count dst_off names. _`
    (qspecl_then [`tvs`, `vs`, `before`, `after`, `ftv`, `copy_count`, `dst_off`, `names`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[log_args_avoid_def]]) >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed saved Log argument list frames: " ^ name)
  end) (DB.thms "typedLogArgsFrames")
