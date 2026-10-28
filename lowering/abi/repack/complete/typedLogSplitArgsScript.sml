(* TOP-LEVEL: selecting actual non-indexed arguments preserves saved source
   values, separation from the data buffer and generated-name freshness. *)
Theory typedLogSplitArgs
Ancestors
  typedLogArgs eventLogSplitProps list pair

Theorem log_args_rel_select:
  !flags ops tvs vs ss wanted.
    LENGTH flags = LENGTH ops /\ log_args_rel ops tvs vs ss ==>
    log_args_rel (select_log_args wanted flags ops) (select_log_args wanted flags tvs)
      (select_log_args wanted flags vs) ss
Proof
  Induct_on `flags`
  >- (Cases >> Cases >> Cases >> simp[select_log_args_def, log_args_rel_def]) >>
  rpt gen_tac >> Cases_on `ops` >- simp[] >>
  rename1 `log_args_rel (arg::ops) _ _ _` >> Cases_on `arg` >>
  Cases_on `tvs` >> Cases_on `vs` >>
  simp_tac (srw_ss()) [log_args_rel_def] >> strip_tac >>
  rename1 `select_log_args wanted (flag::flags) _` >>
  Cases_on `flag = wanted` >> simp[select_log_args_def, log_args_rel_def] >>
  first_x_assum irule >> simp[]
QED

Theorem log_args_safe_select:
  !flags ops tvs ss dst_off byte_count wanted.
    LENGTH flags = LENGTH ops /\ log_args_safe ops tvs ss dst_off byte_count ==>
    log_args_safe (select_log_args wanted flags ops) (select_log_args wanted flags tvs)
      ss dst_off byte_count
Proof
  Induct_on `flags`
  >- (Cases >> Cases >> simp[select_log_args_def, log_args_safe_def]) >>
  rpt gen_tac >> Cases_on `ops` >- simp[] >>
  rename1 `log_args_safe (arg::ops) _ _ _ _` >> Cases_on `arg` >>
  Cases_on `tvs` >- simp[log_args_safe_def] >>
  simp_tac (srw_ss()) [log_args_safe_def] >> strip_tac >>
  rename1 `select_log_args wanted (flag::flags) _` >>
  Cases_on `flag = wanted` >> simp[select_log_args_def, log_args_safe_def] >>
  first_x_assum irule >> simp[]
QED

Theorem EVERY_select_log_args:
  !flags xs P wanted. EVERY P xs ==> EVERY P (select_log_args wanted flags xs)
Proof
  Induct_on `flags` >- (Cases >> simp[select_log_args_def]) >>
  MAP_EVERY qx_gen_tac [`flag`, `xs`, `P`, `wanted`] >> Cases_on `xs` >>
  Cases_on `flag = wanted` >> simp[select_log_args_def]
QED

Theorem log_args_avoid_select:
  !flags ops names wanted.
    log_args_avoid ops names ==> log_args_avoid (select_log_args wanted flags ops) names
Proof
  simp_tac bool_ss [log_args_avoid_def] >> rpt strip_tac >>
  irule EVERY_select_log_args >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed saved split Log arguments: " ^ name)
  end) (DB.thms "typedLogSplitArgs")
