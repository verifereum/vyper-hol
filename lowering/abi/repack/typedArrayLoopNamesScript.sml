(* TOP-LEVEL: syntactic operand-lifetime facts for replayed loop code.
   Protected names can be restricted to a child range; names reserved
   before that range remain protected without assuming undefined outputs. *)
Theory typedArrayLoopNames
Ancestors
  abiBytestringCode abiStaticLoopCode compileEnv venomInst list arithmetic

Theorem compiler_var_names_avoid:
  !arg_op var_base num_names.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base num_names) <=>
    !j. j < num_names ==> arg_op <> Var (compiler_var_name var_base j)
Proof
  simp[compiler_var_names_def, compiler_var_name_def, EVERY_GENLIST]
QED

Theorem compiler_var_names_avoid_index:
  !arg_op var_base num_names j.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base num_names) /\ j < num_names ==>
    arg_op <> Var (compiler_var_name var_base j)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_var_names_avoid] >> strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem compiler_var_names_avoid_segment:
  !arg_op var_base total offset num_names.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base total) /\
    offset + num_names <= total ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + offset) num_names)
Proof
  rpt gen_tac >> simp_tac bool_ss [compiler_var_names_avoid] >> strip_tac >>
  qx_gen_tac `j` >> DISCH_TAC >> rewrite_tac[compiler_var_name_add] >>
  first_x_assum irule >> decide_tac
QED

Theorem compiler_var_names_avoid_prefix:
  !arg_op var_base total_count num_names.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base total_count) /\
    num_names <= total_count ==>
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base num_names)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `total_count`, `0`, `num_names`]
    compiler_var_names_avoid_segment) >> simp[]
QED

Theorem compiler_var_names_avoid_indices:
  !arg_op var_base num_names indices.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base num_names) /\
    EVERY (\j. j < num_names) indices ==>
    EVERY (\j. arg_op <> Var (compiler_var_name var_base j)) indices
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[EVERY_MEM] >>
  qx_gen_tac `j` >> DISCH_TAC >>
  `j < num_names` by fs[EVERY_MEM] >>
  drule_all compiler_var_names_avoid_index >> simp[]
QED

Theorem compiler_var_names_before:
  !var_base offset num_names j.
    j < offset ==>
    EVERY (\name. Var (compiler_var_name var_base j) <> Var name)
      (compiler_var_names (var_base + offset) num_names)
Proof
  rpt gen_tac >> DISCH_TAC >> rewrite_tac[compiler_var_names_avoid] >>
  simp[compiler_var_name_add] >> rpt strip_tac >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed generated-name lifetime theorem: " ^ name)
  end) (DB.thms "typedArrayLoopNames")
