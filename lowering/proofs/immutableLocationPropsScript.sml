(* Immutable lookups in the actual function environment originate in a
   declaration. Argument/local allocation may shadow a key, but cannot
   manufacture an ImmutableLoc. No name-freshness premise is needed. *)
Theory immutableLocationProps
Ancestors
  immutableSectionRel immutableRelation compileVyper compileEnv context finite_map list arithmetic

Theorem immutable_allocate_args_origin:
  !args off vars vars' off' key loc.
  allocate_args sft args off vars = (vars',off') /\
  FLOOKUP vars' key = SOME (ImmutableLoc loc) ==>
  FLOOKUP vars key = SOME (ImmutableLoc loc)
Proof
  Induct >> simp[allocate_args_def] >> rpt gen_tac >>
  PairCases_on `h` >> simp[allocate_args_def] >>
  strip_tac >> first_x_assum drule_all >> simp[FLOOKUP_UPDATE] >> rw[]
QED

Theorem immutable_module_vars_origin:
  !tops vars key loc.
  FLOOKUP (add_module_var_locations tops vars) key = SOME (ImmutableLoc loc) ==>
  FLOOKUP vars key = SOME (ImmutableLoc loc)
Proof
  Induct >> simp[add_module_var_locations_def] >> rpt gen_tac >>
  Cases_on `h` >> simp[add_module_var_locations_def] >>
  rpt CASE_TAC >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[FLOOKUP_UPDATE] >> rw[]
QED

Theorem immutable_locations_cons:
  add_immutable_locations sft (top::tops) off vars =
  add_immutable_locations sft tops (off + compute_immutables_len sft [top])
    (case top of VariableDecl _ Immutable name ty _ =>
       vars |+ (module_var_key (NONE,name), ImmutableLoc off) | _ => vars)
Proof
  Cases_on `top` >> simp[add_immutable_locations_def, compute_immutables_len_def] >>
  CASE_TAC >> simp[add_immutable_locations_def, compute_immutables_len_def]
QED

Theorem immutable_locations_step_origin:
  FLOOKUP (case top of VariableDecl _ Immutable name ty _ =>
     vars |+ (module_var_key (NONE,name), ImmutableLoc off) | _ => vars) key =
    SOME (ImmutableLoc loc) ==>
  FLOOKUP vars key = SOME (ImmutableLoc loc) \/
  ?vis name ty slot. top = VariableDecl vis Immutable name ty slot /\
    key = module_var_key (NONE,name) /\ loc = off
Proof
  Cases_on `top` >> simp[] >> CASE_TAC >> simp[FLOOKUP_UPDATE] >>
  rw[] >> metis_tac[]
QED

Theorem immutable_len_cons:
  compute_immutables_len sft (top::tops) =
    compute_immutables_len sft [top] + compute_immutables_len sft tops
Proof
  mp_tac (Q.SPECL [`[top]`, `tops`] compute_immutables_len_append) >> simp[]
QED

Theorem immutable_locations_origin:
  !tops off vars key loc.
  FLOOKUP (add_immutable_locations sft tops off vars) key = SOME (ImmutableLoc loc) ==>
  FLOOKUP vars key = SOME (ImmutableLoc loc) \/
  ?pre post vis name ty slot.
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    key = module_var_key (NONE,name) /\
    loc = off + compute_immutables_len sft pre
Proof
  Induct >- simp[add_immutable_locations_def] >>
  rpt gen_tac >> simp[immutable_locations_cons] >>
  strip_tac >> first_x_assum drule >> strip_tac
  >- (drule immutable_locations_step_origin >> strip_tac
      >- simp[] >>
      disj2_tac >> qexistsl [`[]`,`tops`] >>
      simp[compute_immutables_len_def] >> metis_tac[]) >>
  disj2_tac >> qexistsl [`h::pre`,`post`] >>
  qexistsl [`vis`,`name`,`ty`,`slot`] >>
  ONCE_REWRITE_TAC [immutable_len_cons] >>
  asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND, ADD_ASSOC]
QED

Theorem immutable_build_compile_env_layout:
  !tops vis mut name args ret body locks.
  immutable_section_layout
    (build_compile_env tops vis mut name args ret body locks) tops
Proof
  rpt gen_tac >> simp[immutable_section_layout_def] >> rpt gen_tac >>
  simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all immutable_allocate_args_origin >> strip_tac >>
  qpat_x_assum `allocate_args _ (collect_locals _) _ _ = _` kall_tac >>
  drule_all immutable_allocate_args_origin >> strip_tac >>
  drule immutable_locations_origin >> strip_tac
  >- (drule immutable_module_vars_origin >> simp[FLOOKUP_DEF]) >>
  gvs[module_var_key_def, nsid_to_string_def] >>
  qmatch_goalsub_rename_tac `VariableDecl decl_vis Immutable _ decl_ty decl_slot` >>
  qexistsl [`pre`,`post`,`decl_vis`,`decl_ty`,`decl_slot`] >> simp[]
QED

Theorem immutable_function_runtime_relation:
  !tops vis mut name args ret body locks addr vs ss.
  immutables_section_rel tops
    (case ALOOKUP vs.immutables addr of
       NONE => empty_immutables | SOME imms => imms) ss.vs_data_section ==>
  immutables_rel (build_compile_env tops vis mut name args ret body locks)
    addr NONE F vs ss
Proof
  rpt strip_tac >> irule immutables_section_rel_runtime_fallback >>
  qexistsl [`ss.vs_data_section`,`tops`] >>
  simp[immutable_build_compile_env_layout]
QED

val _ = List.app (fn (name, th) => let
  val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Unclosed immutable environment origin: " ^ name)
  end) (DB.thms "immutableLocationProps");
