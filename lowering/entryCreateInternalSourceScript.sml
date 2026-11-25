Theory entryCreateInternalSource
Ancestors
  compileVyper compileEnv loweringShapeProps supportedProgram constSubst
  venomInst list pair combin

(* Invert only an actual occurrence: either filter can only retain a member
   of its input, independently of whether a given source tuple is retained. *)
Theorem ordered_internal_source_inclusion[local]:
  MEM chosen (order_internals keys ints) ==> MEM chosen ints
Proof
  simp_tac bool_ss [order_internals_def, MEM_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[MEM_FILTER]
QED

Theorem distinct_source_key_inj[local]:
  !xs k x y. ALL_DISTINCT (MAP k xs) /\ MEM x xs /\ MEM y xs /\
    k x = k y ==> x = y
Proof
  Induct >> simp[MEM_MAP] >> metis_tac[]
QED

Theorem selected_internal_source_from_inclusion[local]:
  supported_program tops /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) ctor)
    fns = SOME callee /\
  MAP (\f. f.fn_name) fns =
    entry :: MAP FST (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn tops T (K global_nonreentrant_slot) ctor cap) srcs)) /\
  internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) ctor <> entry /\
  (!y. MEM y srcs ==> MEM y (FST (SND (classify_functions tops)))) ==>
  MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,fname,args,dflts,ret,ss)) srcs
Proof
  strip_tac >>
  qabbrev_tac `classified = FST (SND (classify_functions tops))` >>
  qabbrev_tac `key : (function_mutability # bool # bool # string #
      (string # type) list # expr list # type # stmt list) -> string =
    FST o source_internal_fn_descriptor tops ctor` >>
  qabbrev_tac `source = subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,fname,args,dflts,ret,ss)` >>
  `MEM source classified` by
    (simp[Abbr `source`, Abbr `classified`, subst_consts_fn_def, MEM_classify_internal] >>
     qexistsl_tac [`dflts`, `ss`] >> simp[]) >>
  `ALL_DISTINCT (MAP key classified)` by
    (drule supported_program_internal_names >>
     disch_then (mp_tac o MATCH_MP classified_internal_names_distinct) >>
     disch_then (mp_tac o MATCH_MP internal_descriptors_ok) >>
     simp[Abbr `key`, Abbr `classified`, MAP_MAP_o]) >>
  `MAP (\f. f.fn_name) fns = entry :: MAP key srcs` by
    (simp[Abbr `key`, GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
          internal_fn_descriptors_MAP_package_internal_fn]) >>
  `key source = internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) ctor` by
    simp[Abbr `key`, Abbr `source`, subst_consts_fn_def] >>
  `MEM (key source) (MAP key srcs)` by
    (drule venomInstTheory.lookup_function_mem >>
     qpat_assum `MAP _ fns = entry :: MAP key srcs` (fn th =>
       simp_tac bool_ss [th, MEM]) >>
     metis_tac[]) >>
  qpat_x_assum `MEM (key source) (MAP key srcs)`
    (qx_choose_then `chosen` strip_assume_tac o REWRITE_RULE [MEM_MAP]) >>
  `MEM chosen classified` by metis_tac[] >>
  `chosen = source` by metis_tac[distinct_source_key_inj] >>
  qpat_x_assum `chosen = source` SUBST_ALL_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem selected_ordered_internal_source:
  srcs = order_internals keys (FST (SND (classify_functions tops))) /\
  supported_program tops /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) ctor)
    fns = SOME callee /\
  MAP (\f. f.fn_name) fns =
    entry :: MAP FST (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn tops T (K global_nonreentrant_slot) ctor cap) srcs)) /\
  internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) ctor <> entry ==>
  MEM (subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,fname,args,dflts,ret,ss)) srcs
Proof
  strip_tac >>
  `!y. MEM y srcs ==> MEM y (FST (SND (classify_functions tops)))` by
    (asm_rewrite_tac[] >> metis_tac[ordered_internal_source_inclusion]) >>
  drule_all selected_internal_source_from_inclusion >>
  disch_then ACCEPT_TAC
QED
