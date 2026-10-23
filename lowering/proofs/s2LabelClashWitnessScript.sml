(* Witness that S2 (lower_vyper_runtime_unit_source_unit_ok) is false as
   stated.  An internal function named "fn_foo" next to an external "foo"
   gives both entry labels "fn_foo"; package_internal_blocks then splits at
   the external entry block, so the internal function ends in STOP.  The
   program is supported, so only the internal_name_ok premise of
   lower_vyper_runtime_unit_source_unit_ok_names excludes it.
   TOP-LEVEL: lower_vyper_runtime_unit_label_clash *)
Theory s2LabelClashWitness
Ancestors
  evalCompiler unitShapeDefs compileVyper supportedProgram
  alist byte integer_word option
Libs finite_mapLib computeLib wordsLib supportedEvalLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [fmap_to_alist_FEMPTY, i2w_pos])
val () = supportedEvalLib.configure ()

(* @internal def fn_foo(): pass   @external def foo(): pass *)
val clash_program =
  ``[FunctionDecl Internal Nonpayable F F "fn_foo"
       ([] : (string # type) list) ([] : expr list) NoneT [Pass];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) NoneT [Pass]]``

val rpolicy = optionSyntax.dest_some (rhs (concl
  (EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)))
val supported_th = EVAL ``supported_program ^clash_program``
val lower_th = EVAL ``lower_vyper_runtime_unit ^clash_program ^rpolicy``
val clash_unit = optionSyntax.dest_some (rhs (concl lower_th))

Theorem lower_vyper_runtime_unit_label_clash:
  ?tops rpolicy unit.
    supported_program tops /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    ~o1_source_unit_ok unit
Proof
  qexistsl_tac [`^clash_program`, `^rpolicy`, `^clash_unit`] >>
  rewrite_tac [supported_th, lower_th, o1_source_unit_ok_def,
               internal_termination_ok_def] >>
  strip_tac >>
  first_x_assum (qspec_then `EL 1 (^clash_unit).cu_context.ctx_functions`
    mp_tac) >>
  EVAL_TAC
QED
