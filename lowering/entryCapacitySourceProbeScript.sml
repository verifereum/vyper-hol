Theory entryCapacitySourceProbe
Ancestors compileVyper allocLimitsProps entryNaturalCapacityProbe words
Libs wordsLib

(* Successful lowering, unlike the modular allocation budget, bounds the
   natural byte size recorded by every external parameter descriptor. *)
Theorem lowered_external_parameter_bytes:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts, ints, fb, ctor) /\
  MEM (mut, nr, rr, fname, fargs, dflts, ret, ss) exts /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  MEM (name, ty) fargs ==>
  type_memory_bytes cenv ty < 2 ** 64
Proof
  strip_tac >>
  `fn_allocs_ok tops (mut, nr, rr, fname, fargs, dflts, ret, ss)` by
    metis_tac[lower_vyper_runtime_unit_allocs_ok] >>
  drule_all fn_allocs_ok_body >>
  simp[listTheory.EVERY_MEM] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem lowered_external_parameter_nonwrap:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts, ints, fb, ctor) /\
  MEM (mut, nr, rr, fname, fargs, dflts, ret, ss) exts /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) /\
  MEM (name, ty) fargs ==>
  type_memory_bytes cenv ty < dimword (:256)
Proof
  strip_tac >> drule_all lowered_external_parameter_bytes >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC >> decide_tac
QED

Theorem natural_capacity_external_excluded:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  classify_functions tops = (exts, ints, fb, ctor) /\
  MEM (mut, nr, rr, fname, fargs, dflts, ret, ss) exts /\
  cenv.ce_struct_fields = make_struct_fields_map tops /\
  cenv.ce_event_info = build_event_info (type_env tops) tops (K NONE) ==>
  ~MEM (name, ArrayT (BaseT (UintT 256)) (Dynamic (2 ** 251 - 1))) fargs
Proof
  strip_tac >> strip_tac >>
  drule_all lowered_external_parameter_nonwrap >>
  simp[natural_capacity_compiler_bytes]
QED
