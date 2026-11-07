(* ABI-static fits excludes every bound-widening constructor. *)
Theory staticTypeFitsPtr
Ancestors vyperTypeSystem compileEnv list

Theorem static_arg_type_fits:
  (!src dst. arg_type_fits src dst ==>
    !sf : string |-> ('a # type # 'b) list. ~is_abi_dynamic sf dst ==> src = dst) /\
  (!ss ds. arg_types_fit ss ds ==>
    !sf : string |-> ('a # type # 'b) list. ~EXISTS (is_abi_dynamic sf) ds ==> ss = ds)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[arg_type_fits_def, is_abi_dynamic_def, combinTheory.o_DEF] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum irule >> qexists_tac `sf` >> simp[]
QED
