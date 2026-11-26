(* Reflect the classified external's checked defaults back to source syntax. *)
structure groupedDefaultLoweringGuardLib =
struct
open HolKernel boolLib bossLib
open compileVyperTheory groupedDefaultHorizonTheory
open listTheory pairTheory

fun raw_defaults_no_sha_tac member =
  `EVERY external_defaults_no_sha256 externals` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`lower_vyper_runtime_unit tops _ = SOME _`,
        `classify_functions tops = (externals,_,_,_)`,
        `EXISTS external_has_defaults externals`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rw[] >>
     gvs[lower_vyper_runtime_unit_def,AllCaseEqs()]) >>
  qpat_assum member mp_tac >>
  qpat_assum `classify_functions tops = (externals,_,_,_)`
    (fn th => simp_tac bool_ss [th,FST]) >>
  qpat_assum `EVERY external_defaults_no_sha256 externals`
    (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  metis_tac[external_defaults_no_sha256_def,
            cj 3 source_no_sha256_after_const_substitution];
end
