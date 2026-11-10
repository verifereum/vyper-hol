structure exprSimAbiEncodeArgsProbeLib =
struct
open HolKernel Parse boolLib bossLib

fun probe_eval_target g =
  CONV_TAC (RAND_CONV (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) g
fun probe_eval_source g =
  CONV_TAC (RATOR_CONV (computeLib.CBV_CONV
    (wordsLib.add_words_compset true (computeLib.copy (computeLib.the_compset()))))) g
fun probe_fetch g =
  (simp[fragGasPathTheory.gas_path_edge_def] >> qexists_tac `0` >>
   CONV_TAC (BINDER_CONV (BINDER_CONV (LAND_CONV (RAND_CONV EVAL)))) >>
   simp[venomInstTheory.get_instruction_def]) g
fun probe_step g = (EVAL_TAC >> simp[]) g
fun probe_jump g =
  (disj2_tac >>
   CONV_TAC (RAND_CONV (REWR_CONV (GSYM boolTheory.ETA_THM))) >> simp[]) g
end
