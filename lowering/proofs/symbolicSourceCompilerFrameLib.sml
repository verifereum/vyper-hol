structure symbolicSourceCompilerFrameLib =
struct
open HolKernel boolLib bossLib
open compileEnvTheory symbolicSourceCompilerFrameTheory

fun frame_tac goal =
  (simp[comp_ignore_bind_def] >>
   rpt (match_mp_tac symbolic_frame_bind >> conj_tac
     >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) goal
end
