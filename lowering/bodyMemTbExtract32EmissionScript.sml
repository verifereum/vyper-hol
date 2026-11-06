(* Chronological emission is not an execution trace or a block-local window. *)
Theory bodyMemTbExtract32Emission
Ancestors
  bodyMemTbExtract32Imports compileEnv venomInst list

Theorem extract32_emit_chronological:
  emit i sa = (u,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ [i]
Proof
  simp[emit_def] >> rpt strip_tac >> gvs[listTheory.APPEND_ASSOC]
QED

Theorem extract32_new_block_chronological:
  new_block label sa = (old,sb) ==>
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
  FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts
Proof
  simp[new_block_def] >> rpt strip_tac >> gvs[]
QED

(* Elimination/composition for independently obtained emitted suffixes. *)
Theorem extract32_chronological_delta_compose:
  (?d1. FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts =
        (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ d1 /\
        EVERY P d1) /\
  (?d2. FLAT (MAP (\b. b.bb_instructions) (REVERSE sc.cs_blocks)) ++ sc.cs_current_insts =
        (FLAT (MAP (\b. b.bb_instructions) (REVERSE sb.cs_blocks)) ++ sb.cs_current_insts) ++ d2 /\
        EVERY P d2) ==>
  ?delta. FLAT (MAP (\b. b.bb_instructions) (REVERSE sc.cs_blocks)) ++ sc.cs_current_insts =
          (FLAT (MAP (\b. b.bb_instructions) (REVERSE sa.cs_blocks)) ++ sa.cs_current_insts) ++ delta /\
          EVERY P delta
Proof
  rpt strip_tac >> qexists_tac `d1 ++ d2` >> simp[listTheory.APPEND_ASSOC]
QED
