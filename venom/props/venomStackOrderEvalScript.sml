(* Exact block-analysis composition with opaque CFG and liveness inputs. *)
Theory venomStackOrderEval
Ancestors stackOrderInternalDefs list pair

Theorem so_analyze_block_result:
  !cfg lr from_to lbl insts final.
    FOLDL (so_step cfg lr from_to lbl)
      <| sobs_stack := []; sobs_needed := []; sobs_idx := 0 |> insts = final ==>
    so_analyze_block cfg lr from_to lbl insts =
      (final.sobs_needed,final.sobs_stack)
Proof
  rpt gen_tac >> strip_tac >> simp[so_analyze_block_def]
QED
