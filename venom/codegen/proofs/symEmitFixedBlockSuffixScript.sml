(* Stack framing from a fixed block's successful-run equation. *)
Theory symEmitFixedBlockSuffix
Ancestors codegenSymRel asmSymSem list

Theorem sym_fixed_block_stack_suffix:
  !allow_own own.
  ss.sym_stack = input ++ stk /\
  (!rest. sym_steps_mode allow_own p env own n
      (ss with sym_stack := input ++ rest) =
    SymOK (ss with <| sym_base := next_base; sym_stack := output ++ rest |>)) /\
  sym_steps_mode allow_own p env own n ss = SymOK ss' ==>
  sym_steps_mode allow_own p env own n (ss with sym_stack := ss.sym_stack ++ tail) =
    SymOK (ss' with sym_stack := ss'.sym_stack ++ tail)
Proof
  rpt gen_tac >> strip_tac >>
  `ss with sym_stack := input ++ stk = ss` by simp[sym_state_component_equality] >>
  qpat_assum `!rest. _` (qspec_then `stk` assume_tac) >>
  `ss' = ss with <| sym_base := next_base; sym_stack := output ++ stk |>` by
    metis_tac[sym_result_11] >>
  qpat_x_assum `!rest. _` (qspec_then `stk ++ tail` mp_tac) >>
  simp[APPEND_ASSOC]
QED
