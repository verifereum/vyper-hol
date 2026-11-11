(* Control and frame interfaces for changing only FMP fields. *)
Theory ctxFmpControlHelpers
Ancestors
  ctxFmpUpdateHelpers contextCodegenRel venomExecSemantics instIdxIndep
Libs
  listTheory

Theorem setup_callee_fmp_update:
  setup_callee fn args
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
  OPTION_MAP (\t. t with
    <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
    (setup_callee fn args s)
Proof
  Cases_on `NULL fn.fn_blocks` >> simp[setup_callee_def]
QED

Theorem merge_callee_state_fmp_update:
  merge_callee_state
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>)
    (t with <|vs_fmp := q; vs_initial_fmp := j; vs_call_entry_fmp := d|>) =
  (merge_callee_state s t) with
    <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>
Proof
  simp[merge_callee_state_def]
QED

Theorem adopt_return_fmp_shift:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> ==>
  adopt_return_fmp ir s' = (adopt_return_fmp ir s) with
    <|vs_fmp := (adopt_return_fmp ir s').vs_fmp;
      vs_initial_fmp := (adopt_return_fmp ir s').vs_initial_fmp;
      vs_call_entry_fmp := (adopt_return_fmp ir s').vs_call_entry_fmp|>
Proof
  strip_tac >> Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def] >>
  once_asm_rewrite_tac[] >> simp[]
QED

Theorem bind_outputs_fmp_update:
  bind_outputs outs vals
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) =
  OPTION_MAP (\t. t with
    <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>)
    (bind_outputs outs vals s)
Proof
  Cases_on `LENGTH outs = LENGTH vals` >>
  simp[bind_outputs_def, foldl_update_var_fmp_update]
QED

Theorem eval_one_phi_fmp_update:
  eval_one_phi
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) inst =
  eval_one_phi s inst
Proof
  simp[eval_one_phi_def, eval_operand_fmp_update]
QED

Theorem eval_phis_fmp_update:
  !insts s p i c.
  eval_phis
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) insts =
  exec_result_map (\t. t with
    <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>)
    (eval_phis s insts)
Proof
  Induct >> simp[eval_phis_def, eval_one_phi_fmp_update,
                 exec_result_map_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[exec_result_map_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s insts` >>
  simp[exec_result_map_def, SRULE [] update_var_fmp_update]
QED

Theorem active_inst_fmp_update:
  active_inst fn inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>) <=>
  active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem enters_block_fmp_update:
  enters_block fn s t ==>
  enters_block fn
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>)
    (t with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>)
Proof
  rw[enters_block_def] >> qexistsl [`bb`,
    `s_phi with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := c|>`] >>
  simp[SRULE [] eval_phis_fmp_update, exec_result_map_def]
QED

(* Option elimination interfaces keep frame internals out of consumers. *)
Theorem setup_callee_fmp_none:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> ==>
  (setup_callee fn args s' = NONE <=> setup_callee fn args s = NONE)
Proof
  strip_tac >> once_asm_rewrite_tac[] >>
  simp[setup_callee_fmp_update]
QED

Theorem setup_callee_fmp_some:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> /\
  setup_callee fn args s = SOME t ==>
  ?t'. setup_callee fn args s' = SOME t' /\
       t' = t with <|vs_fmp := t'.vs_fmp; vs_initial_fmp := t'.vs_initial_fmp;
                    vs_call_entry_fmp := t'.vs_call_entry_fmp|>
Proof
  strip_tac >>
  qexists `t with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
                   vs_call_entry_fmp := s'.vs_fmp|>` >>
  conj_tac >- (once_asm_rewrite_tac[] >> simp[setup_callee_fmp_update]) >>
  simp[]
QED

Theorem merge_callee_state_fmp_shift:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> /\
  t' = t with <|vs_fmp := t'.vs_fmp; vs_initial_fmp := t'.vs_initial_fmp;
               vs_call_entry_fmp := t'.vs_call_entry_fmp|> ==>
  merge_callee_state s' t' = (merge_callee_state s t) with
    <|vs_fmp := (merge_callee_state s' t').vs_fmp;
      vs_initial_fmp := (merge_callee_state s' t').vs_initial_fmp;
      vs_call_entry_fmp := (merge_callee_state s' t').vs_call_entry_fmp|>
Proof
  strip_tac >> once_asm_rewrite_tac[] >>
  simp[merge_callee_state_fmp_update, merge_callee_state_def]
QED

Theorem bind_outputs_fmp_none:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> ==>
  (bind_outputs outs vals s' = NONE <=> bind_outputs outs vals s = NONE)
Proof
  strip_tac >> once_asm_rewrite_tac[] >> simp[bind_outputs_fmp_update]
QED

Theorem bind_outputs_fmp_some:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> /\
  bind_outputs outs vals s = SOME t ==>
  ?t'. bind_outputs outs vals s' = SOME t' /\
       t' = t with <|vs_fmp := t'.vs_fmp; vs_initial_fmp := t'.vs_initial_fmp;
                    vs_call_entry_fmp := t'.vs_call_entry_fmp|>
Proof
  strip_tac >>
  qexists `t with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
                   vs_call_entry_fmp := s'.vs_call_entry_fmp|>` >>
  conj_tac >- (once_asm_rewrite_tac[] >> simp[bind_outputs_fmp_update]) >>
  simp[]
QED

(* Entry setup and sequential continuation update only control fields. *)
Theorem control_fields_fmp_shift:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> ==>
  (s' with <|vs_prev_bb := prev; vs_current_bb := lbl; vs_inst_idx := idx|>) =
  (s with <|vs_prev_bb := prev; vs_current_bb := lbl; vs_inst_idx := idx|>) with
    <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
      vs_call_entry_fmp := s'.vs_call_entry_fmp|>
Proof
  strip_tac >> once_asm_rewrite_tac[] >> simp[]
QED

Theorem inst_idx_fmp_shift:
  s' = s with <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
               vs_call_entry_fmp := s'.vs_call_entry_fmp|> ==>
  (s' with vs_inst_idx := idx) = (s with vs_inst_idx := idx) with
    <|vs_fmp := s'.vs_fmp; vs_initial_fmp := s'.vs_initial_fmp;
      vs_call_entry_fmp := s'.vs_call_entry_fmp|>
Proof
  strip_tac >> once_asm_rewrite_tac[] >> simp[]
QED
