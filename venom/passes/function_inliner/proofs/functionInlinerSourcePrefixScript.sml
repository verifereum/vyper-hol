(* Successful source evaluation supplies the parameter trace, including its residual. *)
Theory functionInlinerSourcePrefix
Ancestors
  functionInlinerEntryHandoff callLayoutDefs venomExecSemantics venomInstProps
  venomInst list arithmetic

Theorem inline_source_parameter_trace:
  !n bb s fuel C res.
    n <= LENGTH bb.bb_instructions /\ s.vs_inst_idx = 0 /\
    (!k. k < n ==> is_param_opcode (EL k bb.bb_instructions).inst_opcode) /\
    exec_block fuel C bb s = res /\ (!e. res <> Error e) ==>
    ?ss. ss 0 = s /\
      (!k. k < n ==> ?t.
        step_inst fuel C (EL k bb.bb_instructions) (ss k) = OK t /\
        ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) /\
      (ss n).vs_inst_idx = n /\ exec_block fuel C bb (ss n) = res
Proof
  Induct >- (rpt strip_tac >> qexists_tac `\k. s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?ss. ss 0 = s /\
      (!k. k < n ==> ?t.
        step_inst fuel C (EL k bb.bb_instructions) (ss k) = OK t /\
        ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) /\
      (ss n).vs_inst_idx = n /\ exec_block fuel C bb (ss n) = res` by
    (first_x_assum irule >> simp[] >> metis_tac[LESS_TRANS, LESS_OR_EQ]) >>
  `n < LENGTH bb.bb_instructions /\
   is_param_opcode (EL n bb.bb_instructions).inst_opcode` by simp[] >>
  `~is_terminator (EL n bb.bb_instructions).inst_opcode` by
    (Cases_on `(EL n bb.bb_instructions).inst_opcode` >>
     gvs[is_param_opcode_def, is_terminator_def]) >>
  qspecl_then [`EL n bb.bb_instructions`,`fuel`,`C`,`ss n`]
    mp_tac step_inst_param_ok_or_error >> simp[] >> strip_tac
  >- (rename1 `step_inst fuel C (EL n bb.bb_instructions) (ss n) = OK mid` >>
      qpat_x_assum `exec_block _ _ _ (ss n) = _` mp_tac >>
      simp[Once exec_block_def, get_instruction_def] >> strip_tac >>
      qexists_tac `\k. if k = SUC n then mid with vs_inst_idx := SUC n else ss k` >>
      simp[] >> rpt strip_tac >> Cases_on `k = n` >> gvs[] >>
      first_x_assum irule >> decide_tac) >>
  qpat_x_assum `exec_block _ _ _ (ss n) = _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >> metis_tac[]
QED

Theorem inline_source_parameter_prefix:
  bb.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  s.vs_inst_idx = 0 /\ exec_block fuel C bb s = res /\
  (!e. res <> Error e) ==>
  ?ss. ss 0 = s /\
    (!k. k < LENGTH params ==> ?t.
      step_inst fuel C (EL k params) (ss k) = OK t /\
      ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    exec_block fuel C bb (ss (LENGTH params)) = res
Proof
  strip_tac >>
  qspec_then `LENGTH params` mp_tac inline_source_parameter_trace >>
  disch_then (qspecl_then [`bb`,`s`,`fuel`,`C`,`res`] mp_tac) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >> simp[EL_APPEND_EQN] >>
      drule_all param_insts_from_el >> simp[param_inst_at_def]) >>
  simp[EL_APPEND_EQN]
QED

(* The initial selected child has no predecessor; successful PHIs therefore
   leave exactly the original child entry state for the parameter trace. *)
Theorem inline_source_entry_parameter_prefix:
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  source.vs_prev_bb = NONE /\ source.vs_inst_idx = 0 /\
  eval_phis source entry.bb_instructions = OK post /\
  exec_block fuel C entry
    (post with vs_inst_idx := phi_prefix_length entry.bb_instructions) = res /\
  (!e. res <> Error e) ==>
  phi_prefix_length entry.bb_instructions = 0 /\ post = source /\
  ?ss. ss 0 = source /\
    (!k. k < LENGTH params ==> ?t.
      step_inst fuel C (EL k params) (ss k) = OK t /\
      ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    exec_block fuel C entry (ss (LENGTH params)) = res
Proof
  strip_tac >>
  `phi_prefix_length entry.bb_instructions = 0` by
    metis_tac[algebraicOptMainEntryProofsTheory.ao_eval_phis_initial_prefix] >>
  `post = source` by
    metis_tac[analysisSimProofsBaseTheory.phi_prefix_length_zero_eval_phis_ok,
              exec_result_11] >>
  gvs[] >> irule inline_source_parameter_prefix >> metis_tac[]
QED
