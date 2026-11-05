Theory extRetCopyCountedPtr
Ancestors
  fragGasPathPtr fragGasSeqPtr fragExec ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState arithmetic

(* Zero-count fragments with explicit normal and exceptional endpoints.
   Concrete clients put their entry/end cursors in P and Q. *)
Definition copy_path_ptr_def:
  copy_path_ptr D lo ctx fn PG P Q R <=>
    !G tn s. P G tn s ==>
      ?G' tn' r. gas_path_ptr D lo ctx fn PG G tn s 0 G' tn' r /\
        ((?t. r = OK t /\ ~t.vs_halted /\ Q G' tn' t) \/
         (exit_result r /\ R (G',tn') r))
End

Theorem copy_path_ptr_refl:
  (!G tn s. P G tn s ==> ~s.vs_halted) ==>
  copy_path_ptr D lo ctx fn PG P P R
Proof
  rw[copy_path_ptr_def] >> qexistsl_tac [`G`, `tn`, `OK s`] >>
  `~s.vs_halted` by metis_tac[] >>
  simp[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem copy_path_ptr_then:
  !P Q S R. copy_path_ptr D lo ctx fn PG P Q R /\
  copy_path_ptr D lo ctx fn PG Q S R ==>
  copy_path_ptr D lo ctx fn PG P S R
Proof
  simp[copy_path_ptr_def] >> rpt strip_tac >>
  qpat_x_assum `!G tn s. P G tn s ==> _` drule >>
  strip_tac
  >- (qpat_x_assum `!G tn s. Q G tn s ==> _` drule >>
      strip_tac >> gvs[] >>
      metis_tac[gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []])
  >> metis_tac[]
QED

Theorem copy_path_ptr_iterate:
  !count H.
    (!i. i < count ==>
      copy_path_ptr D lo ctx fn PG (H i) (H (SUC i)) R) /\
    (!i G tn s. i <= count /\ H i G tn s ==> ~s.vs_halted) ==>
    !i. i <= count ==> copy_path_ptr D lo ctx fn PG (H i) (H count) R
Proof
  Induct >> rpt strip_tac
  >- (gvs[] >> irule copy_path_ptr_refl >> metis_tac[]) >>
  rename1 `i <= SUC limit` >>
  Cases_on `i = SUC limit`
  >- (gvs[] >> irule copy_path_ptr_refl >> metis_tac[LESS_EQ_REFL]) >>
  `i <= limit` by decide_tac >>
  irule copy_path_ptr_then >> qexists_tac `H limit` >> conj_tac
  >- (first_x_assum irule >> simp[] >>
      `!j. j <= limit ==> j <= SUC limit` by decide_tac >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

(* The direct-jump alternative in the counted relation needs no PHI premise. *)
Theorem jump_gas_path_ptr:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> GAS /\
  step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
  ptr_inst_ok D lo 0 ctx fn G tn inst s ==>
  gas_path_ptr D lo ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (simp[gas_path_ptr_edge_def] >>
     qexists_tac `0` >>
     simp[step_inst_non_invoke, gasCountTheory.gas_count_step_def,
          ptr_safe_step_def] >> metis_tac[]) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[jump_to_def]
QED
