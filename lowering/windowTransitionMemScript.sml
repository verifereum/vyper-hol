(* Same-witness semantic and memory continuation composition. *)
Theory windowTransitionMem
Ancestors
  abiEncoderWindowArrayBody abiEncoderWindowArrayInvariant
  abiEncoderWindowPhase memContinuation fragGasPathMem arithmetic

Theorem window_phase_chain_mem:
  window_phase ctx func st mid left left_out s t /\ mem_cont_sim ctx func s t /\
  window_phase ctx func mid en right right_out t u /\ mem_cont_sim ctx func t u /\
  st.cs_next_var <= mid.cs_next_var /\ left SUBSET ids /\ right SUBSET ids /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) left_out) /\
  (!a. EVERY (\(b,n). a < b \/ b+n <= a) outs ==>
    EVERY (\(b,n). a < b \/ b+n <= a) right_out) ==>
  window_phase ctx func st en ids outs s u /\ mem_cont_sim ctx func s u
Proof
  strip_tac >> conj_tac
  >- (drule_all window_phase_chain >> simp[]) >>
  metis_tac[mem_cont_sim_trans]
QED

Theorem window_array_transition_refl_mem:
  alloca_inv s /\ alloca_room ctx func s /\ ~s.vs_halted ==>
  window_array_transition ctx func owner ids outs s s /\ mem_cont_sim ctx func s s
Proof
  simp[window_array_transition_refl, mem_cont_sim_refl]
QED

Theorem window_array_transition_trans_mem:
  window_array_transition ctx func owner ids outs s t /\ mem_cont_sim ctx func s t /\
  window_array_transition ctx func owner ids outs t u /\ mem_cont_sim ctx func t u ==>
  window_array_transition ctx func owner ids outs s u /\ mem_cont_sim ctx func s u
Proof
  metis_tac[window_array_transition_trans, mem_cont_sim_trans]
QED

Theorem window_array_phase_transition_mem:
  window_phase ctx func owner en ids outs s t /\ mem_cont_sim ctx func s t /\
  (!R. window_sizes32 R s ==> window_sizes32 R t) ==>
  window_array_transition ctx func owner ids outs s t /\ mem_cont_sim ctx func s t
Proof
  metis_tac[window_array_phase_transition]
QED

Theorem window_array_pure_phase_transition_mem:
  window_phase ctx func owner en {} [] s t /\ mem_cont_sim ctx func s t ==>
  window_array_transition ctx func owner {} [] s t /\ mem_cont_sim ctx func s t
Proof
  metis_tac[window_array_pure_phase_transition]
QED

Theorem window_array_transition_phase_mem:
  window_array_transition ctx func owner ids outs s t /\ mem_cont_sim ctx func s t /\
  t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts ==>
  window_phase ctx func owner en ids outs s t /\ mem_cont_sim ctx func s t
Proof
  metis_tac[window_array_transition_phase]
QED

Theorem window_array_loop_finite_mem:
  !n j s.
    j+n = N /\ P j s /\
    (!k u. k < N /\ P k u ==>
      ?v. window_array_transition ctx func owner ids outs u v /\
        mem_cont_sim ctx func u v /\ P (SUC k) v) /\
    (!u. P N u ==>
      ?v. window_array_transition ctx func owner ids outs u v /\
        mem_cont_sim ctx func u v /\ Q v) ==>
    ?t. window_array_transition ctx func owner ids outs s t /\
      mem_cont_sim ctx func s t /\ Q t
Proof
  Induct
  >- (rpt gen_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < N` by decide_tac >>
  `?v. window_array_transition ctx func owner ids outs s v /\
    mem_cont_sim ctx func s v /\ P (SUC j) v` by metis_tac[] >>
  `SUC j+n = N` by decide_tac >>
  `?t. window_array_transition ctx func owner ids outs v t /\
    mem_cont_sim ctx func v t /\ Q t` by metis_tac[] >>
  metis_tac[window_array_transition_trans_mem]
QED

Theorem window_array_loop_run_mem:
  j <= N /\ P j s /\
  (!k u. k < N /\ P k u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\
      mem_cont_sim ctx func u v /\ P (SUC k) v) /\
  (!u. P N u ==>
    ?v. window_array_transition ctx func owner ids outs u v /\
      mem_cont_sim ctx func u v /\ Q v) ==>
  ?t. window_array_transition ctx func owner ids outs s t /\
    mem_cont_sim ctx func s t /\ Q t
Proof
  strip_tac >> irule window_array_loop_finite_mem >>
  qexistsl_tac [`N`, `P`, `j`, `N-j`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem window_array_loop_finite_counted_mem:
  !steps j s.
    j+steps = N /\ P j s /\
    (!k u. k < N /\ P k u ==>
      ?v count. window_array_transition ctx func owner ids outs u v /\
        mem_cont_sim ctx func u v /\ gas_path_mem ctx func u count (OK v) /\
        P (SUC k) v) /\
    (!u. P N u ==>
      ?v count. window_array_transition ctx func owner ids outs u v /\
        mem_cont_sim ctx func u v /\ gas_path_mem ctx func u count (OK v) /\ Q v) ==>
    ?t count. window_array_transition ctx func owner ids outs s t /\
      mem_cont_sim ctx func s t /\ gas_path_mem ctx func s count (OK t) /\ Q t
Proof
  Induct >- (rpt gen_tac >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `j < N` by decide_tac >>
  `?v left. window_array_transition ctx func owner ids outs s v /\
    mem_cont_sim ctx func s v /\ gas_path_mem ctx func s left (OK v) /\
    P (SUC j) v` by metis_tac[] >>
  `SUC j+steps = N` by decide_tac >>
  `?t right. window_array_transition ctx func owner ids outs v t /\
    mem_cont_sim ctx func v t /\ gas_path_mem ctx func v right (OK t) /\ Q t` by
    (qpat_x_assum `!j s. j + steps = N /\ _ ==> _`
       (qspecl_then [`SUC j`,`v`] mp_tac) >> simp[]) >>
  `window_array_transition ctx func owner ids outs s t /\ mem_cont_sim ctx func s t` by
    (irule window_array_transition_trans_mem >> qexists_tac `v` >> simp[]) >>
  qexistsl_tac [`t`,`left+right`] >> simp[] >>
  irule gas_path_mem_then >> qexists_tac `v` >> simp[]
QED

Theorem window_array_loop_run_counted_mem:
  j <= N /\ P j s /\
  (!k u. k < N /\ P k u ==>
    ?v count. window_array_transition ctx func owner ids outs u v /\
      mem_cont_sim ctx func u v /\ gas_path_mem ctx func u count (OK v) /\
      P (SUC k) v) /\
  (!u. P N u ==>
    ?v count. window_array_transition ctx func owner ids outs u v /\
      mem_cont_sim ctx func u v /\ gas_path_mem ctx func u count (OK v) /\ Q v) ==>
  ?t count. window_array_transition ctx func owner ids outs s t /\
    mem_cont_sim ctx func s t /\ gas_path_mem ctx func s count (OK t) /\ Q t
Proof
  strip_tac >> irule window_array_loop_finite_counted_mem >>
  qexistsl_tac [`N`,`P`,`j`,`N-j`] >> asm_rewrite_tac[] >> decide_tac
QED
