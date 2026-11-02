(* A finite run can be replayed with an arbitrary unused GAS suffix.
   The consumed prefix includes zero readings after oracle exhaustion. *)
Theory gasOracleReplay
Ancestors
  stateEquiv venomExecSemantics venomState list rich_list arithmetic

Definition gas_prefix_def:
  gas_prefix n (gs : (256 word) list) = TAKE n (gs ++ REPLICATE n 0w)
End

Definition gas_replay_at_def:
  gas_replay_at n f s <=> !tail.
    lift_result
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
             b = (a with vs_gas_readings := tail))
      (f s) (f (s with vs_gas_readings :=
                        gas_prefix n s.vs_gas_readings ++ tail))
End

Definition gas_replay_def:
  gas_replay f s <=> ?n. gas_replay_at n f s
End

Theorem gas_prefix_zero[simp]:
  gas_prefix 0 gs = []
Proof
  simp[gas_prefix_def]
QED

Theorem gas_take_pad[local]:
  !n (gs:'a list) a b x.
    n <= LENGTH gs + a /\ n <= LENGTH gs + b ==>
    TAKE n (gs ++ REPLICATE a x) = TAKE n (gs ++ REPLICATE b x)
Proof
  rw[LIST_EQ_REWRITE, LENGTH_TAKE, LENGTH_APPEND, LENGTH_REPLICATE] >>
  rw[EL_TAKE, EL_APPEND_EQN, EL_REPLICATE, LENGTH_REPLICATE]
QED

Theorem gas_prefix_suc:
  (gas_prefix (SUC n) [] = 0w :: gas_prefix n []) /\
  (gas_prefix (SUC n) (g::gs) = g :: gas_prefix n gs)
Proof
  conj_tac
  >- simp[gas_prefix_def, TAKE_def] >>
  simp[gas_prefix_def, TAKE_def] >>
  `TAKE n (gs ++ REPLICATE (SUC n) 0w) =
   TAKE n (gs ++ REPLICATE n 0w)` by
    (irule gas_take_pad >> simp[]) >>
  gvs[]
QED

Theorem gas_prefix_add:
  !n gs m. gas_prefix (n + m) gs =
    gas_prefix n gs ++ gas_prefix m (DROP n gs)
Proof
  Induct_on `n`
  >- simp[]
  >> Cases_on `gs`
  >- (simp[ADD_CLAUSES, gas_prefix_suc] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[ADD_COMM])
  >> simp[ADD_CLAUSES, gas_prefix_suc] >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[ADD_COMM]
QED

Definition gas_bind_ok_def:
  gas_bind_ok r k = case r of OK t => k t | other => other
End

Theorem gas_replay_bind_ok:
  gas_replay f s /\ (!t. f s = OK t ==> gas_replay k t) ==>
  gas_replay (\u. gas_bind_ok (f u) k) s
Proof
  simp[gas_replay_def] >> strip_tac >>
  Cases_on `f s` >> gvs[]
  >- (qexists_tac `n + n'` >>
      simp[gas_replay_at_def, gas_prefix_add, APPEND_ASSOC] >>
      gen_tac >>
      qpat_x_assum `gas_replay_at n f s` mp_tac >>
      simp[gas_replay_at_def] >>
      disch_then (qspec_then
        `gas_prefix n' (DROP n s.vs_gas_readings) ++ tail` mp_tac) >>
      Cases_on `f (s with vs_gas_readings :=
        gas_prefix n s.vs_gas_readings ++
        (gas_prefix n' (DROP n s.vs_gas_readings) ++ tail))` >>
      simp[lift_result_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `gas_replay_at n' k v` mp_tac >>
      simp[gas_replay_at_def] >>
      disch_then (qspec_then `tail` mp_tac) >>
      simp[gas_bind_ok_def, DROP_DROP_T, ADD_COMM])
  >> qexists_tac `n` >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  simp[gas_replay_at_def] >>
  disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `f (s with vs_gas_readings :=
    gas_prefix n s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def, gas_bind_ok_def]
QED

Theorem gas_oracle_replay:
  (!fuel ctx inst s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (step_inst fuel ctx inst s)
         (step_inst fuel ctx inst
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx bb s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (exec_block fuel ctx bb s)
         (exec_block fuel ctx bb
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail))) /\
  (!fuel ctx func s.
     ?n. !tail.
       lift_result
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (\a b. a.vs_gas_readings = DROP n s.vs_gas_readings /\
                  b = (a with vs_gas_readings := tail))
         (run_blocks fuel ctx func s)
         (run_blocks fuel ctx func
           (s with vs_gas_readings :=
             TAKE n (s.vs_gas_readings ++ REPLICATE n 0w) ++ tail)))
Proof
  cheat
QED
