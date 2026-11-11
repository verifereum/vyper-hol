(* Finite emission simulation.  The contracts below concern ONE emission,
   never the unprocessed suffix.  Scanner/provenance supplies endpoint laws;
   emission and runtime certificates supply the two progress contracts.
   D stores a frozen abort reason/state and a separately advancing ghost. *)
Theory acMergeSimulationProofs
Ancestors
  acChainProofs acAbortRelProofs assertCombinerDefs analysisSimDefs stateEquiv
  rich_list
Libs
  listTheory arithmeticTheory

Definition ac_live_emission_contract_def:
  ac_live_emission_contract xs cs fuel ctx R Rt A L D <=>
    !n mp su mp' out su' s t.
      n < LENGTH xs /\ L n mp su s t /\
      ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
      (!s'. step_inst fuel ctx (EL n xs) s = OK s' ==>
        ?t'. run_insts fuel ctx out t = OK t' /\
             L (SUC n) mp' su' s' t') /\
      (!a sa. step_inst fuel ctx (EL n xs) s = Abort a sa ==>
        (?ta. run_insts fuel ctx out t = Abort a ta /\ A sa ta) \/
        (?t'. run_insts fuel ctx out t = OK t' /\
              D (SUC n) mp' su' a sa s t')) /\
      (!sa. step_inst fuel ctx (EL n xs) s = Halt sa ==>
        ?ta. run_insts fuel ctx out t = Halt ta /\ Rt sa ta) /\
      (!v sa. step_inst fuel ctx (EL n xs) s = IntRet v sa ==>
        ?ta. run_insts fuel ctx out t = IntRet v ta /\ Rt sa ta)
End

Definition ac_deferred_emission_contract_def:
  ac_deferred_emission_contract xs cs fuel ctx A D <=>
    !n mp su mp' out su' a sa g t.
      n < LENGTH xs /\ D n mp su a sa g t /\
      ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
      (?ta. run_insts fuel ctx out t = Abort a ta /\ A sa ta) \/
      (?t' g'. run_insts fuel ctx out t = OK t' /\
         D (SUC n) mp' su' a sa g' t' /\
         (((EL n xs).inst_opcode = ASSERT /\ g' = g) \/
          (ac_is_safe_between (EL n xs) /\
           step_inst fuel ctx (EL n xs) g = OK g')))
End

Definition ac_emission_end_contract_def:
  ac_emission_end_contract xs R L D <=>
    (!mp su s t. L (LENGTH xs) mp su s t ==> R s t) /\
    (!mp su a sa g t. ~D (LENGTH xs) mp su a sa g t)
End

(* Arbitrary cursor, supply and actual accumulator.  Both modes are proved
   together: an early source Abort can finish through the deferred IH. *)
Theorem ac_merge_insts_simulation_suffix:
  !xs cs fuel ctx R Rt A L D.
    ac_live_emission_contract xs cs fuel ctx R Rt A L D /\
    ac_deferred_emission_contract xs cs fuel ctx A D /\
    ac_emission_end_contract xs R L D ==>
    !rest n. DROP n xs = rest /\ n <= LENGTH xs ==>
      (!mp su s t. L n mp su s t ==>
        (?e. run_insts fuel ctx rest s = Error e) \/
        lift_result R Rt A (run_insts fuel ctx rest s)
          (run_insts fuel ctx (FST (ac_merge_insts cs mp su rest)) t)) /\
      (!mp su a sa g t. D n mp su a sa g t ==>
        ?ta. run_insts fuel ctx (FST (ac_merge_insts cs mp su rest)) t =
             Abort a ta /\ A sa ta)
Proof
  rpt gen_tac >> strip_tac >> Induct >> rpt gen_tac >> strip_tac
  >- (fs[DROP_EQ_NIL] >>
      `n = LENGTH xs` by decide_tac >> gvs[] >>
      gvs[ac_emission_end_contract_def, ac_merge_insts_def,
          run_insts_def, lift_result_def] >> metis_tac[]) >>
  `n < LENGTH xs` by
    (spose_not_then assume_tac >> fs[NOT_LESS, DROP_LENGTH_TOO_LONG]) >>
  `EL n xs = h` by metis_tac[HD_DROP, HD] >>
  `DROP (SUC n) xs = rest` by
    (qspecl_then [`1`,`n`,`xs : instruction list`] mp_tac DROP_DROP_T >>
     simp[ADD1]) >>
  `SUC n <= LENGTH xs` by decide_tac >>
  first_x_assum (qspec_then `SUC n` mp_tac) >> simp[] >> strip_tac >>
  conj_tac >- suspend "live" >> suspend "deferred"
QED

Resume ac_merge_insts_simulation_suffix[live]:
  rpt gen_tac >> strip_tac >> fs[] >>
  Cases_on `ac_merge_inst cs mp su (EL n xs)` >>
  rename1 `ac_merge_inst cs mp su (EL n xs) = (mp',z)` >>
  Cases_on `z` >> rename1 `ac_merge_inst cs mp su (EL n xs) = (mp',out,su')` >>
  `n < LENGTH xs` by decide_tac >>
  drule (iffLR ac_live_emission_contract_def) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `ac_merge_insts cs mp' su' rest` >>
  simp[Once ac_merge_insts_def, run_insts_append, run_insts_def] >>
  Cases_on `step_inst fuel ctx (EL n xs) s` >> gvs[] >>
  fs[run_insts_append, lift_result_def] >>
  first_x_assum drule >> simp[lift_result_def] >>
  strip_tac >> simp[lift_result_def]
QED

Resume ac_merge_insts_simulation_suffix[deferred]:
  rpt gen_tac >> strip_tac >> fs[] >>
  Cases_on `ac_merge_inst cs mp su (EL n xs)` >>
  rename1 `ac_merge_inst cs mp su (EL n xs) = (mp',z)` >>
  Cases_on `z` >> rename1 `ac_merge_inst cs mp su (EL n xs) = (mp',out,su')` >>
  `n < LENGTH xs` by decide_tac >>
  drule (iffLR ac_deferred_emission_contract_def) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `ac_merge_insts cs mp' su' rest` >>
  simp[Once ac_merge_insts_def, run_insts_append] >>
  gvs[run_insts_append] >> first_x_assum drule >> simp[]
QED

Finalise ac_merge_insts_simulation_suffix


(* Proof-facing cursor invariants.  S carries ordered provenance/freshness;
   pending selects ONLY the current chain entry, resolved through the actual
   mp accumulator.  K is the source cursor certificate.  Neither predicate
   contains any execution of an unprocessed suffix. *)
Definition ac_merge_live_def:
  ac_merge_live X K S pending n mp su s t <=>
    S n mp su /\ K n s /\ state_equiv X s t /\
    (!j p. pending n mp su = SOME (j,p) ==>
           eval_operand p t = SOME 0w)
End

Definition ac_merge_deferred_def:
  ac_merge_deferred X K S pending n mp su (a:abort_type) sa g t <=>
    S n mp su /\ K n g /\ state_equiv X g t /\
    (?j p v. pending n mp su = SOME (j,p) /\
             eval_operand p t = SOME v /\ v <> 0w) /\
    ac_abort_equiv sa (revert_state (set_returndata [] g))
End

(* The scanner endpoint condition, unlike a semantic suffix assumption,
   merely says that no removed assertion is left waiting at end-of-list. *)
Theorem ac_merge_cursor_end_contract:
  !S pending xs X K.
  (!mp su. S (LENGTH xs) mp su ==>
      pending (LENGTH xs) mp su = NONE) ==>
  ac_emission_end_contract xs (state_equiv X)
    (ac_merge_live X K S pending) (ac_merge_deferred X K S pending)
Proof
  rw[ac_emission_end_contract_def, ac_merge_live_def,
     ac_merge_deferred_def] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

(* C1.6 instantiates K with runtime certificates and S/pending with scanner
   provenance and the selected ALOOKUP entry.  All semantic obligations below
   concern only one emitted list, including the ghost continuation case. *)
Theorem ac_merge_insts_simulation_conditional:
  !xs dfg fuel ctx X K S pending su s t.
    ac_live_emission_contract xs (ac_scan_block dfg xs NONE) fuel ctx
      (state_equiv X) (execution_equiv UNIV) ac_abort_equiv
      (ac_merge_live X K S pending) (ac_merge_deferred X K S pending) /\
    ac_deferred_emission_contract xs (ac_scan_block dfg xs NONE) fuel ctx
      ac_abort_equiv (ac_merge_deferred X K S pending) /\
    (!mp su'. S (LENGTH xs) mp su' ==>
       pending (LENGTH xs) mp su' = NONE) /\
    ac_merge_live X K S pending 0 [] su s t ==>
    (?e. run_insts fuel ctx xs s = Error e) \/
    lift_result (state_equiv X) (execution_equiv UNIV) ac_abort_equiv
      (run_insts fuel ctx xs s)
      (run_insts fuel ctx
        (FST (ac_merge_insts (ac_scan_block dfg xs NONE) [] su xs)) t)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `ac_merge_live X cert shape pending 0 [] su s t` >>
  `ac_emission_end_contract xs (state_equiv X)
     (ac_merge_live X cert shape pending) (ac_merge_deferred X cert shape pending)` by
    (irule ac_merge_cursor_end_contract >> simp[]) >>
  drule ac_merge_insts_simulation_suffix >> simp[] >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED
