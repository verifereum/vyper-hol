Theory acMergeCursorProofs
Ancestors
  acMergeCursorDefs acSupplyProofs acChainProofs assertCombinerDefs
  irSupplyFreshProps venomFnScheduleRunner list rich_list alist

(* Prefix reachability records the actual supply, not arbitrary historical
   association-list values. *)
Theorem ac_merge_prefix_bounds:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    n <= LENGTH xs /\ ir_supply_extends su0 su
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_ind >>
  simp[ir_supply_extends_refl] >> rpt gen_tac >> strip_tac >>
  drule ac_merge_inst_fresh >> strip_tac >>
  metis_tac[ir_supply_extends_trans]
QED

Theorem ac_merge_prefix_completion:
  !xs cs su0 n mp su.
    ac_merge_prefix_reachable xs cs su0 n mp su ==>
    SND (ac_merge_insts cs [] su0 xs) =
    SND (ac_merge_insts cs mp su (DROP n xs))
Proof
  ho_match_mp_tac ac_merge_prefix_reachable_ind >> rpt strip_tac
  >- simp[] >>
  `DROP n xs = EL n xs :: DROP (SUC n) xs` by
    simp[DROP_CONS_EL] >>
  gvs[Once ac_merge_insts_def] >>
  Cases_on `ac_merge_insts cs mp' su' (DROP (SUC n) xs)` >> gvs[]
QED

Theorem ac_merge_prefix_remaining_supply:
  ac_merge_prefix_reachable xs cs su0 n mp su ==>
  ir_supply_extends su (SND (ac_merge_insts cs [] su0 xs))
Proof
  strip_tac >> drule ac_merge_prefix_completion >> strip_tac >>
  Cases_on `ac_merge_insts cs mp su (DROP n xs)` >> gvs[] >>
  drule ac_merge_insts_fresh >> simp[]
QED

Theorem ac_merge_static_initial:
  ir_supply_extends (SND (ac_merge_insts cs [] su0 xs)) su_end ==>
  ac_merge_static xs cs su0 su_end 0 [] su0
Proof
  strip_tac >> simp[ac_merge_static_def, ac_merge_prefix_zero] >>
  irule ir_supply_extends_trans >>
  qexists `SND (ac_merge_insts cs [] su0 xs)` >> simp[] >>
  irule ac_merge_prefix_remaining_supply >>
  qexistsl [`[]`,`0`] >> simp[ac_merge_prefix_zero]
QED

Theorem ac_merge_static_step:
  ir_supply_extends (SND (ac_merge_insts cs [] su0 xs)) su_end /\
  ac_merge_static xs cs su0 su_end n mp su /\ n < LENGTH xs /\
  ac_merge_inst cs mp su (EL n xs) = (mp',out,su') ==>
  ac_merge_static xs cs su0 su_end (SUC n) mp' su' /\
  ir_supply_extends su su'
Proof
  rpt strip_tac
  >- (simp[ac_merge_static_def] >>
      `ac_merge_prefix_reachable xs cs su0 (SUC n) mp' su'` by
        (irule ac_merge_prefix_step >> fs[ac_merge_static_def] >> metis_tac[]) >>
      simp[] >> irule ir_supply_extends_trans >>
      qexists `SND (ac_merge_insts cs [] su0 xs)` >> simp[] >>
      irule ac_merge_prefix_remaining_supply >> metis_tac[]) >>
  drule ac_merge_inst_fresh >> simp[]
QED
