(*
 * An executable definite-assignment check for Venom functions, and its
 * soundness: a function that passes it has fn_defs_reach_uses.
 *
 * The check rejects PHIs and accepts a use of v in block bb when v is
 * written earlier in bb, or written in the entry block and bb is another
 * block (every path to bb starts with the whole entry block), or bb cannot
 * be reached from the entry along blocks that don't write v.  The first
 * two cover almost every use in lowered code, so the search runs rarely.
 * It is the HOL counterpart of the VarNotDefined check in
 * vyper/venom/check_venom.py, decided per variable by a graph search
 * instead of the VarDefinition dataflow.
 *
 * TOP-LEVEL:
 *   fn_defs_reach_uses_check        -- the check
 *   fn_defs_reach_uses_check_sound  -- check ==> fn_defs_reach_uses
 *)

Theory defsReachCheck
Ancestors
  venomWf venomInst list rich_list

(* Some instruction of bb writes v. *)
Definition bb_writes_def:
  bb_writes v bb <=> EXISTS (\inst. MEM v inst.inst_outputs) bb.bb_instructions
End

(* One sweep over the blocks: add the successors of each block in R that
   doesn't write v. *)
Definition avoid_sweep_def:
  avoid_sweep v [] R = R /\
  avoid_sweep v (bb::bbs) R =
    avoid_sweep v bbs
      (if MEM bb.bb_label R /\ ~bb_writes v bb then
         FILTER (\s. ~MEM s R) (bb_succs bb) ++ R
       else R)
End

(* Sweep until nothing is added; NONE when the fuel runs out first. *)
Definition avoid_reach_def:
  avoid_reach v bbs (0:num) R = NONE /\
  avoid_reach v bbs (SUC n) R =
    let R' = avoid_sweep v bbs R in
    if LENGTH R' = LENGTH R then SOME R else avoid_reach v bbs n R'
End

(* Enough sweeps: each productive one adds a successor label. *)
Definition avoid_fuel_def:
  avoid_fuel bbs = SUC (SUM (MAP (\bb. LENGTH (bb_succs bb)) bbs))
End

(* Every path from entry to lbl passes a block that writes v. *)
Definition var_def_reaches_def:
  var_def_reaches fn entry_bb lbl v <=>
    (lbl <> entry_bb.bb_label /\ bb_writes v entry_bb) \/
    case avoid_reach v fn.fn_blocks (avoid_fuel fn.fn_blocks)
           [entry_bb.bb_label] of
      NONE => F
    | SOME R => ~MEM lbl R
End

(* defs: the variables written earlier in the block. *)
Definition insts_defs_reach_check_def:
  insts_defs_reach_check fn entry_bb lbl defs [] = T /\
  insts_defs_reach_check fn entry_bb lbl defs (inst::rest) =
    (inst.inst_opcode <> PHI /\
     EVERY (\op. case op of
                   Var v => MEM v defs \/ var_def_reaches fn entry_bb lbl v
                 | _ => T) inst.inst_operands /\
     insts_defs_reach_check fn entry_bb lbl (inst.inst_outputs ++ defs) rest)
End

Definition fn_defs_reach_uses_check_def:
  fn_defs_reach_uses_check fn <=>
    case fn.fn_blocks of
      [] => T
    | entry_bb :: _ =>
        EVERY (\bb. insts_defs_reach_check fn entry_bb bb.bb_label []
                      bb.bb_instructions) fn.fn_blocks
End

(* R is closed under the edges out of blocks that don't write v. *)
Definition avoid_closed_def:
  avoid_closed v bbs R <=>
    !bb s. MEM bb bbs /\ MEM bb.bb_label R /\ ~bb_writes v bb /\
           MEM s (bb_succs bb) ==> MEM s R
End

Theorem avoid_sweep_extends[local]:
  !bbs R v. ?X. avoid_sweep v bbs R = X ++ R
Proof
  Induct >- (simp[avoid_sweep_def] >> qexists_tac `[]` >> simp[]) >>
  simp[avoid_sweep_def] >> rpt gen_tac >> IF_CASES_TAC >> simp[] >>
  qmatch_goalsub_abbrev_tac `avoid_sweep v bbs R0` >>
  first_x_assum (qspecl_then [`R0`, `v`] strip_assume_tac) >> simp[Abbr `R0`] >>
  metis_tac[APPEND_ASSOC]
QED

Theorem avoid_sweep_mono[local]:
  !x R v bbs. MEM x R ==> MEM x (avoid_sweep v bbs R)
Proof
  rpt strip_tac >>
  qspecl_then [`bbs`, `R`, `v`] strip_assume_tac avoid_sweep_extends >>
  simp[]
QED

Theorem avoid_sweep_succs[local]:
  !bbs R bb s v.
    MEM bb bbs /\ MEM bb.bb_label R /\ ~bb_writes v bb /\
    MEM s (bb_succs bb) ==> MEM s (avoid_sweep v bbs R)
Proof
  Induct >> rw[avoid_sweep_def] >> gvs[]
  >- (irule avoid_sweep_mono >> simp[MEM_FILTER] >> metis_tac[])
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem avoid_reach_closed[local]:
  !n R R' v bbs. avoid_reach v bbs n R = SOME R' ==>
                 (!x. MEM x R ==> MEM x R') /\ avoid_closed v bbs R'
Proof
  Induct >> simp[avoid_reach_def] >> rpt gen_tac >> IF_CASES_TAC >>
  strip_tac
  >- (gvs[avoid_closed_def] >> rpt strip_tac >>
      drule_all avoid_sweep_succs >> strip_tac >>
      qspecl_then [`bbs`, `R`, `v`] strip_assume_tac avoid_sweep_extends >>
      gvs[]) >>
  first_x_assum drule >> strip_tac >> simp[] >>
  metis_tac[avoid_sweep_mono]
QED

Theorem avoid_closed_path[local]:
  !rest a fn v R.
    avoid_closed v fn.fn_blocks R /\ MEM a R /\ is_fn_path fn (a::rest) /\
    (!x bb. MEM x (FRONT (a::rest)) /\ MEM bb fn.fn_blocks /\
            bb.bb_label = x ==> ~bb_writes v bb) ==>
    MEM (LAST (a::rest)) R
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[is_fn_path_def, fn_cfg_edge_def] >>
  `MEM h R` by (gvs[avoid_closed_def] >> first_x_assum irule >>
                qexists_tac `bb` >> simp[]) >>
  first_x_assum (qspecl_then [`h`, `fn`, `v`, `R`] mp_tac) >>
  simp[LAST_DEF] >> Cases_on `rest` >> gvs[]
QED

Theorem insts_defs_reach_check_el[local]:
  !insts defs j.
    insts_defs_reach_check fn e lbl defs insts /\ j < LENGTH insts ==>
    (EL j insts).inst_opcode <> PHI /\
    !v. MEM (Var v) (EL j insts).inst_operands ==>
        MEM v defs \/
        (?i. i < j /\ MEM v (EL i insts).inst_outputs) \/
        var_def_reaches fn e lbl v
Proof
  Induct >> simp[insts_defs_reach_check_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `j` >> gvs[EVERY_MEM]
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  first_x_assum drule_all >> strip_tac >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
  >- (disj2_tac >> disj1_tac >> qexists_tac `0` >> simp[])
  >- (disj2_tac >> disj1_tac >> qexists_tac `SUC i` >> simp[])
QED

Theorem MEM_FRONT_EL[local]:
  !l x. MEM x (FRONT l) /\ l <> [] ==> ?k. k < LENGTH l - 1 /\ EL k l = x
Proof
  rpt strip_tac >> gvs[MEM_EL, LENGTH_FRONT] >>
  qexists_tac `n` >> simp[] >> irule (GSYM EL_FRONT) >>
  simp[LENGTH_FRONT, NULL_EQ]
QED

Theorem var_def_reaches_def_on_all_paths[local]:
  !fn entry_bb rest bb use_inst_opt v.
    fn.fn_blocks = entry_bb :: rest /\ MEM bb fn.fn_blocks /\
    var_def_reaches fn entry_bb bb.bb_label v ==>
    def_on_all_paths fn bb use_inst_opt v
Proof
  rpt gen_tac >> strip_tac >>
  simp[def_on_all_paths_def, fn_entry_label_def, entry_block_def] >>
  rpt strip_tac >> disj1_tac >>
  qpat_x_assum `var_def_reaches _ _ _ _` mp_tac >>
  simp[var_def_reaches_def] >> strip_tac
  >- (qexistsl [`0`, `entry_bb`] >> Cases_on `path` >> gvs[] >>
      Cases_on `t` >> gvs[bb_writes_def, EXISTS_MEM] >> metis_tac[]) >>
  Cases_on `avoid_reach v (entry_bb::rest) (avoid_fuel (entry_bb::rest))
               [HD path]` >> gvs[] >>
  drule avoid_reach_closed >> strip_tac >>
  CCONTR_TAC >>
  `MEM (LAST path) x` by
    (Cases_on `path` >- fs[] >>
     qspecl_then [`t`, `h`, `fn`, `v`, `x`] mp_tac avoid_closed_path >>
     impl_tac >- (fs[] >> rpt strip_tac >> fs[bb_writes_def, EXISTS_MEM] >>
                  drule MEM_FRONT_EL >> simp[] >> strip_tac >>
                  metis_tac[]) >>
     simp[]) >>
  gvs[]
QED

Theorem fn_defs_reach_uses_check_block[local]:
  !fn entry_bb rest bb.
    fn_defs_reach_uses_check fn /\ fn.fn_blocks = entry_bb :: rest /\
    MEM bb fn.fn_blocks ==>
    insts_defs_reach_check fn entry_bb bb.bb_label [] bb.bb_instructions
Proof
  rw[fn_defs_reach_uses_check_def] >> gvs[EVERY_MEM]
QED

Theorem fn_defs_reach_uses_check_sound:
  !fn. fn_defs_reach_uses_check fn ==> fn_defs_reach_uses fn
Proof
  rpt strip_tac >> simp[fn_defs_reach_uses_def] >> rpt gen_tac >>
  strip_tac >>
  Cases_on `fn.fn_blocks` >- gvs[] >>
  rename1 `fn.fn_blocks = entry_bb :: rest` >>
  `insts_defs_reach_check fn entry_bb bb.bb_label [] bb.bb_instructions` by
    metis_tac[fn_defs_reach_uses_check_block] >>
  qpat_x_assum `MEM inst _` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `inst = EL j bb.bb_instructions` >>
  drule_all insts_defs_reach_check_el >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac
  >- fs[]
  >- (simp[def_on_all_paths_def] >> rpt strip_tac >> disj2_tac >>
      qexists_tac `i` >> simp[] >> qexists_tac `j` >> simp[]) >>
  irule var_def_reaches_def_on_all_paths >> metis_tac[]
QED
