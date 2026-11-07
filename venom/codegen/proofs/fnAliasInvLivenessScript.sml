Theory fnAliasInvLiveness
Ancestors
  livenessTerminationProofs livenessTransferProofs livenessBlockProofs
  livenessDefs dfAnalyzeDefs
Libs
  listTheory

(* Sufficient closure under exactly the transfers used by the analysis. *)
Definition alias_live_closed_def:
  alias_live_closed fn P <=>
    (!l bb i live.
      lookup_block l fn.fn_blocks = SOME bb /\
      i < LENGTH bb.bb_instructions /\
      (!v. MEM v live ==> P l (SUC i) v) ==>
      !v. MEM v (liveness_transfer fn.fn_blocks
                    (EL i bb.bb_instructions) live) ==> P l i v) /\
    (!l s live.
      MEM s (cfg_succs_of (cfg_analyze fn) l) /\
      (!v. MEM v live ==> P s 0 v) ==>
      !v. MEM v (liveness_edge_transfer fn.fn_blocks s l live) ==>
        P l (LENGTH (liveness_instrs fn.fn_blocks l)) v)
End

Theorem alias_live_closed_inst:
  alias_live_closed fn P /\
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (!w. MEM w live ==> P l (SUC i) w) /\
  MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions) live) ==>
  P l i v
Proof
  simp[alias_live_closed_def] >> metis_tac[]
QED

Theorem alias_live_closed_edge:
  alias_live_closed fn P /\
  MEM s (cfg_succs_of (cfg_analyze fn) l) /\
  (!w. MEM w live ==> P s 0 w) /\
  MEM v (liveness_edge_transfer fn.fn_blocks s l live) ==>
  P l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  simp[alias_live_closed_def] >> metis_tac[]
QED

Theorem alias_liveness_transfer_rule:
  (!v. MEM v (inst_uses inst) ==> A v) /\
  (!v. MEM v live /\ ~MEM v (inst_defs inst) ==> A v) ==>
  !v. MEM v (liveness_transfer bbs inst live) ==> A v
Proof
  simp[liveness_transfer_def, live_update_mem] >> metis_tac[]
QED

Theorem alias_liveness_edge_present:
  lookup_block s bbs = SOME bb /\
  (!v. MEM v (input_vars_from l bb.bb_instructions live) ==> A v) ==>
  !v. MEM v (liveness_edge_transfer bbs s l live) ==> A v
Proof
  simp[liveness_edge_transfer_def]
QED

Theorem alias_liveness_edge_absent:
  lookup_block s bbs = NONE /\ (!v. MEM v live ==> A v) ==>
  !v. MEM v (liveness_edge_transfer bbs s l live) ==> A v
Proof
  simp[liveness_edge_transfer_def]
QED

Theorem alias_live_closed_out:
  alias_live_closed fn P /\
  (!l i v. MEM v (df_at [] st l i) ==> P l i v) /\
  MEM v (liveness_out fn.fn_blocks (cfg_analyze fn) l st) ==>
  P l (LENGTH (liveness_instrs fn.fn_blocks l)) v
Proof
  simp[liveness_out_def, livenessTransferProofsTheory.mem_foldl_list_union,
       MEM_MAP] >> rpt strip_tac >>
  gvs[] >> irule alias_live_closed_edge >> simp[] >>
  qexistsl_tac [`df_at [] st s 0`,`s`] >> simp[]
QED

Theorem alias_live_closed_block_range:
  alias_live_closed fn P /\
  (!l i v. MEM v (df_at [] st l i) ==> P l i v) ==>
  !n l i v. n = LENGTH (liveness_instrs fn.fn_blocks l) - i /\
    i <= LENGTH (liveness_instrs fn.fn_blocks l) /\
    MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) l st) l i) ==>
    P l i v
Proof
  strip_tac >> Induct
  >- (rpt strip_tac >>
      `i = LENGTH (liveness_instrs fn.fn_blocks l)` by decide_tac >>
      gvs[liveness_block_exit] >> metis_tac[alias_live_closed_out]) >>
  rpt strip_tac >>
  `i < LENGTH (liveness_instrs fn.fn_blocks l)` by decide_tac >>
  drule liveness_block_transfer >>
  disch_then (qspecl_then [`st`,`cfg_analyze fn`] assume_tac) >>
  Cases_on `lookup_block l fn.fn_blocks` >> gvs[liveness_instrs_def] >>
  irule alias_live_closed_inst >>
  qexistsl_tac [`x`,`fn`,`df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) l st) l (SUC i)`] >>
  simp[] >> rpt strip_tac >> first_x_assum irule >>
  simp[liveness_instrs_def] >> decide_tac
QED

Theorem alias_live_closed_block:
  alias_live_closed fn P /\
  (!l i v. MEM v (df_at [] st l i) ==> P l i v) ==>
  !l i v. MEM v (df_at [] (liveness_block fn.fn_blocks (cfg_analyze fn) b st) l i) ==>
    P l i v
Proof
  rpt strip_tac >> Cases_on `l = b`
  >- (gvs[] >> Cases_on `i <= LENGTH (liveness_instrs fn.fn_blocks b)`
      >- (irule alias_live_closed_block_range >> metis_tac[]) >>
      `LENGTH (liveness_instrs fn.fn_blocks b) < i` by decide_tac >>
      gvs[liveness_block_beyond] >> metis_tac[]) >>
  gvs[liveness_block_other_inst] >> metis_tac[]
QED

Theorem alias_live_closed_analyze:
  alias_live_closed fn P ==>
  !l i v. MEM v (live_vars_at (liveness_analyze fn) l i) ==> P l i v
Proof
  strip_tac >>
  `!l i v. MEM v (df_at [] (liveness_recompute fn) l i) ==> P l i v`
    suffices_by simp[live_vars_at_def, liveness_analyze_def] >>
  mp_tac (Q.INST [`Q` |->
    `\p. !l i v. MEM v (df_at [] (SND p) l i) ==> P l i v`]
    liveness_recompute_lift) >>
  (impl_tac
   >- (conj_tac
       >- simp[init_df_state_def, df_at_def] >>
       rpt strip_tac >> PairCases_on `p` >>
       Cases_on `p0` >> gvs[worklistDefsTheory.wl_step_def] >>
       simp[COND_RAND] >> rpt strip_tac >>
       irule alias_live_closed_block >>
       qexistsl_tac [`h`,`fn`,`p1`] >> simp[])) >>
  simp[liveness_recompute_def]
QED
