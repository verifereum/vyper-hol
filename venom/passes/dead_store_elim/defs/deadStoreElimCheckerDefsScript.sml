(*
 * Dead Store Elimination — executable dead-store check
 *
 * dse_checked_analysis cand keeps the candidate ids that pass an executable
 * check of every all_dead_stores condition, so it meets all_dead_stores for
 * any candidate list (deadStoreElimCheckerTheory).  The liveness walk is a
 * bounded label search followed by an explicit closure check, so its
 * soundness needs no termination argument.
 *)
Theory deadStoreElimCheckerDefs
Ancestors
  deadStoreElimDefs basePtrDefs cfgDefs memLocDefs list rich_list

(* Some instruction of the list reads store_loc before any instruction
   completely clobbers it (a read and a clobber in one instruction count as
   a read). *)
Definition dse_read_before_clobber_def:
  (dse_read_before_clobber aliases bp space store_loc [] <=> F) /\
  (dse_read_before_clobber aliases bp space store_loc (inst::insts) <=>
     dse_inst_reads_alias aliases bp space store_loc inst \/
     (~dse_inst_clobbers bp space store_loc inst /\
      dse_read_before_clobber aliases bp space store_loc insts))
End

(* Executable block_no_full_clobber. *)
Definition dse_clobber_free_def:
  dse_clobber_free bp space store_loc fn lbl <=>
    EVERY (\bb. bb.bb_label = lbl ==>
                EVERY (\inst. ~dse_inst_clobbers bp space store_loc inst)
                      bb.bb_instructions)
          fn.fn_blocks
End

(* One step of the walk in dse_mem_def_live: add the successors of the
   reached labels whose blocks do not clobber store_loc. *)
Definition dse_reach_step_def:
  dse_reach_step cfg bp space store_loc fn lbls =
    nub (lbls ++
         FLAT (MAP (\lbl. if dse_clobber_free bp space store_loc fn lbl
                          then cfg_succs_of cfg lbl else []) lbls))
End

(* Executable sufficient condition for ~dse_mem_def_live.  The walk stops
   after SUC (LENGTH fn.fn_blocks) steps; the check then requires the
   reached labels to be closed under the walk, so stopping early only
   rejects a store, never accepts a live one. *)
Definition dse_not_live_check_def:
  dse_not_live_check cfg aliases bp store_loc space fn bb inst_idx <=>
    let rest = DROP (SUC inst_idx) bb.bb_instructions in
    let reached = FUNPOW (dse_reach_step cfg bp space store_loc fn)
                    (SUC (LENGTH fn.fn_blocks))
                    (cfg_succs_of cfg bb.bb_label) in
    ~dse_read_before_clobber aliases bp space store_loc rest /\
    (EXISTS (dse_inst_clobbers bp space store_loc) rest \/
     EVERY (\lbl.
       (dse_clobber_free bp space store_loc fn lbl ==>
        EVERY (\l. MEM l reached) (cfg_succs_of cfg lbl)) /\
       ~EXISTS (\bb'. bb'.bb_label = lbl /\
                      dse_read_before_clobber aliases bp space store_loc
                        bb'.bb_instructions)
               fn.fn_blocks)
       reached)
End

(* Executable all_dead_stores condition for one instruction id. *)
Definition dse_dead_store_check_def:
  dse_dead_store_check cfg aliases bp space fn id <=>
    EXISTS (\bb. EXISTS (\inst_idx.
      let inst = EL inst_idx bb.bb_instructions in
      let loc = bp_get_write_location bp inst space in
        inst.inst_id = id /\
        is_memory_def_opcode space inst.inst_opcode /\
        inst.inst_outputs = [] /\
        ~loc.ml_volatile /\ ml_is_fixed loc /\ loc.ml_size <> SOME 0 /\
        effects_in_space space inst /\
        dse_not_live_check cfg aliases bp loc space fn bb inst_idx)
      (COUNT_LIST (LENGTH bb.bb_instructions))) fn.fn_blocks
End

(* The candidate ids (cand space fn) that pass the check.  Any cand gives
   an analysis that satisfies all_dead_stores. *)
Definition dse_checked_analysis_def:
  dse_checked_analysis cand space fn =
    set (FILTER (dse_dead_store_check (cfg_analyze fn) FEMPTY
                   (bp_analyze (cfg_analyze fn) fn) space fn)
                (cand space fn))
End
