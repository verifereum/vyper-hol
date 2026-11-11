Theory o1MakeSsaFlags
Ancestors
  unitShapeDefs makeSsaDefs irSupply venomInst list alist pair makeSsaCurrentAllocation

(* The live original flags need only have their current concrete names among
   the output aliases. Older concrete versions can safely remain in ws. *)
Definition current_flag_alias_def:
  current_flag_alias rs vs ws <=>
    !v. MEM v vs ==> MEM (latest_current_name rs v) ws
End

(* Ported from makeSsaCurrentAllocation in the read-only makessa3 reference.
   This interface is independent of definite assignment and dominance. *)
Theorem current_flag_alias_copy:
  current_flag_alias rs vs ws /\
  push_current_name s rs v = (rs',s',n) ==>
  current_flag_alias rs' (v::vs) (n::ws)
Proof
  rpt strip_tac >> drule current_push_latest >> strip_tac >>
  gvs[current_flag_alias_def] >> rpt strip_tac >>
  Cases_on `v' = v` >> gvs[]
QED

Theorem current_flag_alias_redefine:
  current_flag_alias rs vs ws /\
  push_current_name s rs v = (rs',s',n) /\
  (!w. MEM w vs /\ w <> v ==> latest_current_name rs w <> n) ==>
  current_flag_alias rs' (FILTER (\w. w <> v) vs)
                        (FILTER (\w. w <> n) ws)
Proof
  rpt strip_tac >> drule current_push_latest >> strip_tac >>
  gvs[current_flag_alias_def, MEM_FILTER] >> rpt strip_tac >>
  simp[] >> metis_tac[]
QED

Theorem current_flag_alias_empty[simp]:
  current_flag_alias rs [] []
Proof
  simp[current_flag_alias_def]
QED

Theorem current_flag_alias_call:
  push_current_name s rs v = (rs',s',n) ==>
  current_flag_alias rs' [v] [n]
Proof
  strip_tac >> drule current_push_latest >>
  simp[current_flag_alias_def]
QED

Theorem current_flag_alias_assert:
  current_flag_alias rs vs ws /\
  flag_fails bbs vs (mk_inst id ASSERT [Var v] []) ==>
  flag_fails bbs ws (mk_inst id ASSERT [Var (latest_current_name rs v)] [])
Proof
  simp[flag_fails_def, mk_inst_def, current_flag_alias_def]
QED

Theorem current_flag_path_write:
  write_effects inst.inst_opcode <> empty_effects ==>
  (flag_path bbs vs (inst::rest) <=>
   inst.inst_opcode <> INVOKE /\
   (flag_fails bbs vs inst \/ flag_path bbs [] rest))
Proof
  simp[flag_path_def]
QED

(* Candidate recursive consumer interface (not established here):
   under the allocation-consistency invariant and current_flag_alias rs vs ws,
   rename_current_block_insts s rs insts = (rs',s',insts') should transport
   flag_path bbs vs insts to flag_path bbs' ws insts'. The bbs/bbs' boundary
   must preserve revert_path and block-list length. The copy case above uses
   an evolving rs; the redefinition case additionally needs disjointness of
   the new concrete output from current names of surviving original aliases.
   This disjointness is not a consequence of current_flag_alias alone. *)
