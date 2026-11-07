Theory frameBlockSegments
Ancestors venomExecSemantics venomState venomInst

(* Fixed-fuel prefixes of actual block execution.  A successful step may
   itself include a completed call; no claim about producing that step or
   about changing its fuel is part of this interface.  In particular the
   nonterminator branch does not inspect post.vs_halted. *)
Inductive block_segment:
[~empty:]
  (!fuel ctx bb s. block_segment fuel ctx bb s s)
[~next:]
  (!fuel ctx bb s inst post t.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK post /\
    block_segment fuel ctx bb
      (post with vs_inst_idx := SUC s.vs_inst_idx) t ==>
    block_segment fuel ctx bb s t)
End

Theorem block_segment_replay:
  !fuel ctx bb s t. block_segment fuel ctx bb s t ==>
    exec_block fuel ctx bb s = exec_block fuel ctx bb t
Proof
  ho_match_mp_tac block_segment_ind >> rpt strip_tac >>
  simp[Once exec_block_def]
QED

(* Endpoints, not instruction-list equality or equal prefix lengths, are
   the boundary for pairing two executions.  R may relate arbitrary
   results, including errors, halts and internal returns. *)
Theorem block_segment_pair_replay:
  block_segment fuel ctx bb s t /\
  block_segment fuel' ctx' bb' s' t' /\
  R (exec_block fuel ctx bb t) (exec_block fuel' ctx' bb' t') ==>
  R (exec_block fuel ctx bb s) (exec_block fuel' ctx' bb' s')
Proof
  metis_tac[block_segment_replay]
QED
