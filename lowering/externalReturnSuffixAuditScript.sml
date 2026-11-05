(* Task-owned continuation audit; no admitted suffix theorem. *)
Theory externalReturnSuffixAudit
Ancestors externalReturnAllocEncoder

(* C1.5.2.2.9: exact interfaces inspected.

   1. fragExec.frag_exec_def quantifies over EVERY fn containing the code.
      With live entry PC, frag_exec ctx st mid (=s) (=u) (K F) gives u's
      live mid PC and the non-Error continuation simulation, for that fn.
      abiDecoderLoop.abi_decode_sim_from_fragment exports exactly this:
        frag_exec ctx st mid P Q (K F) /\ fn_has_code st mid fn /\ P s /\
        ~s.vs_halted /\ s.vs_current_bb=st.cs_current_bb /\
        s.vs_inst_idx=LENGTH st.cs_current_insts ==>
        ?u. Q u /\ live_mid_PC u /\ abi_decode_sim ctx fn s u.
      abi_decode_sim_def is continuation simulation, not an execution trace.
      abi_decode_sim_trans composes it. Its use is sound after the suffix
      produces a concrete Halt, which is non-Error.

   2. abiEncoderWindowContract.abi_encoder_window_result_def provides
      bytes at d, evaluated length, live encoder-end PC, preservation of
      old reserved Vars, registered effects, and abi_decode_sim ctx func u t.
      It does NOT itself provide frag_exec or universal containing-function
      simulation. In particular .8's func is fixed, while frag_exec binds fn.
      fn_has_code does not imply fn=func or distinct ids for arbitrary fn.
      Consequently a direct rewrite of .8 into a universally quantified
      frag_exec is not justified by the accepted contracts. This is a proof
      interface issue, not a source-semantic counterexample. A fixed-func
      terminating run is sufficient for the eventual counted stmt_frag,
      whose definition already fixes func and assumes distinct ids.

   3. Operational suffix statement proposed (fixed arbitrary func):
      Let A be precisely the antecedent of
      return_output_alloc_encoder_continuation, adding
        emit_inst RETURN [buf.buf_operand;out] [] en=(x,sf) /\
        fn_has_code en sf func /\ ~s.vs_halted /\
        s.vs_current_bb=st.cs_current_bb /\
        s.vs_inst_idx=LENGTH st.cs_current_insts.
      Then A ==>
        ?fuel ss. run_from fuel ctx func s = Halt ss /\
          ss.vs_returndata=enc at av /\
          contract_storage ss=contract_storage s /\
          contract_transient ss=contract_transient s /\
          ss.vs_logs=s.vs_logs /\ ss.vs_requests=s.vs_requests /\
          ss.vs_pending_deletions=s.vs_pending_deletions.
      No claimed theorem here. Allocation .8 plus from_fragment supplies
      live u; .8 supplies t and dst value, window_result supplies bytes,
      length, end PC, registered effects and sim u t. enc length<dimword
      follows length<=msz<dimword. loweringHalt.return_buffer_run executes
      RETURN once code lookup is extracted from emit_inst metadata and
      fn_has_code; sim u t and sim s u lift its Halt back to s.
      return_buffer_run preserves accounts/transient/logs/requests/deletions.
      The exact logs/requests/deletions equalities to s above still need an
      allocation observer-frame boundary: .8 exports only contract projections
      and labels, not these exact equalities. Do not assume them from .8.
      For external success projection they can instead be relative to u:
      Allocation .8 preserves contract projections, labels; its stmt_state_rel
      at u plus encoder/RETURN effects is sufficient for external_halt_success
      with u as the source-related anchor (no need for state_rel at t).

   4. Result projection proposed, separately:
      Add to A the premises
        cx.sources=srcs /\ cx.layouts=layouts /\ cx.txn.target=tx.target /\
        ~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops /\
        return_bytes tops ret v (enc at av).
      Conclude ?fuel. external_call_result_rel tops ret tx
        (INL v, finalize_pending_deletions
          (abstract_machine_from_state srcs exps layouts es), es.requests)
        (run_from fuel ctx func s).
      loweringHalt.external_halt_success consumes state_rel at u and equality
      of accounts/transient/logs/requests/deletions to the final Halt state.
      vyperLoweringCorrect.chosen_return_abi_bytes supplies return_bytes once
      av is identified with the source value under the selected wrap policy.
      external_call_result_rel_def and tx_return_bytes_def then project success.
      Bytes alone do not imply account/log/request agreement. The raw flag
      and type/wrap/ABI correspondence are caller facts, not encoder facts.

   5. Smallest missing bridge for later authorization:
      fixed-function endpoint exit composition:
        abi_decode_sim ctx func s t /\
        run_from fuel ctx func t=Halt ss ==>
        ?fuel'. run_from fuel' ctx func s=Halt ss.
      This follows directly from abi_decode_sim_def (non-Error Halt).
      Use it with return_buffer_run, not a fictitious universal frag_exec
      conversion. If a universal fragment is still required, a new uniform
      producer must quantify over every containing fn and carry the resource
      guarantees needed there; .8 alone cannot certify that.

   6. Labels/context: abi_decode_sim needs the same ctx/func on both sides;
      no separate label-equality premise appears in its definition or in
      return_buffer_run. .8 retains allocation labels, but registered_effect
      does not promise encoder labels equality. Do not silently claim it.
      Optional unlock precedes allocation. Its source es' and updated machine
      effects require optional_unlock_frag and external_halt_success_unlock;
      the no-unlock suffix above must be proved before that wrapper.
      Package size, expression-to-ABI window production, normalization,
      run_from_gas_path and counted expression composition remain outside
      this audit. No existing theorem/definition was changed. *)
