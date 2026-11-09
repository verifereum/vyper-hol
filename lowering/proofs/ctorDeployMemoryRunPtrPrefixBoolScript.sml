(* C1.decode.boolloop CONTRACT DIAGNOSTIC ONLY -- no theorem is asserted here.
   This file records a proposed HOL statement and the outstanding proof interface.
   Review is required before introducing any proof obligation for it.

   Evidence for the specialization:
   abiEncoderScript.sml:475-518,552-588: DecDynArray below takes the loop arm;
   BoolClamp needs clamping, has no offset, and has 32-byte ABI/memory stride.
   abiEncoderScript.sml:77-81,167-172: each body reads a word, checks SHR 1 = 0
   through ISZERO/ASSERT, then MSTOREs the word. ASSERT failure is Abort, not OK
   with a halted state (venomExecSemanticsScript.sml:833-842).
   contextScript.sml:241-245: the loop allocates exactly one fresh 32-byte site.

   PROPOSED STATEMENT (all identifiers below are existing HOL constants or bound
   variables; R is a theorem-local let, NOT a new definition).

   prefix_decode_dyn_bool_ptr:
     !st st' dst src data_size max_count ctx fn PG D lo s G tn
      a d b sz.
       compile_abi_decode_to_buf (Var dst) (Var src) DLOAD (Lit 0w)
         (Lit (n2w data_size))
         (DecDynArray (DecPrimWord BoolClamp) 32 32 F max_count) st = ((),st') /\
       fn_has_code st st' fn /\ fresh_vars_wrt st s /\
       dst <> src /\ FLOOKUP G src = NONE /\
       eval_operand (Var src) s = SOME (n2w a) /\
       eval_operand (Var dst) s = SOME (n2w d) /\
       FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
       d + 32*(max_count+1) <= b+sz /\ b+sz <= s.vs_alloca_next /\
       a + 32*(max_count+1) < dimword(:256) /\
       0 < data_size /\ data_size < dimword(:256) /\
       data_size = LENGTH s.vs_data_section /\
       s.vs_alloca_next + 32 < dimword(:256) /\
       (!aid. st.cs_next_id <= aid ==> FLOOKUP s.vs_allocas aid = NONE) /\
       op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
       allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
       ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
       s.vs_inst_idx = LENGTH st.cs_current_insts
       ==>
       let count = w2n (abi_decode_load DLOAD (n2w a) s);
           cap = 32*(max_count+1);
           scratch = s.vs_alloca_next;
           R = (\(v,Gv,tv) (w,Gw,tw).
             ?bb inst z.
               lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
               get_instruction bb v.vs_inst_idx = SOME inst /\
               ~v.vs_halted /\ ~z.vs_halted /\
               (!f. step_inst f ctx inst v = OK z /\
                    ptr_safe_step D lo f ctx fn PG Gv tv inst v) /\
               (if is_terminator inst.inst_opcode then
                  w = z /\ w.vs_inst_idx = 0 /\
                  Gw = entry_prov fn w Gv /\ tw = entry_taint_vars fn w tv /\
                  (?next. lookup_block w.vs_current_bb fn.fn_blocks = SOME next /\
                    eval_phis w next.bb_instructions = OK w /\
                    phi_prefix_length next.bb_instructions = 0)
                else
                  w = (z with vs_inst_idx := SUC v.vs_inst_idx) /\
                  (!f. ghost_step f ctx PG Gv tv inst v = (Gw,tw))))
       in
         (?t Gt tt.
           RTC R (s,G,tn) (t,Gt,tt) /\ ~t.vs_halted /\
           t.vs_current_bb = st'.cs_current_bb /\
           t.vs_inst_idx = LENGTH st'.cs_current_insts /\
           count <= max_count /\ a+32*(count+1) <= data_size /\
           mload d t = n2w count /\
           (!j. j < count ==>
             w2n (abi_decode_load DLOAD (n2w (a+32+32*j)) s) < 2 /\
             mload (d+32+32*j) t =
               abi_decode_load DLOAD (n2w (a+32+32*j)) s) /\
           t.vs_data_section = s.vs_data_section /\
           t.vs_alloca_next = scratch+32 /\ allocas_from lo t /\
           FLOOKUP Gt dst = SOME (b,sz) /\ op_taint tt (Var dst) = {} /\
           (!k. k < 32*(count+1) ==> d+k NOTIN tt.t_mem) /\
           (!p k. (p+k <= d \/ d+cap <= p) /\
                  (p+k <= scratch \/ scratch+32 <= p) ==>
             mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
           ((!f. ptr_safe_run D lo f ctx fn PG Gt tt t) ==>
            !f. ptr_safe_run D lo f ctx fn PG G tn s))
         \/
         (?v Gv tv bb inst vh.
           RTC R (s,G,tn) (v,Gv,tv) /\
           lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
           get_instruction bb v.vs_inst_idx = SOME inst /\
           inst.inst_opcode = ASSERT /\
           (!f. step_inst f ctx inst v = Abort Revert_abort vh /\
                ptr_safe_step D lo f ctx fn PG Gv tv inst v) /\
           vh = revert_state (set_returndata [] v) /\
           ((inst.inst_id = st.cs_next_id+3 /\ max_count < count) \/
            (inst.inst_id = st.cs_next_id+9 /\ count <= max_count /\
             data_size < a+32*(count+1)) \/
            (inst.inst_id = st.cs_next_id+30 /\ count <= max_count /\
             a+32*(count+1) <= data_size /\
             ?j. j < count /\
               2 <= w2n (abi_decode_load DLOAD (n2w (a+32+32*j)) s) /\
               (!k. k < j ==>
                 w2n (abi_decode_load DLOAD (n2w (a+32+32*k)) s) < 2))) /\
           (!f. ptr_safe_run D lo f ctx fn PG G tn s))

   Important scope/strength notes:
   - This specializes to distinct pre-existing variable operands, not arbitrary
     operands. Registration must later establish these premises or generalize it.
   - It does NOT assume canonical source Bool words, count validity, or source-end
     validity: all three ASSERT failure classes remain in the disjunction.
   - cap is a destination capacity and an arithmetic nonwrapping bound, not an
     assertion that all capacity bytes lie in the actual data section. The latter
     may be shorter; hence the payload-end ASSERT may actually fail.
   - R supplies actual instruction execution and ghost/safety certificates in the
     CONCLUSION, not hypotheses. On branch edges it uses the incoming ghost, not
     ghost_step. No PHI transformation is duplicated at entry.
   - The continuation is all-fuel, since each traversed block consumes fuel.
     Ordinary instructions within a block do not. The existing indexed block
     chain rule applies after grouping normal instructions into concrete blocks;
     R is evidence, not a claimed existing RTC-to-ptr_safe_run theorem.

   PROPOSED INVARIANT AT HEADER (inline in the future proof).
   Let ip be the generated scratch operand (ALLOCA id st.cs_next_id+12), and
   hdr/body/exit the three fresh labels emitted by compile_abi_decode_dyn_loop.
   At header (Lit 0w) entry (v,Gv,tv), indexed by i:
     i <= count /\ count <= max_count /\ a+32*(count+1) <= data_size /\
     ~v.vs_halted /\ v.vs_current_bb=hdr /\ v.vs_inst_idx=0 /\
     v.vs_data_section=s.vs_data_section /\
     eval_operand (Var src) v=SOME(n2w a) /\
     eval_operand (Var dst) v=SOME(n2w d) /\
     eval_operand ip v=SOME(n2w scratch) /\
     op_taint tv (Var src)={} /\ op_taint tv (Var dst)={} /\
     op_taint tv ip={} /\
     op_prov Gv ip=SOME(scratch,32) /\
     FLOOKUP Gv dst=SOME(b,sz) /\ FLOOKUP Gv src=NONE /\
     mload scratch v=n2w i /\ mload d v=n2w count /\
     (!k. k<32 ==> scratch+k NOTIN tv.t_mem) /\
     (!j. j<i ==>
       w2n(abi_decode_load DLOAD (n2w(a+32+32*j)) s)<2 /\
       mload (d+32+32*j) v=abi_decode_load DLOAD (n2w(a+32+32*j)) s) /\
     (!k. k<32*(i+1) ==> d+k NOTIN tv.t_mem) /\
     v.vs_alloca_next=scratch+32 /\ allocas_from lo v.
   Also retain the two-region memory frame and all original operand evaluations.
   Generated-variable distinctness and unchanged src/dst/ip across repeated
   header/body executions are compiler-shape obligations, not a claim that
   fresh_vars_wrt st remains true after the loop has executed once.

   HEADER CERTIFICATE MATCHING:
   Choose u0=v; u1=update_var iv (n2w i) v;
   u2=update_var cv (n2w count) u1;
   u3=update_var cmp (bool_to_word(i<count)) u2;
   u4=update_var done (bool_to_word(~(i<count))) u3.
   These are exactly abi_decode_header_state's intermediate updates.
   Set g/q by the four actual ghost steps, never by whole-block simulation.
   j=0 MLOAD: scratch provenance/range and clean scratch word give access_ok and
     untainted iv. j=1 DLOAD: src evaluation, immutable data section and clean src
     give count and clean cv. j=2 LT and j=3 ISZERO: clean scalar inputs, plus
     i<=count<dimword, give semantic equations and clean cmp/done.
   JNZ uses clean done and the exact chosen target; the checked header adapter
   supplies the concrete edge and entry ghost transformation. i=count exits;
   i<count enters the body, without claiming any other ghost_block endpoint.

   BODY/BACKEDGE OBLIGATIONS:
   Body MLOAD reloads i from the same scratch. ADD/MUL address arithmetic must
   establish a+32+32*i and d+32+32*i without wrap. src is non-provenanced; dst
   retains (b,sz) through ADDs, while scalar MUL offsets have no provenance.
   The DLOAD result is untainted. SHR/ISZERO either reaches the Bool ASSERT Abort
   at id+30, or proves the word<2. Only the successful case performs MSTORE.
   That store is within the destination allocation and removes all taint in the
   next 32 bytes. Disjoint scratch/destination ranges preserve both count and
   index. ADD i 1 is nonwrapping because i<count. MSTORE ip writes a clean word,
   then JMP hdr transports incoming ghost via entry_prov/entry_taint_vars.
   The invariant is restored with SUC i and measure count-SUC i < count-i.
   A zero count still performs scratch ALLOCA/initialization, then exits through
   the first header; it must not be implemented by skipping scratch allocation.

   OUTSTANDING INTERFACES, NOT YET THEOREMS:
   1. Exact emitted compiler shape and generated names/labels, including ASSERT
      offsets +3,+9,+30 and ALLOCA +12. Offsets are counted from the definitions
      above, not yet certified by an exported code-shape theorem.
   2. Actual MLOAD safety/output taint lemma for a clean provenance-backed word;
      clean pure-op composition and pointer ADD/MUL provenance/frame lemmas.
   3. BoolClamp DLOAD/SHR/ISZERO/ASSERT/MSTORE success and Abort paired adapters.
      The existing NoClamp word adapter cannot replace BoolClamp validation.
   4. Destination/scratch clean-word framing through stores and entry ghosts;
      generated label/name freshness and alloca-id freshness from registration.
   5. Initial straight-line guards/count store/ALLOCA/index initialization paired
      adapter, preserving failures before scratch exists. ASSERT Abort needs no
      ret_taint Halt proof: ptr_safe_block stops on non-OK including Abort.
   6. Actual body/backedge certificates, finite well-founded iteration with Abort
      alternatives, and grouping its evidence into the existing block chain
      continuations. abi_decode_sim/frag_exec do not establish these witnesses.
   This diagnostic is not a proof of any of (1)-(6), nor of the proposed theorem.
*)
Theory ctorDeployMemoryRunPtrPrefixBool
Ancestors
  ctorDeployMemoryRunPtrPrefixHeader ctorDeployMemoryRunPtrPrefixWord

val _ = export_theory();
