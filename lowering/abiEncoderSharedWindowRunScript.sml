(* The external-return caller's encoder run, derived from the shared
   encoder spine over the function's 32-byte ALLOCA sites. *)
Theory abiEncoderSharedWindowRun
Ancestors
  abiEncoderSharedRecursive abiEncoderSharedContract abiEncoderVarRestore
  abiEncoderFragmentFrame abiEncoderEntry abiEncoderExitPhi
  abiEncoderRegisteredEffect abiEncoderWindow abiEncoderAdmissible
  abiDecoderAllocation abiDecoderFootprint abiDecoderReentry abiDecoderLoop
  abiEncoderProps exprLoweringProps fragExec compileEnv
  venomState venomInst venomExecSemantics venomMemDefs venomWf
  contractABI valueEncoding words list finite_map pred_set

(* Same statement as compile_abi_encode_to_buf_window_run, proved from the
   shared encoder spine (abi_encoder_shared_admissible + abi_encoder_shared_run)
   instead of the abiEncoderWindow* family.  Intuition, not prescription:
   - sites = {inst.inst_id | MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA
     /\ inst.inst_operands = [Lit 32w]} satisfies abi_sites_cover by definition,
     and every site has alloca_size 32.
   - Run on abi_decoder_prune_vars st.cs_next_var initial (fresh_vars_wrt st'
     holds there), then restore the caller's variables with
     abi_encoder_shared_restore / abi_encoder_restored_operand, as
     abi_encoder_restored_frame does.
   - first/last = st.cs_next_id/st'.cs_next_id, b = 0,
     cap = alloca_next + 32 * CARD (missing sites); alloca_room gives the room.
   - The shared input's source footprint is zero-aware; the destination one
     is not.  When LENGTH (enc at av) = 0 the descriptor has no dynamic part
     and the fragment emits no ALLOCA, so no slot entry can sit around d;
     otherwise LENGTH (enc at av) >= 32 and the caller's zero-aware
     regions_disjoint premise gives the footprint.  Care: a site of func
     outside the fragment whose id falls in frag_ids would also be in the
     footprint.
   - The exit-block phi disjunction comes from abi_encoder_core_containing_exit_phi;
     the registered effect on frag_ids from abi_encoder_registered_effect_enlarge. *)
Theorem compile_abi_encode_to_buf_shared_window_run:
  !dst src ei st out st' ctx func initial at av sb source_cap d.
    compile_abi_encode_to_buf dst src ei st = (out,st') /\
    abi_encoder_admissible ei /\
    abi_encoder_window_input ei at av sb source_cap initial.vs_memory /\
    eval_operand src initial = SOME (n2w sb) /\
    eval_operand dst initial = SOME (n2w d) /\
    (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
    fn_has_code st st' func /\ fn_inst_ids_distinct func /\
    alloca_inv initial /\ alloca_room ctx func initial /\
    sb + source_cap <= initial.vs_alloca_next /\
    d + LENGTH (enc at av) <= initial.vs_alloca_next /\
    venomMemDefs$regions_disjoint
      (sb,source_cap) (d,LENGTH (enc at av)) /\
    (!inst b sz.
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids st st' /\
      FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = 32 /\
      venomMemDefs$regions_disjoint (sb,source_cap) (b,sz) /\
      venomMemDefs$regions_disjoint (d,LENGTH (enc at av)) (b,sz)) /\
    ~initial.vs_halted /\
    initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?actual.
      mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
      eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
      abi_encoder_registered_effect (frag_ids st st')
        [(d,LENGTH (enc at av))] initial actual /\
      alloca_inv actual /\ alloca_room ctx func actual /\
      (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
             lookup_var x actual = SOME w) /\
      ~actual.vs_halted /\
      actual.vs_current_bb = st'.cs_current_bb /\
      actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
      abi_decode_sim ctx func initial actual
Proof
  cheat
QED
