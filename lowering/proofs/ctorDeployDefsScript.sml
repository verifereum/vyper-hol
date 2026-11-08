(* Definitions for the deployment composition (e2e_deploy_correctness).
 * TOP-LEVEL: deploy_phases, imm_len, deploy_entry_state, deploy_source_ok, deploy_dead,
 * deploy_source_exempt, deploy_venom_result_rel.
 * Also mem_dead_bytes, imm_section_dead. Helper: deploy_venom_result_rel_terminates.
 * deploy_venom_result_rel is the Venom-level counterpart of deploy_result_rel:
 * it relates load_contract's result to a run of the deployment unit, and the
 * creation-frame piece turns it into deploy_result_rel.
 *)
Theory ctorDeployDefs
Ancestors
  e2eDeployDefs e2eProducers ptrDiscipline passSimulationDefs
  venomExecSemantics venomState e2eEntry compileVyper compileEnv valueEncoding
  immutableSectionRel vyperValue vyperContext

(* Every artifact a successful compile_vyper (K SOME) produces for the
   deployment unit, as compile_vyper_runtime_phases does for the runtime unit. *)
Definition deploy_phases_def:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) <=>
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
    dout.po_final_assembly = rpolicy.rpol_final_assembly /\
    codegen_assembly rpolicy dout.po_unit = SOME prog /\
    generate_context_plan dout.po_unit.cu_context = SOME cplan /\
    assembly_target_safe rpolicy.rpol_target prog /\
    prog = execute_plan cplan.cp_initial_fmp (context_plan_ops cplan) ++
           data_segment_asm dout.po_unit.cu_data_segment ++
           [AsmDataHeader "code_end"] /\
    deploy_bc = assemble prog
End

(* Bytes of the constructor's immutables fixed region, at memory offset 0. *)
Definition imm_len_def:
  imm_len tops =
    compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
End

(* The deployment unit's entry state: entry_venom_state with the alloca
   frontier past the immutables fixed region, which the constructor addresses
   by literal offsets rather than through an ALLOCA. *)
Definition deploy_entry_state_def:
  deploy_entry_state prog cplan tops es =
    entry_venom_state prog cplan es with vs_alloca_next := imm_len tops
End

(* The source-side hypotheses of e2e_deploy_correctness. *)
Definition deploy_source_ok_def:
  deploy_source_ok tops am tx <=>
    supported_program tops /\ constructor_call_free tops /\
    deploy_typing_ok tops am tx /\ deploy_storage_ok tops am tx
End

(* mem_dead_bytes sec off tv i: byte i of sec is dead in a value of type tv
   laid out from byte off of sec in memory layout, by the lengths sec itself
   holds (the memory twin of dead_bytes):
   - a bytestring: a data byte at or past the length, within the capacity;
   - a DynArray: every byte of an element at or past the length, and the
     dead bytes of the elements below it;
   - a struct, tuple or static array: the dead bytes of its members.
   These are the bytes immutable_value_mask leaves unused. *)
Definition mem_dead_bytes_def:
  (mem_dead_bytes (sec:word8 list) off (BaseTV (BytesT (Dynamic max))) i <=>
     off + 32 + w2n (mem_word_at off sec) <= i /\
     i < off + type_memory_size (BaseTV (BytesT (Dynamic max)))) /\
  (mem_dead_bytes sec off (BaseTV (StringT max)) i <=>
     off + 32 + w2n (mem_word_at off sec) <= i /\
     i < off + type_memory_size (BaseTV (StringT max))) /\
  (mem_dead_bytes sec off (BaseTV _) i <=> F) /\
  (mem_dead_bytes sec off (FlagTV _) i <=> F) /\
  (mem_dead_bytes sec off NoneTV i <=> F) /\
  (mem_dead_bytes sec off (TupleTV tvs) i <=>
     mem_dead_bytes_list sec off tvs i) /\
  (mem_dead_bytes sec off (ArrayTV tv (Fixed n)) i <=>
     ?k. k < n /\ mem_dead_bytes sec (off + k * type_memory_size tv) tv i) /\
  (mem_dead_bytes sec off (ArrayTV tv (Dynamic n)) i <=>
     ?k. k < n /\
         if k < w2n (mem_word_at off sec) then
           mem_dead_bytes sec (off + 32 + k * type_memory_size tv) tv i
         else
           off + 32 + k * type_memory_size tv <= i /\
           i < off + 32 + (k + 1) * type_memory_size tv) /\
  (mem_dead_bytes sec off (StructTV fields) i <=>
     mem_dead_bytes_fields sec off fields i) /\
  (mem_dead_bytes_list sec off [] i <=> F) /\
  (mem_dead_bytes_list sec off (tv::tvs) i <=>
     mem_dead_bytes sec off tv i \/
     mem_dead_bytes_list sec (off + type_memory_size tv) tvs i) /\
  (mem_dead_bytes_fields sec off [] i <=> F) /\
  (mem_dead_bytes_fields sec off ((_,tv)::fields) i <=>
     mem_dead_bytes sec off tv i \/
     mem_dead_bytes_fields sec (off + type_memory_size tv) fields i)
End

(* Byte j of an immutables section sec is dead in some immutable's value. *)
Definition imm_section_dead_def:
  imm_section_dead tops sec j <=>
    ?pre vis name ty slot post tv.
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
      evaluate_type (type_env tops) ty = SOME tv /\
      mem_dead_bytes sec
        (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre)
        tv j
End

(* The deployment's dead bytes, fixed before the run (so independent of its
   gas readings): the target's dead storage and transient storage bytes in
   the context load_contract runs the constructor in, as external_call_dead,
   and the dead bytes of the immutables section the run returns after the
   runtime code.  vs_immutables are not observed, so all of them are dead. *)
Definition deploy_dead_def:
  deploy_dead tops runtime_bc am tx =
    let cx = initial_evaluation_context ((tx.target, [(NONE, tops)]) :: am.sources)
               am.layouts tx NONE in
    <| d_stor := (\a st. if a = tx.target
                         then {(k,b) | storage_dead cx F st (w2n k) b}
                         else {});
       d_trans := (\a st. if a = tx.target
                          then {(k,b) | storage_dead cx T st (w2n k) b}
                          else {});
       d_imm := K UNIV;
       d_ret := (\r. {i | LENGTH runtime_bc <= i /\
                         imm_section_dead tops (DROP (LENGTH runtime_bc) r)
                           (i - LENGTH runtime_bc)}) |>
End

Definition deploy_source_exempt_def:
  deploy_source_exempt tops
    (src : (abstract_machine # call_request list) + exception) <=>
    case src of
      INR (Error e) => unspecified_behaviour_exempt tops e
    | _ => F
End

(* A successful constructor halts returning the runtime code followed by its
   immutables section, with the source's accounts (the target modulo code,
   its storage modulo storage_dead), transient storage (modulo storage_dead)
   and logs. Failures abort; a source Error may also halt
   only when it is exempt. *)
Definition deploy_venom_result_rel_def:
  deploy_venom_result_rel tops runtime_bc tx
    (src : (abstract_machine # call_request list) + exception) vres <=>
    case (src, vres) of
      (INL (am', rqs), Halt ss) =>
        let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
        ?section.
          ss.vs_returndata = runtime_bc ++ section /\
          immutables_section_rel tops (account_immutables am' tx.target) section /\
          (!a. a <> tx.target ==>
               lookup_account a ss.vs_accounts = lookup_account a am'.accounts) /\
          (lookup_account tx.target ss.vs_accounts) with code := [] =
          (lookup_account tx.target am'.accounts) with
            <| code := [];
               storage := (lookup_account tx.target ss.vs_accounts).storage |> /\
          storage_agree
            (storage_dead cx F (lookup_account tx.target am'.accounts).storage)
            (lookup_account tx.target am'.accounts).storage
            (lookup_account tx.target ss.vs_accounts).storage /\
          transient_agree cx am'.tStorage ss.vs_transient /\
          am'.logs = ss.vs_logs
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error e), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End

Theorem deploy_venom_result_rel_terminates:
  deploy_venom_result_rel tops runtime_bc tx src res ==> terminates res
Proof
  Cases_on `res` >> simp[terminates_def] >>
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >> simp[deploy_venom_result_rel_def])
  >> rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_venom_result_rel_def]
QED
