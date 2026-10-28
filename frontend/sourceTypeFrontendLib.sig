signature sourceTypeFrontendLib = sig
  (* Opt-in annotation gate for a stricter source frontend. The caller supplies
     original syntax and independently resolved environments, never inferred
     annotation widths as the names/constants/type_env arguments. *)
  type input =
    {type_env : Term.term,
     names : Term.term,
     constants : Term.term,
     annotation : Term.term}

  type certificate =
    {resolution : Term.term,
     equation : Thm.thm,
     well_formed : Thm.thm,
     provenance : Thm.thm,
     original_bounds : Thm.thm,
     claim : Thm.thm option}

  (* Fail on explicit source-type errors or a non-closed/noncomputable input.
     All returned facts are kernel theorems, not ML evaluations of constants. *)
  val resolve : input -> certificate
  val check_claim : input -> Term.term -> certificate
end
