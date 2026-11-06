Theory dftGasInvAudit
Ancestors dftGasOracleInv

(* Fail certification if the exported result carries an untrusted oracle. *)
val _ =
  if List.exists (fn name => name <> "DISK_THM")
       (#1 (Tag.dest_tag (Thm.tag dft_ev_lowered_inv)))
  then raise Fail "dft_ev_lowered_inv has an untrusted oracle tag"
  else print "dft_ev_lowered_inv oracle audit: clean\n";
