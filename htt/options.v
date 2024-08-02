(* turn off the automation of Program *)
#[export] Obligation Tactic := auto.
(* turn off other Program extensions *)
#[export] Unset Program Cases. 
(* commenting this out allows a bit more convenience *)
(* when working with tuples, as one can pass a proof *)
(* of a "wrong" fact, and Program would emit obligation *)
(* that wrong fact equals the right fact. *)
(* If left uncommented, the equality will have to be *)
(* witnessed manually in the program *)
(* #[export] Unset Program Generalized Coercion. *)
#[export] Unset Program Mode.
