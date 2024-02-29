(* This has been checked in https://coq.vercel.app/scratchpad.html *)
  
Inductive foo : Set :=
  | fooey.

(* Note that the type on a constructor doesn't use a function type to
   represent the argument. I guess that's just derived from the signature
   of the whole datatype. *)

Inductive niche (k : nat) : Set :=
  | nicheuser : niche k.

(* Increment the index of a niche user. *)
Definition incuser {k : nat} (o : niche k) :=
match o with
  (nicheuser _) => nicheuser (S k)   (* weird syntax that error messages forced *)
end.

Check (niche 5).
Check (nicheuser 5).
Check incuser (nicheuser 5).

Definition incniche {k : nat} (n : Set) :=
  match n with
    (niche _) => niche (S k)  (* error on first "niche": "Unknown constructor: niche." *)
end.
