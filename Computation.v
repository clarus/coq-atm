(** The definition of computations, used to represent interactive programs. *)
Require Import Coq.NArith.NArith.
Require Import ListString.All.

Local Open Scope type.

(** System calls. *)
Module Command.
  Inductive t :=
  | AskCard
  | AskPIN
  | CheckPIN (pin : N)
  | AskAmount
  | CheckAmount (amount : N)
  | GiveAmount (amount : N)
  | GiveCard
  | ShowError (message : LString.t).

  (** The type of an answer for a command depends on the value of the command. *)
  Definition answer (command : t) : Type :=
    match command with
    | AskCard => bool (* If the given card seems valid. *)
    | AskPIN => option N (* A number or cancellation. *)
    | CheckPIN _ => bool (* If the PIN number is valid. *)
    | AskAmount => option N (* A number or cancellation. *)
    | CheckAmount _ => bool (* If the amount can be withdrawn. *)
    | GiveAmount _ => bool (* If the money was given. *)
    | GiveCard => bool (* If the card was given. *)
    | ShowError _ => unit (* Show an error message. *)
    end.
End Command.

(** Computations with I/Os. *)
Module C.
  (** A computation can either return a pure value, or do a system call and wait
      for the answer to run another computation. *)
  Inductive t (A : Type) : Type :=
  | Ret : forall (x : A), t A
  | Call : forall (command : Command.t), (Command.answer command -> t A) -> t A.
  Arguments Ret {A} _.
  Arguments Call {A} _ _.

  (** Some optional notations. *)
  Module Notations.
    (** A nicer notation for `Ret`. *)
    Definition ret {A : Type} (x : A) : t A :=
      Ret x.

    (** We define an explicit apply function so that Coq does not try to expand
        the notations everywhere. *)
    Definition apply {A B} (f : A -> B) (x : A) := f x.

    (** System call. *)
    Notation "'call!' answer ':=' command 'in' X" :=
      (Call command (fun answer => X))
      (at level 200, answer ident, command at level 100, X at level 200).

    (** System call with typed answer. *)
    Notation "'call!' answer : A ':=' command 'in' X" :=
      (Call command (fun (answer : A) => X))
      (at level 200, answer ident, command at level 100, A at level 200, X at level 200).

    (** System call ignoring the answer. *)
    Notation "'do_call!' command 'in' X" :=
      (Call command (fun _ => X))
      (at level 200, command at level 100, X at level 200).

    (** This notation is useful to compose computations which wait for a
        continuation. We do not have an explicit bind operator to simplify the
        language and the proofs. *)
    Notation "'let!' x ':=' X 'in' Y" :=
      (apply X (fun x => Y))
      (at level 200, x ident, X at level 100, Y at level 200).

    (** Let with a typed answer. *)
    Notation "'let!' x : A ':=' X 'in' Y" :=
      (apply X (fun (x : A) => Y))
      (at level 200, x ident, X at level 100, A at level 200, Y at level 200).

    (** Let ignoring the answer. *)
    Notation "'do_let!' X 'in' Y" :=
      (apply X (fun _ => Y))
      (at level 200, X at level 100, Y at level 200).
  End Notations.
End C.
