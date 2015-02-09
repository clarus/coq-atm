(** Specifications. *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import FunctionNinjas.All.
Require Import ListString.All.
Require Import Computation.

Import ListNotations.
Local Open Scope char.

(** A run is an execution of the program with explicit answers for the
    system calls. *)
Module Run.
  (** We define a run by induction on the structure of a computation. *)
  Inductive t {A : Type} : C.t A -> Type :=
  | Ret : forall (x : A), t (C.Ret x)
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t A}, t (handler answer) ->
    t (C.Call command handler).

  (** The final result of a run. *)
  Fixpoint eval {A : Type} {x : C.t A} (run : t x) : A :=
    match run with
    | Ret x => x
    | Call _ _ _ run => eval run
    end.

  (** The trace of a run. *)
  Fixpoint trace {A : Type} {x : C.t A} (run : t x)
    : list {command : Command.t & Command.answer command} :=
    match run with
    | Ret _ => []
    | Call command answer _ run => existT _ command answer :: trace run
    end.
End Run.
