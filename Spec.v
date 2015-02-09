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
  Inductive t : C.t -> Type :=
  | Ret : t C.Ret
  | Call : forall (command : Command.t) (answer : Command.answer command)
    {handler : Command.answer command -> C.t}, t (handler answer) ->
    t (C.Call command handler).

  (** The trace of a run. *)
  Fixpoint trace {x : C.t} (run : t x)
    : list {command : Command.t & Command.answer command} :=
    match run with
    | Ret => []
    | Call command answer _ run => existT _ command answer :: trace run
    end.
End Run.
